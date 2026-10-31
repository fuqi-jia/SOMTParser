/* -*- Source -*-
 * translate(): frontend -> HIR -> passes -> Parser -> dialect emission.
 * Do not include <cassert> (see hir_to_parser.cpp).
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/translate.h"
#include "somtparser/lowering/z3_finite_set_lowering.h"
#include "somtparser/lowering/optimathsat_array_lowering.h"

#include "somtparser/lowering/bound_ints_pass.h"
#include "somtparser/lowering/positive_exists.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/hir/soft_objectives.h"
#include "somtparser/hir/packed_clause_io.h"
#include "somtparser/hir/packed_linear_io.h"
#include "somtparser/hir/packed_scalar_io.h"

#include <chrono>
#include <exception>
#include <fstream>
#include <new>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>

namespace SOMTParser {

using Uir::ErrorCode;

namespace {

void applyEmittedNames(Uir::Sem::TranslationContract& contract,
                      const Lower::HirToParser& lowerer) {
    namespace H = Uir::Hir;
    const auto& emitted = lowerer.emittedNames();
    // The usual large-model path retains its shared signature and axioms.
    if (emitted.empty()) { return; }
    std::unordered_map<std::string, std::string> globals;
    for (const auto& symbol : contract.target_signature.symbols) {
        // Sorts occupy a separate namespace and are not renamed by emitName.
        if (symbol.kind == Uir::Sem::SymbolKind::SORT) { continue; }
        const auto found = emitted.find(symbol.name);
        if (found != emitted.end()) { globals.emplace(*found); }
    }
    if (globals.empty()) { return; } // bound-variable-only alpha-renaming
    const auto rename = [&](std::string& name) {
        const auto found = globals.find(name);
        if (found != globals.end()) { name = found->second; }
    };
    auto signature = contract.target_signature.materialize();
    for (auto& symbol : signature.symbols) {
        if (symbol.kind != Uir::Sem::SymbolKind::SORT) { rename(symbol.name); }
    }
    contract.target_signature = Uir::Sem::SignatureSnapshot(std::move(signature));
    // Valid scalar ranges end in "[N]"; packed Boolean ranges are accepted
    // only without ordinary symbols. Neither can contain a generated name!N
    // from this lowerer, so their compact names and bounds stay unchanged.
    for (auto& mapping : contract.symbol_map) { rename(mapping.target); }
    for (auto& bounds : contract.target_declaration_bounds) { rename(bounds.target_name); }
    for (auto& observable : contract.projection.observables) {
        if (observable.projection != Uir::Sem::ProjectionKind::CONSTANT) {
            rename(observable.target_name);
        }
    }
    for (auto& observable : contract.projection.optional_observables) {
        rename(observable.target_name);
    }
    for (auto& choice : contract.projection.choices) {
        for (auto& alternative : choice.alternatives) {
            rename(alternative.target_name);
            for (auto& binding : alternative.bindings) { rename(binding.target_name); }
        }
    }
    for (auto& grammar : contract.projection.grammar_choices) {
        for (auto& node : grammar.nodes) {
            rename(node.selector_target);
            for (auto& alternative : node.alternatives) {
                for (auto& binding : alternative.bindings) { rename(binding.target_name); }
            }
        }
    }
    // Rewrite free symbol occurrences only. A BOUND_VAR and its binder keep
    // their scoped identity, even if their spelling equals a renamed global;
    // literal text and datatype constructors inhabit different roles too.
    // Iterative postorder retains DAG sharing and handles deep target axioms.
    std::unordered_map<const H::Expr*, H::ExprPtr> memo;
    for (auto& axiom : contract.target_axioms) {
        if (!axiom) { continue; }
        std::vector<std::pair<H::ExprPtr, bool>> pending{{axiom, false}};
        while (!pending.empty()) {
            auto item = std::move(pending.back());
            pending.pop_back();
            const auto& expression = item.first;
            if (memo.count(expression.get())) { continue; }
            if (!item.second) {
                pending.emplace_back(expression, true);
                for (const auto& child : expression->args) {
                    if (child && !memo.count(child.get())) { pending.emplace_back(child, false); }
                }
                continue;
            }
            std::string name = expression->name;
            if (expression->kind == H::ExprKind::IDENT || expression->kind == H::ExprKind::APPLY) {
                rename(name);
            }
            bool changed = name != expression->name;
            for (const auto& child : expression->args) {
                changed = changed || (child && memo.at(child.get()) != child);
            }
            H::ExprPtr result = expression;
            if (changed) {
                auto replacement = std::make_shared<H::Expr>(*expression);
                replacement->name = std::move(name);
                for (auto& child : replacement->args) {
                    if (child) { child = memo.at(child.get()); }
                }
                result = std::move(replacement);
            }
            memo.emplace(expression.get(), std::move(result));
        }
        axiom = memo.at(axiom.get());
    }
}

void recordSemanticStage(Uir::TranslationReport& report,
                         const Uir::Sem::TranslationContract& contract) {
    Uir::EncodingChoice choice;
    if (report.detailsEnabled()) {
        choice.site = contract.id;
        choice.unified_op = "semantic-translation-stage";
        choice.strategy = contract.source.id + "->" + contract.target.id
            + (contract.decision.polarity == Uir::Sem::VerdictPolarity::PRESERVE
                   ? ";verdict-preserving"
                   : ";verdict-inverting");
    }
    choice.fidelity = contract.claimed_fidelity;
    if (report.detailsEnabled()) {
        choice.rationale =
            "validated Phi/A/beta/objective/decision metadata and recorded local proof "
            "obligations. Target SAT: " + contract.decision.target_sat_meaning
            + "; target UNSAT: " + contract.decision.target_unsat_meaning;
    }
    if (contract.claimed_fidelity.count_status == Uir::CountStatus::PRESERVED) {
        for (const Uir::Sem::ProofObligation& obligation : contract.obligations) {
            if (obligation.kind == Uir::Sem::ProofObligationKind::MODEL_COUNT
                && obligation.evidence != Uir::EvidenceKind::PENDING
                && !obligation.rationale.empty()
                && !obligation.evidence_refs.empty()) {
                choice.count_evidence = Uir::CountEvidence{
                    obligation.evidence, obligation.rationale, obligation.evidence_refs};
                break;
            }
        }
        if (!choice.count_evidence) {
            // Keep an invalid contract from briefly appearing as a positive
            // report claim before TranslationContract::validate rejects it.
            choice.fidelity.count_status = Uir::CountStatus::UNASSESSED;
        }
    }
    report.addChoice(std::move(choice));
}

} // namespace

std::string Translation::toSmt2() const {
    return toSmt2(dialect_);
}

std::string Translation::toSmt2(Lower::OmtDialect dialect) const {
    std::ostringstream out;
    writeSmt2(out, dialect);
    return out.str();
}

std::string Translation::toParserSmt2() const {
    requireDetails("native export");
    if (module_mode_) { return module_smt2_; }
    if (packed_smt_) {
        throw std::runtime_error("packed translation has no materialized Parser AST; use writeSmt2() or toSmt2()");
    }
    std::ostringstream out;
    std::vector<std::string> names;
    std::string preamble;
    const auto omt = objectiveCommands(Lower::OmtDialect::Z3, &names, &preamble);
    writeSmt2Body(out, omt, Lower::OmtDialect::Z3, names, preamble);
    return out.str();
}

void Translation::writeSmt2(std::ostream& out, Lower::OmtDialect dialect) const {
    if (!details_ || module_mode_) {
        if (dialect != dialect_) { throw std::logic_error("another dialect is unavailable for this Translation; translate again with details=True and module=False"); }
        if (!details_ && (!captured_output_ || exit_code_ != 0)) {
            throw std::logic_error("SMT output was not retained with details=False; use the supplied output stream or translate again with details=True");
        }
        out << (module_mode_ && details_ ? module_smt2_ : completed_smt2_);
        if (!out) { throw std::runtime_error("writeSmt2: failed while writing SMT-LIB output"); }
        return;
    }
    std::vector<std::string> objective_names;
    std::string preamble;
    const std::string omt = objectiveCommands(dialect, &objective_names, &preamble);
    const auto& materialized = packed_smt_ ? packed_base_parser_ : parser_;
    if (dialect == Lower::OmtDialect::OptiMathSAT
        && (set_solver_requirements_.has_sets || (materialized
            && (Lower::needsOptiMathSatArrayLowering(*materialized) || Lower::needsOptiMathSatDefinitionLowering(*materialized))))) {
        std::ostringstream raw;
        writeSmt2Body(raw, omt, dialect, objective_names, preamble);
        out << Lower::lowerBooleanArraysForOptiMathSat(set_solver_requirements_.has_sets
            ? Lower::lowerFiniteSetsForOptiMathSat(raw.str()) : raw.str());
        if (!out) throw std::runtime_error("writeSmt2: failed while writing OptiMathSAT array output");
        return;
    }
    // The parser body can be very large. Only buffer it when the translated
    // HIR actually contains sets that need Z3's representation rewrite.
    // set_solver_requirements_ was computed from typed HIR before lowering,
    // including declarations, function bodies and datatype fields.
    if (dialect != Lower::OmtDialect::Z3 || !set_solver_requirements_.has_sets) {
        writeSmt2Body(out, omt, dialect, objective_names, preamble);
        return;
    }
    if (set_solver_requirements_.non_integer_carrier) {
        throw std::runtime_error("Z3 finite-set export currently requires Set Int; use the native Set dialect for other element sorts");
    }
    std::ostringstream raw;
    writeSmt2Body(raw, omt, dialect, objective_names, preamble);
    out << Lower::lowerFiniteSetsForZ3(raw.str());
    if (!out) throw std::runtime_error("writeSmt2: failed while writing Z3 finite-set output");
}

void Translation::validateForSmt2() const {
    condAssert(ok_, "writeSmt2 called on a failed Translation");
    if (packed_smt_) {
        condAssert(model_ && (model_->packed_linear_rows || !model_->packed_bool_clauses.empty()
                            || !model_->scalar_var_ranges.empty() || model_->packed_function_calls),
                   "writeSmt2: packed translation lost its storage");
        if (model_->packed_linear_rows || !model_->scalar_var_ranges.empty() || model_->packed_function_calls) {
            condAssert(packed_base_parser_ && lowered_,
                       "writeSmt2: packed numeric translation lost its ordinary declarations");
        }
        return;
    }
    condAssert(parser_ && model_ && lowered_, "writeSmt2: Translation is incomplete");
}

std::size_t Translation::objectiveCount() const noexcept {
    return objective_count_;
}

std::string Translation::objectiveCommands(Lower::OmtDialect dialect,
                                            std::vector<std::string>* objective_names,
                                            std::string* preamble) const {
    if (preamble) preamble->clear();
    validateForSmt2();
    // translate() already proved emission succeeds for this model (see step 7
    // there), so a failure here is an internal inconsistency. Never discard
    // these diagnostics into a local nobody reads.
    if (packed_smt_ && !model_->packed_linear_rows
        && model_->scalar_var_ranges.empty() && !model_->packed_function_calls) {
        (void)Lower::omtDialectName(dialect);
        if (objective_names) objective_names->clear();
        if (soft_objective_count_ == 0) return {};
        if (dialect == Lower::OmtDialect::OptiMathSAT) return "(minimize I)\n";
        if (dialect == Lower::OmtDialect::Gomt) {
            std::string name = "__somt_packed_soft";
            for (const auto& range : model_->bool_var_ranges) {
                while (range.contains(name)) name += '_';
            }
            if (objective_names) objective_names->push_back(name);
            return "(optimize-sat " + name + ")\n";
        }
        return {};
    }
    Uir::Diagnostics emit_diags;
    const std::string omt =
        Lower::emitObjectives(*model_, dialect, *lowered_, emit_diags, soft_objective_count_, objective_names, preamble);
    condAssert(!emit_diags.hasErrors(),
               std::string("writeSmt2: objective emission failed after translate() "
                           "validated it: ")
                   + (emit_diags.all().empty() ? "" : emit_diags.all().front().message));
    return omt;
}

void Translation::writeSmt2Body(std::ostream& out, const std::string& omt,
                               Lower::OmtDialect dialect,
                               const std::vector<std::string>& objective_names,
                               const std::string& preamble) const {
    // Solver options such as produce-models must precede all declarations.
    out << preamble;
    const auto write_query_tail = [&]() {
        // The GOMT emitter already selects the objective with optimize-sat.
        // A subsequent check-sat is a second, feasibility-only query.
        if (dialect != Lower::OmtDialect::SmtLib2025 || objective_count_ == 0) {
            out << "(check-sat)\n";
        }
        for (const auto& response : terminal_responses_) {
            if (dialect == Lower::OmtDialect::SmtLib2025
                && response.find("(get-objectives") == 0) {
                if (!objective_names.empty()) {
                    out << "(get-value (";
                    for (size_t i = 0; i < objective_names.size(); ++i) {
                        if (i) out << ' ';
                        out << objective_names[i];
                    }
                    out << "))\n";
                }
            } else out << response << '\n';
        }
        out << "(exit)\n";
    };
    if (packed_smt_) {
        Uir::Diagnostics diagnostics;
        if (!model_->scalar_var_ranges.empty() || model_->packed_function_calls) {
            // The ordinary module emits set-logic first and declares every
            // compact coordinate referenced by its formulas. Remaining scalar
            // declarations precede their first use in the packed suffix.
            if ((dialect == Lower::OmtDialect::Gomt || dialect == Lower::OmtDialect::OptiMathSAT)
                && soft_objective_count_ != 0)
                packed_base_parser_->writeSMT2HardModule(out);
            else packed_base_parser_->writeSMT2Module(out);
            condAssert(Uir::Hir::writePackedScalarDeclarationsSmt2(*model_, *lowered_, out, diagnostics),
                       diagnostics.all().empty() ? "packed scalar declaration emission failed"
                                                : diagnostics.all().front().message);
            condAssert(Uir::Hir::writePackedScalarsSmt2(*model_, *lowered_, out, diagnostics),
                       diagnostics.all().empty() ? "packed scalar SMT-LIB emission failed"
                                                : diagnostics.all().front().message);
            out << omt;
        } else if (model_->packed_linear_rows) {
            if ((dialect == Lower::OmtDialect::Gomt || dialect == Lower::OmtDialect::OptiMathSAT)
                && soft_objective_count_ != 0)
                packed_base_parser_->writeSMT2HardModule(out);
            else packed_base_parser_->writeSMT2Module(out);
            condAssert(Uir::Hir::writePackedLinearDeclarationsSmt2(
                           *model_, packed_linear_symbols_, *lowered_, out, diagnostics),
                       diagnostics.all().empty() ? "packed linear declaration emission failed"
                                                : diagnostics.all().front().message);
            condAssert(Uir::Hir::writePackedLinearBoundsSmt2(
                           *model_, packed_linear_symbols_, out, diagnostics),
                       diagnostics.all().empty() ? "packed linear bound emission failed"
                                                : diagnostics.all().front().message);
            condAssert(Uir::Hir::writePackedLinearRowsSmt2(
                           *model_, packed_linear_symbols_, out, diagnostics),
                       diagnostics.all().empty() ? "packed linear SMT-LIB emission failed"
                                                : diagnostics.all().front().message);
            out << omt;
        } else {
            const std::string soft_name = dialect == Lower::OmtDialect::Gomt
                && !objective_names.empty() ? objective_names.front() : "";
            if (!soft_name.empty()) {
                out << "(set-option :enable-omt true)\n"
                    << "(define-maxsmt-objective " << soft_name << ")\n";
            } else if (dialect == Lower::OmtDialect::OptiMathSAT && soft_objective_count_ != 0) {
                out << "(set-option :produce-models true)\n";
            }
            condAssert(Uir::Hir::writePackedBoolClausesSmt2(*model_, out, diagnostics, soft_name),
                       diagnostics.all().empty() ? "packed SMT-LIB emission failed"
                                                : diagnostics.all().front().message);
            out << omt;
        }
        write_query_tail();
        condAssert(static_cast<bool>(out), "writeSmt2: failed while writing packed SMT-LIB output");
        return;
    }
    // Module emission preserves the parser's declaration/function/datatype
    // ordering and includes named and soft assertions. Objectives belong after
    // the module and before the query tail, exactly where the former string
    // splice inserted them, without materializing the complete script.
    if ((dialect == Lower::OmtDialect::Gomt || dialect == Lower::OmtDialect::OptiMathSAT)
                && soft_objective_count_ != 0)
        parser_->writeSMT2HardModule(out);
    else parser_->writeSMT2Module(out);
    out << omt;
    write_query_tail();
    if (!out) {
        throw std::runtime_error("writeSmt2: failed while writing SMT-LIB output");
    }
}

void Translation::writeSmt2(const std::string& path,
                            Lower::OmtDialect dialect) const {
    if (!details_ || module_mode_) {
        const auto script = toSmt2(dialect);
        std::ofstream out(path, std::ios::binary | std::ios::out | std::ios::trunc);
        if (!out) { throw std::runtime_error("writeSmt2: could not open destination: " + path); }
        out << script;
        out.flush();
        if (!out) { throw std::runtime_error("writeSmt2: failed while writing destination: " + path); }
        return;
    }
    // Refuse failed translations before opening with truncation, so a rejected
    // Translation or an unsupported objective dialect cannot destroy a
    // pre-existing destination. Objective validation happens once, before open.
    std::vector<std::string> objective_names;
    std::string preamble;
    const std::string omt = objectiveCommands(dialect, &objective_names, &preamble);
    std::string rendered;
    const auto& materialized = packed_smt_ ? packed_base_parser_ : parser_;
    const bool oms_arrays = dialect == Lower::OmtDialect::OptiMathSAT
        && (set_solver_requirements_.has_sets || (materialized
            && (Lower::needsOptiMathSatArrayLowering(*materialized) || Lower::needsOptiMathSatDefinitionLowering(*materialized))));
    if (oms_arrays) {
        std::ostringstream raw;
        writeSmt2Body(raw, omt, dialect, objective_names, preamble);
        rendered = Lower::lowerBooleanArraysForOptiMathSat(set_solver_requirements_.has_sets
            ? Lower::lowerFiniteSetsForOptiMathSat(raw.str()) : raw.str());
    } else if (dialect == Lower::OmtDialect::Z3 && set_solver_requirements_.has_sets) {
        if (set_solver_requirements_.non_integer_carrier) {
            throw std::runtime_error("Z3 finite-set export currently requires Set Int; use the native Set dialect for other element sorts");
        }
        std::ostringstream raw;
        writeSmt2Body(raw, omt, dialect, objective_names, preamble);
        rendered = Lower::lowerFiniteSetsForZ3(raw.str());
    }
    std::ofstream out(path, std::ios::binary | std::ios::out | std::ios::trunc);
    if (!out) {
        throw std::runtime_error("writeSmt2: could not open destination: " + path);
    }
    if (oms_arrays || (dialect == Lower::OmtDialect::Z3 && set_solver_requirements_.has_sets)) out << rendered;
    else writeSmt2Body(out, omt, dialect, objective_names, preamble);
    out.flush();
    if (!out) {
        throw std::runtime_error("writeSmt2: failed while writing destination: " + path);
    }
}

Translation translateImpl(const Lang::SourceUnit& unit, const TranslateOptions& opts,
                          Uir::Hir::ConstraintModelPtr input_model,
                          const std::vector<Uir::Hir::LocatedExpr>& source_terms) {
    using clock = std::chrono::steady_clock;
    const auto started = clock::now();

    Translation t;
    t.dialect_ = opts.omt_dialect;
    t.report_.setDetailsEnabled(opts.details || !opts.report_path.empty());
    const char* stage = "setup";

    // Per-stage timing, recorded because a total cannot be optimised against.
    // Each stage writes its own field as it completes, so a translation that
    // fails part way still reports the cost of the stages that ran -- which is
    // exactly when the number is most wanted.
    const auto ms_since = [](clock::time_point from) {
        return std::chrono::duration<double, std::milli>(clock::now() - from)
            .count();
    };

    // Everything below runs inside this lambda so that the catch at the bottom
    // covers all of it. Step 3 already had its own try/catch around the
    // frontend call, but steps 5-8 did not, and Parser's builders throw
    // ParseErrorException on an ill-formed term -- so a single bad benchmark
    // escaped translate() and ended the batch run. diagnostic.h states the
    // contract this restores: "one malformed input must degrade to a recorded
    // failure, never an escaped exception that ends the run."
    //
    // This is a boundary, not a way to carry on regardless: every catch below
    // leaves ok_ false. Allocation exhaustion has its own resource diagnostic;
    // other unexpected exceptions remain internal errors.
    const auto body = [&]() {
    // 0. Register the passes built into this library. Idempotent, and must
    //    happen before anything below queries PassRegistry::instance() (step
    //    5), or a profile naming one of them would reject with E_PASS_PIPELINE
    //    as if it were never registered at all.
    Lower::registerBuiltinPasses(Uir::PassRegistry::instance());

    // 1. Resolve the language.
    auto& registry = Lang::LanguageRegistry::instance();
    Lang::Language* lang = nullptr;
    if (input_model) {
        // Direct HIR input does not invoke a textual frontend.
    } else if (!opts.language_id.empty()) {
        lang = registry.byId(opts.language_id);
        if (lang == nullptr) {
            t.diagnostics_.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                 "no language registered under id '" + opts.language_id + "'");
            return;
        }
    } else {
        lang = registry.detect(unit);
        if (lang == nullptr) {
            t.diagnostics_.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                 "could not determine the input language of '"
                                     + unit.main_path + "'");
            return;
        }
    }

    // 1b. Data files only reach a frontend that claims them. Anything else
    //     would parse the model alone and report success for a problem whose
    //     data half was silently dropped -- a wrong answer, not a degraded one.
    const std::string source_id = input_model ? "hir" : lang->id();
    if (!unit.data_paths.empty() && (!lang || !lang->acceptsDataFiles())) {
        std::string dropped;
        for (const auto& p : unit.data_paths) {
            if (!dropped.empty()) { dropped += ", "; }
            dropped += '\'' + p + '\'';
        }
        t.diagnostics_.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                             "language '" + source_id
                                 + "' does not read data files, but "
                                 + std::to_string(unit.data_paths.size())
                                 + " data file(s) were given and would be dropped: "
                                 + dropped);
        return;
    }

    // 2. Resolve the profile. An unknown id is an error, never a fallback:
    //    a silent fallback would let a result row misreport its configuration.
    const auto profile = Uir::EncodingProfile::builtin(opts.profile_id);
    if (!profile) {
        t.diagnostics_.error(ErrorCode::E_PASS_PIPELINE,
                             "unknown profile '" + opts.profile_id + "'");
        return;
    }

    // 2b. A profile may declare an encoding style (ground / quantified). That
    //     is a claim about how constructs with a finite index set are encoded,
    //     and it is worth nothing unless some pass in the pipeline acts on it.
    //     Say so rather than let two profiles be silently identical: a user who
    //     asked for `quantified` and received `ground` byte-for-byte has no
    //     other way to find out. This warning retires itself -- it stops firing
    //     as soon as a pass sets PassTraits::reads_encoding_style.
    if (!Uir::encodingStyleIsConsumed(*profile, Uir::PassRegistry::instance())) {
        t.diagnostics_.warn(
            ErrorCode::E_PASS_PIPELINE,
            std::string("profile '") + profile->id() + "' selects the '"
                + Uir::encodingStyleName(profile->style())
                + "' encoding style, but no pass in its pipeline reads it, so"
                  " the selection has no effect in this build");
    }

    // 3. Parse. The frontend contract forbids exceptions, but a defect there
    //    must still not take down a batch run.
    Lang::ParseOutcome outcome;
    stage = "frontend parsing";
    try {
        if (input_model) {
            outcome.model = input_model;
        } else {
            const auto parse_started = clock::now();
            outcome = lang->parse(unit, opts.parse);
            t.report_.mutableStats().parse_ms = ms_since(parse_started);
        }
    } catch (const std::bad_alloc&) {
        t.diagnostics_.error(ErrorCode::E_RESOURCE,
                             "memory allocation failed during frontend parsing");
        return;
    } catch (const std::exception& e) {
        t.diagnostics_.error(ErrorCode::E_INTERNAL,
                             std::string("frontend '") + source_id
                                 + "' threw: " + e.what());
        return;
    } catch (...) {
        t.diagnostics_.error(ErrorCode::E_INTERNAL,
                             "frontend '" + source_id + "' threw an unknown exception");
        return;
    }
    t.diagnostics_.merge(outcome.diagnostics);
    if (!outcome.ok()) {
        if (!t.diagnostics_.hasErrors()) {
            t.diagnostics_.error(ErrorCode::E_PARSE,
                                 "frontend '" + source_id + "' produced no model");
        }
        return;
    }
    t.model_ = std::move(outcome.model);
    t.terminal_responses_ = std::move(outcome.terminal_responses);
    t.semantics_ = std::move(outcome.semantics);
    stage = "source semantic validation";

    // A semantic contract is executable metadata, not documentation. Refuse a
    // frontend that claims exactness without the corresponding local proof
    // obligations, or whose stages cannot be composed.
    if (!t.semantics_.validate(t.diagnostics_)) {
        return;
    }
    const Uir::Sem::SourceSemanticSpec source_spec =
        Uir::Sem::sourceSemanticSpec(source_id);
    // Built-in languages have registered source specifications and are held to
    // them. External Language implementations remain source-compatible: they
    // may opt into the semantic API by attaching contracts, but are not
    // mistaken for one of the repository's audited adapters.
    if (source_spec.valid()) {
        if (t.semantics_.stages().empty()) {
            t.diagnostics_.error(
                ErrorCode::E_INTERNAL,
                "frontend '" + source_id
                    + "' produced a model without a source semantic translation contract");
            return;
        }
        if (!Uir::Sem::validateSourceContract(
                source_spec, t.semantics_.stages().front(), t.diagnostics_)) {
            return;
        }
    }

    // 3a. Take over the frontend's encoding choices, now that there is a model
    //     they describe. Deliberately *after* the ok() check: choices from a
    //     parse that produced nothing describe a translation that does not
    //     exist, and an experiment row carrying them could not be reproduced.
    //     The diagnostics already carry why the parse failed.
    t.report_.mergeFrontend(outcome.report);
    for (const Uir::Sem::TranslationContract& contract : t.semantics_.stages()) {
        recordSemanticStage(t.report_, contract);
    }
    t.report_.beginPhase();

    // 3b. Type-check the model the frontend handed over, before anything reads
    //     it. A frontend is not required to type-check -- most of these
    //     languages have their own type systems that do not map onto this one --
    //     so an ill-sorted model is an ordinary outcome of parsing, not a
    //     frontend defect, and it is reported against the input as E_TYPE.
    //     Without this, `constraint x` on an Int x translated cleanly to
    //     `(assert x)` and was reported as an exact-fidelity success.
    const auto typecheck_started = clock::now();
    stage = "HIR type checking";
    // Reuse this one model check: validation-only roots are not a second
    // preflight traversal, and the usual empty-batch path is unchanged.
    const bool typechecked = source_terms.empty()
        ? Uir::Hir::typeCheck(*t.model_, t.diagnostics_)
        : Uir::Hir::typeCheckTerms(*t.model_, source_terms, t.diagnostics_);
    t.report_.mutableStats().typecheck_ms = ms_since(typecheck_started);
    if (!typechecked) {
        return;
    }
    // `none` is a deliberate feasibility-only projection of an optimization
    // problem. It preserves SAT/UNSAT but not the optimum, so it must enter the
    // same fidelity channel as every other approximation. The `feasibility`
    // profile accepts this explicitly; exact profiles reject it below.
    if (!t.model_->objectives.empty()
        && opts.omt_dialect == Lower::OmtDialect::None) {
        Uir::Fidelity feasibility = Uir::Fidelity::exact();
        feasibility.preserves_optimum = false;
        t.report_.addChoice({"objective-emission", "optimization-objective",
                             "drop-for-smt-feasibility", feasibility,
                             "the plain-SMT dialect preserves the feasible set but emits no "
                             "objective order"});
    }

    // 4. Domain fingerprint, recorded before any pass rewrites the model.
    stage = "HIR feature analysis";
    if (t.report_.detailsEnabled()) {
        for (const auto& f : t.model_->features()) {
            t.report_.mutableFeatureCounts()[std::string(f.name())] += 1;
        }
    }

    // 5. Passes, with the pre-flight check inside.
    const auto passes_started = clock::now();
    stage = "HIR passes";
    const bool passed = Uir::PassManager::run(*t.model_, *profile,
                                              Uir::PassRegistry::instance(),
                                              t.report_, t.diagnostics_);
    t.report_.mutableStats().passes_ms = ms_since(passes_started);
    if (!passed) {
        return;
    }
    const auto stages_before_pass_extension = t.semantics_.stages().size();
    stage = "post-pass semantic validation";
    std::string pass_pipeline;
    for (const auto& pass : profile->pipeline()) {
        if (!pass_pipeline.empty()) { pass_pipeline += ","; }
        pass_pipeline += pass.pass_id;
    }
    if (!Uir::Sem::extendRelationalWithDefinedHelpers(
            *t.model_, pass_pipeline, t.semantics_, t.diagnostics_)) {
        return;
    }
    for (std::size_t i = stages_before_pass_extension; i < t.semantics_.stages().size(); ++i) {
        recordSemanticStage(t.report_, t.semantics_.stages()[i]);
    }
    // Cache the actual output shape after passes and before consuming lowering
    // releases constraint records. Source objective metadata remains in the
    // earlier semantic stage; a pass may replace soft groups by explicit costs.
    t.soft_objective_count_ = Uir::Hir::softObjectiveGroups(*t.model_).size();
    t.objective_count_ = t.soft_objective_count_ + t.model_->objectives.size();
    // Analyze the post-pass HIR: a lowering pass may introduce quantifiers.
    // Keep solver-only requirements out of pass features because Sets lower
    // natively and are not a pass obligation.
    t.set_solver_requirements_ = t.model_->setSolverRequirements();

    // Build the target contract while the post-pass HIR is still intact but
    // before lowering allocates the parser DAG. The contract owns the target
    // signature, identity maps, and bound axioms needed for later validation.
    // This lets the translation-specific consuming lowerer release the large
    // private HIR declaration/constraint containers as soon as each section
    // has been lowered, instead of retaining them through contract creation.
    const bool has_target_semantics =
        input_model || !t.semantics_.stages().empty();
    Uir::Sem::TranslationContract target_contract;
    double target_contract_build_ms = 0.0;
    bool optimization_target = false;
    if (has_target_semantics) {
        stage = "target semantic construction";
        const auto contract_started = clock::now();
        optimization_target = Uir::Sem::hasOptimization(*t.model_)
            && (opts.omt_dialect != Lower::OmtDialect::None
                || t.model_->objectives.empty());
        target_contract = input_model
            ? Uir::Sem::relationalToSmtContract(*t.model_, optimization_target)
            : Uir::Sem::relationalToSmtContract(
                *t.model_, optimization_target,
                t.semantics_.stages().back().projection,
                t.semantics_.stages().back().target_axioms,
                &t.semantics_.stages().back().target_signature);
        target_contract_build_ms = ms_since(contract_started);
        t.report_.mutableStats().semantics_ms = target_contract_build_ms;
    }

    // Export-level existential witnesses are target-private constants. Build
    // their extension from the original contract, so none can accidentally
    // become a source observable or a source-signature obligation.
    stage = "positive existential witness lowering";
    const auto existential_witnesses = Lower::liftPositiveExists(*t.model_);
    if (!existential_witnesses.empty()) {
        // Validate the actual final formulas and symbol scopes sent to Parser,
        // including untouched negative/reified/universal quantifier contexts.
        if (!Uir::Hir::typeCheck(*t.model_, t.diagnostics_)) { return; }
        Uir::Fidelity witness_fidelity = Uir::Fidelity::exact();
        witness_fidelity.count_status = Uir::CountStatus::NO_GUARANTEE;
        for (const auto& witness : existential_witnesses) {
            t.report_.addChoice({
                "constraint[" + std::to_string(witness.constraint_index) + "]",
                "positive-exists", "fresh-private-constant", witness_fidelity,
                "quantifier " + std::to_string(witness.quantifier_index)
                    + ": bound '" + witness.bound_name + "' -> auxiliary '"
                    + witness.symbol_name
                    + "'; original-symbol projection and ordered objectives preserved; "
                      "witness multiplicity is not counted"});
        }
        if (!t.report_.fidelity().meets(profile->minFidelity())) {
            t.diagnostics_.error(ErrorCode::E_FIDELITY_REJECTED,
                "fresh existential witnesses do not meet the fidelity floor of profile '"
                    + profile->id() + "'");
            return;
        }
        if (has_target_semantics) {
            target_contract.target_signature = Uir::Sem::SignatureSnapshot(
                Uir::Sem::signatureOf(*t.model_));
            target_contract.sentence_translation_id += ":positive-exists-witnesses-v1";
            target_contract.claimed_fidelity = Uir::Fidelity::meet(
                target_contract.claimed_fidelity, witness_fidelity);
            for (auto kind : {Uir::Sem::ProofObligationKind::SOUNDNESS,
                              Uir::Sem::ProofObligationKind::COMPLETENESS,
                              Uir::Sem::ProofObligationKind::OBSERVABLES}) {
                target_contract.obligations.push_back({kind,
                    Uir::EvidenceKind::BY_CONSTRUCTION,
                    "only top-level positive existential conjuncts introduce fresh private "
                    "constants; projecting these constants gives exactly the original "
                    "relation; objectives and original symbols remain unchanged",
                    {"src/lowering/positive_exists.cpp",
                     "test/lowering/test_positive_exists.cpp"}});
            }
            if (!target_contract.validate(t.diagnostics_)) { return; }
        }
        t.set_solver_requirements_ = t.model_->setSolverRequirements();
    }

    const bool has_packed_storage = !t.model_->bool_var_ranges.empty()
                                 || !t.model_->packed_bool_clauses.empty()
                                 || t.model_->packed_linear_rows != nullptr
                                 || !t.model_->scalar_var_ranges.empty()
                                 || t.model_->packed_function_calls != nullptr;
    if (has_packed_storage) {
        stage = "packed SMT lowering";
        // This path preserves the compact representation through the checked
        // pass pipeline and semantic contract, then streams directly. The
        // packed writer enforces its packed-only subset before Translation is
        // marked successful.
        Uir::Diagnostics packed_diags;
        if (!t.model_->scalar_var_ranges.empty() || t.model_->packed_function_calls) {
            stage = "packed scalar preamble construction";
            auto preamble = Uir::Hir::packedScalarPreamble(*t.model_, packed_diags);
            if (!preamble) { t.diagnostics_.merge(packed_diags); return; }
            // The suffix needs source declaration indices, function signatures,
            // objectives, and packed storage, but not the ordinary formulas.
            // Transfer ownership of those roots to the private preamble before
            // allocating the parser DAG, so consuming lowering can release each
            // root as soon as its target exists. An externally retained frontend
            // model must remain untouched, as must every translateHir caller.
            if (input_model || t.model_.use_count() == 1) {
                std::vector<Uir::Hir::Constraint>().swap(t.model_->constraints);
                for (auto& function : t.model_->funs) { function.body.reset(); }
                for (auto& declaration : t.model_->decls) {
                    declaration.lower_bound.reset();
                    declaration.upper_bound.reset();
                }
            }
            stage = "packed scalar SMT lowering";
            t.packed_base_parser_ = newParser();
            t.lowered_ = std::make_shared<Lower::HirToParser>(t.packed_base_parser_);
            const auto lower_started = clock::now();
            if (!t.lowered_->lowerConsumingForTranslation(
                    *preamble, t.report_, t.diagnostics_)) { return; }
            t.report_.mutableStats().lower_ms = ms_since(lower_started);
            stage = "packed scalar objective validation";
            // Count every scalar exactly once, including those borrowed by the
            // ordinary preamble and those unused by any constraint.
            t.report_.mutableStats().num_vars = t.model_->decls.size();
            for (const auto& range : t.model_->scalar_var_ranges) {
                t.report_.mutableStats().num_vars += range.count;
            }
            if (!Lower::validateObjectives(*t.model_, *t.lowered_, packed_diags)) {
                t.diagnostics_.merge(packed_diags); return;
            }
            if (opts.omt_dialect != Lower::OmtDialect::None || t.soft_objective_count_ != 0) {
                (void)Lower::emitObjectives(*t.model_, opts.omt_dialect, *t.lowered_, packed_diags, t.soft_objective_count_);
                if (packed_diags.hasErrors()) { t.diagnostics_.merge(packed_diags); return; }
            }
            if (t.model_->packed_function_calls) {
                for (const auto& batch : t.model_->packed_function_calls->batches) {
                    t.report_.mutableStats().num_constraints += batch.arguments.size() / batch.arity;
                }
            }
            t.report_.mutableStats().num_smt_nodes = 0;
        } else if (t.model_->packed_linear_rows) {
            if (!t.model_->bool_var_ranges.empty() || !t.model_->packed_bool_clauses.empty()) {
                t.diagnostics_.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "a packed numeric model cannot mix packed Boolean clause storage");
                return;
            }
            if (!Uir::Hir::validatePackedLinearRows(*t.model_, packed_diags)) {
                t.diagnostics_.merge(packed_diags);
                return;
            }
            // The immutable matrix stays shared. Lower only ordinary HIR:
            // declarations, nonliteral domains, semicontinuous formulas and
            // objectives use the established name, sort and dialect machinery.
            // Literal bounds remain in HIR for the complementary stream writer
            // instead of allocating a parser comparison node per endpoint.
            t.packed_base_parser_ = newParser();
            t.lowered_ = std::make_shared<Lower::HirToParser>(t.packed_base_parser_);
            const auto lower_started = clock::now();
            if (!t.lowered_->lowerPackedLinearPreamble(
                    *t.model_, t.report_, t.diagnostics_, true, true)) { return; }
            t.report_.mutableStats().lower_ms = ms_since(lower_started);
            t.packed_linear_symbols_.reserve(t.model_->decls.size());
            for (const auto& declaration : t.model_->decls) {
                t.packed_linear_symbols_.push_back(smtSymbol(
                    t.lowered_->emittedSymbolName(declaration.name, t.diagnostics_)));
            }
            if (t.diagnostics_.hasErrors()) { return; }
            // Preserve every objective dialect, including a later re-emission
            // from a Translation initially requested with OmtDialect::None.
            if (!Lower::validateObjectives(*t.model_, *t.lowered_, packed_diags)) {
                t.diagnostics_.merge(packed_diags);
                return;
            }
            if (opts.omt_dialect != Lower::OmtDialect::None || t.soft_objective_count_ != 0) {
                (void)Lower::emitObjectives(*t.model_, opts.omt_dialect, *t.lowered_, packed_diags, t.soft_objective_count_);
                if (packed_diags.hasErrors()) {
                    t.diagnostics_.merge(packed_diags);
                    return;
                }
            }
            for (const auto& batch : t.model_->packed_linear_rows->batches) {
                t.report_.mutableStats().num_constraints += batch.rows.size();
            }
            // There is no fully materialized target DAG on this route.
            t.report_.mutableStats().num_smt_nodes = 0;
        } else if (!Uir::Hir::validatePackedBoolClauseModel(*t.model_, packed_diags)) {
            t.diagnostics_.merge(packed_diags);
            return;
        }
        if (has_target_semantics) {
            stage = "packed target semantic validation";
            if (t.lowered_) { applyEmittedNames(target_contract, *t.lowered_); }
            const auto target_fidelity = t.report_.phaseFidelity();
            target_contract.claimed_fidelity = Uir::Fidelity::meet(
                target_contract.claimed_fidelity, target_fidelity);
            t.semantics_.add(std::move(target_contract));
            if (!t.semantics_.validate(t.diagnostics_)) return;
            recordSemanticStage(t.report_, t.semantics_.stages().back());
            if (!t.report_.fidelity().meets(profile->minFidelity())) {
                t.diagnostics_.error(ErrorCode::E_FIDELITY_REJECTED,
                    "target semantic fidelity is below the floor required by profile '"
                        + profile->id() + "'");
                return;
            }
        }
        t.report_.mutableStats().num_objectives = t.objective_count_;
        t.packed_smt_ = true;
        // Requirements were captured from complete post-pass HIR above. The
        // packed scalar emission model may now have relinquished formula roots;
        // re-analyzing that metadata would forget requirements of the preamble.
        if (t.report_.detailsEnabled()) {
            auto& provenance = t.report_.mutableProvenance();
            provenance.somtparser_version = "1.0.0";
            provenance.language_id = source_id;
            provenance.language_version = input_model ? "1" : lang->version();
            provenance.profile_id = profile->id();
            provenance.profile_content_hash = profile->contentHash();
            provenance.target_dialect = Lower::omtDialectName(opts.omt_dialect);
            t.report_.mutableStats().translate_ms =
                std::chrono::duration<double, std::milli>(clock::now() - started).count();
        }
        t.ok_ = true;
        return;
    }

    // 6. Lower onto a Parser.
    stage = "SMT lowering";
    t.parser_ = newParser();
    t.lowered_ = std::make_shared<Lower::HirToParser>(t.parser_);
    const auto lower_started = clock::now();
    // translateHir supplies a private container copy. A textual frontend may
    // retain its result elsewhere, so consume only when this container is ours.
    // Resetting roots never mutates the immutable expressions shared by callers.
    const bool private_model = input_model || t.model_.use_count() == 1;
    const bool lowered = private_model
        ? t.lowered_->lowerConsumingForTranslation(
              *t.model_, t.report_, t.diagnostics_)
        : t.lowered_->lower(*t.model_, t.report_, t.diagnostics_);
    t.report_.mutableStats().lower_ms = ms_since(lower_started);
    if (!lowered) {
        return;
    }

    // Frontends describe source -> relational core. Complete that account with
    // the stage this function has just executed.
    const auto semantics_started = clock::now();
    stage = "target semantic validation";
    if (has_target_semantics) {
        applyEmittedNames(target_contract, *t.lowered_);
        const auto target_fidelity = t.report_.phaseFidelity();
        target_contract.claimed_fidelity = Uir::Fidelity::meet(
            target_contract.claimed_fidelity, target_fidelity);
        t.semantics_.add(std::move(target_contract));
        if (!t.semantics_.validate(t.diagnostics_)) {
            return;
        }
        recordSemanticStage(t.report_, t.semantics_.stages().back());
        if (!t.report_.fidelity().meets(profile->minFidelity())) {
            t.diagnostics_.error(
                ErrorCode::E_FIDELITY_REJECTED,
                "target semantic fidelity is below the floor required by profile '"
                    + profile->id() + "'");
            return;
        }
    }

    t.report_.mutableStats().semantics_ms = target_contract_build_ms
        + ms_since(semantics_started);

    // 7. Prove objective emission succeeds now, while there is still a
    //    Diagnostics to report into. toSmt2() returns a bare string and has no
    //    channel for an error, so validating here is what lets it assert rather
    //    than silently hand back a model with its objectives missing.
    //
    //    Validated dialect-free FIRST, on purpose. This used to call
    //    emitObjectives() with opts.omt_dialect, which returns "" without
    //    looking at anything when the dialect is None -- so the one
    //    configuration that emits no objectives was also the one that checked
    //    none, and toSmt2(Z3) on such a Translation hit the assert this step
    //    exists to justify.
    //
    //    And then AGAIN for the configured dialect, which the dialect-free pass
    //    cannot stand in for: whether an objective can be emitted is partly a
    //    property of the target. `pareto` is a combination Z3 expresses and the
    //    2025 proposal does not, so an XCSP3 multi-objective instance passed
    //    the dialect-free check, translated, reported ok(), and then threw from
    //    toSmt2() -- which has no channel for an error, so the CLI turned it
    //    into SIGABRT. The assert at the top of this file said the failure was
    //    "after translate() validated it"; translate() had validated something
    //    else. A dialect the caller never configured can still throw from
    //    toSmt2(dialect), and that stays an assert: it is a caller asking for a
    //    guarantee this function never gave.
    stage = "objective validation";
    {
        Uir::Diagnostics emit_diags;
        if (!Lower::validateObjectives(*t.model_, *t.lowered_, emit_diags)) {
            t.diagnostics_.merge(emit_diags);
            return;
        }
    }
    if (opts.omt_dialect != Lower::OmtDialect::None || t.soft_objective_count_ != 0) {
        Uir::Diagnostics emit_diags;
        (void)Lower::emitObjectives(*t.model_, opts.omt_dialect, *t.lowered_,
                                    emit_diags, t.soft_objective_count_);
        if (emit_diags.hasErrors()) {
            t.diagnostics_.merge(emit_diags);
            return;
        }
    }

    // The parser now owns the complete lowered model, and the report and
    // contracts have their own validated metadata. Re-emission only needs the
    // HIR objectives and their combination policy. Keeping every constraint
    // here would retain both full representations throughout serialization.
    // Use a separate container rather than clearing the frontend/input model:
    // immutable expressions may also belong to the translateHir caller.
    stage = "emission metadata";
    auto emission_model = std::make_shared<Uir::Hir::ConstraintModel>();
    emission_model->objectives = t.model_->objectives;
    emission_model->objective_combination = t.model_->objective_combination;
    t.model_ = std::move(emission_model);
    // The parser already owns every declaration and function body. Future
    // term lowering is limited to objectives; discard the duplicate indexes
    // for constraint-only variables before module serialization.
    t.lowered_->retainObjectiveBindings(*t.model_);

    // 8. Provenance, so the row can be traced back to this configuration.
    if (t.report_.detailsEnabled()) {
        auto& prov = t.report_.mutableProvenance();
        prov.somtparser_version = "1.0.0";
        prov.language_id = source_id;
        prov.language_version = input_model ? "1" : lang->version();
        prov.profile_id = profile->id();
        prov.profile_content_hash = profile->contentHash();
        prov.target_dialect = Lower::omtDialectName(opts.omt_dialect);

        const auto elapsed = clock::now() - started;
        t.report_.mutableStats().translate_ms =
            std::chrono::duration<double, std::milli>(elapsed).count();

    }
    t.ok_ = true;
    };   // end of body

    try {
        body();
    } catch (const std::bad_alloc&) {
        t.ok_ = false;
        t.diagnostics_.error(ErrorCode::E_RESOURCE,
                             std::string("memory allocation failed during ") + stage);
    } catch (const std::exception& e) {
        t.ok_ = false;
        t.diagnostics_.error(ErrorCode::E_INTERNAL,
                             std::string("translate() threw: ") + e.what());
    } catch (...) {
        t.ok_ = false;
        t.diagnostics_.error(ErrorCode::E_INTERNAL,
                             "translate() threw an unknown exception");
    }
    return t;
}

} // namespace SOMTParser
