/* -*- Source -*-
 * SMT-LIB 2 baseline frontend.
 *
 * The format is docs/languages/smtlib2.md. This is the arm every other language
 * is measured against: the same question, asked directly, so a difference in
 * solver time between it and a translated benchmark is a property of the
 * translation rather than of the question.
 *
 * It carries no reader. The engine already parses SMT-LIB, so this parses with
 * it and lifts with Lower::ParserToHir. What the frontend adds is a **boundary
 * that says what it did not carry**, and that is the whole point of the file:
 *
 * The HIR covers less than the engine's 326 node kinds. A baseline that
 * silently translated the part it understood and dropped the rest would
 * produce, under the name "SMT-LIB", a benchmark for a fragment nobody
 * competes in -- and it would compare that against languages translated in
 * full. §4.1 calls this a second-filter failure of an unusual kind: the
 * question is preserved perfectly and the *corpus* is silently replaced.
 *
 * So an unliftable construct is an E_UNSUPPORTED_CONSTRUCT naming the kind, and
 * the instance is not translated at all. A missing instance is a visible gap in
 * a results table; a silently smaller one is not.
 *
 * The logic is carried into the report for the same reason. `(set-logic
 * QF_LIA)` is a restriction the file asserts about itself, and a row that does
 * not record it cannot be grouped by division -- which is how SMT-COMP results
 * are read.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/smtlib2.h"

#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/frontend/parser.h"
#include "cvc5_sets.h"

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <system_error>
#include <unordered_set>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

class SmtLib2Language : public Language {
public:
    SmtLib2Language() {
        // MEASURED, not asserted: running this frontend over a corpus and
        // counting what refused. docs/languages/smtlib2.md keeps the same
        // figures, and they are figures rather than a judgement precisely so
        // that a claim about what the baseline covers can be rechecked.
        //
        // The number has been re-measured three times with three instruments,
        // and each found something the previous one could not:
        //
        //   `test/instances` -- 21 scripts the ENGINE has always parsed, in
        //       this repository the whole time -- was 10 of 21, and named two
        //       clusters the table had not counted at all: indexed operators
        //       and the regular expressions.
        //
        //   test/lowering/test_lift_operator_sweep.cpp asks the question once
        //       per OPERATOR rather than once per file. It found three rows
        //       counted as supported and not reachable -- finite sets,
        //       floating-point literals, the `to_fp` conversions -- and four
        //       nothing had exercised. Sets are the clearest: all nine set
        //       operators were correctly in the lift table and `liftSort` had
        //       no line for `(Set T)`, so every script naming the sort died at
        //       its DECLARATION. A table that is full one line above an empty
        //       one reads as complete from either end.
        //
        //   The ENGINE's own gaps bound this number from below. `(_ divisible
        //       n)` was not a missing row but an unaskable one: the engine had
        //       only a non-standard `is_divisible`, so the frontend never saw
        //       the construct to fail on it.
        //
        // Of the seven operators the sweep named, six were added to the HIR --
        // rotate_left, rotate_right, repeat, bvcomp, is_int, str.is_digit --
        // because each is standard SMT-LIB and expansion is one-way: a rotation
        // that came back as two shifts and an `or` is a different script,
        // measured differently, with no diagnostic saying so.
        //
        // Applied sort constructors are the row with the most history. They
        // were counted as supported and were not: `(declare-sort S 1)` used as
        // `(S Bool)` lifted by flattening the application to the constructor's
        // NAME, so `(S Bool)` and `(S Int)` became one sort, and the emitted
        // script read back -- which is how a wrong answer passed for a
        // supported feature. Hir::Sort now carries the arguments, so the row is
        // supported for real.
        // Algebraic datatypes were the last row of the same shape as sets:
        // SortKind::DATATYPE, DatatypeDecl and the three expression kinds
        // were all in the HIR, the lowering emitted them, and the lift had
        // NOTHING -- a whole theory the IR carried that could not be read
        // out of a script. Mutual recursion additionally needed the ENGINE
        // to stop splitting one declaration group into two commands.
        coverage_.total = 26;
        coverage_.supported = 25;
        coverage_.missing = {
            "real algebraic numbers (root-obj), which is a Z3 extension and "
            "not SMT-LIB -- refused on principle rather than for now, which "
            "is why test_smtlib2.cpp takes its unliftable example from here",
        };
        // What moved on 2026-08-15, and why each was a gap rather than a
        // decision:
        //
        //   define-fun bodies now cross as HIR definitions. Replacing every
        //       source macro with a UF and an equation unnecessarily adds
        //       quantifiers for parameters, or many extra solver variables for
        //       zero-argument DAG aliases. Recursive definitions keep the
        //       lifter's explicit recursive-group/equation policy.
        //
        //   let                          inlined. SMT-LIB defines let by
        //       substitution, so this is exact; it costs SIZE, not meaning.
        //       Before, a let-bound reference lifted as an IDENT the model
        //       never declared.
        //
        //   regular expressions          every operator already existed in the
        //       HIR and none was in the lift table.
        //
        //   indexed operators            `(_ extract hi lo)`, the extensions,
        //       `(_ re.loop i j)`. These could not be table entries: the engine
        //       stores indices as CHILDREN and the HIR in `Expr::indices`.
    }

    std::string id() const override { return "smtlib2"; }
    std::string displayName() const override { return "SMT-LIB 2"; }
    std::string version() const override { return "2.6"; }
    std::vector<std::string> extensions() const override { return {".smt2"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    /** Lower than CHC's, deliberately. Both claim `.smt2`; a file that opens
     *  `(set-logic HORN)` is a CHC instance and this must not win the tie, but
     *  every other SMT-LIB file should land here rather than nowhere. */
    double sniff(std::string_view head) const override {
        if (head.find("set-logic HORN") != std::string_view::npos) { return 0.0; }
        return head.find("(set-logic") != std::string_view::npos
                   || head.find("(declare-") != std::string_view::npos
                   || head.find("(assert") != std::string_view::npos
               ? 0.5 : 0.0;
    }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) override {
        ParseOutcome out;
        std::string src = unit.inline_source;
        if (src.empty()) {
            std::error_code ec;
            if (std::filesystem::is_directory(unit.main_path, ec)) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "'" + unit.main_path + "' is a directory");
                return out;
            }
            std::ifstream in(unit.main_path, std::ios::binary);
            if (!in) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "cannot open '" + unit.main_path + "'");
                return out;
            }
            std::ostringstream ss;
            ss << in.rdbuf();
            src = ss.str();
        }

        std::size_t set_rewrites = 0;
        const auto compatibility = opts.options.find("cvc5_sets");
        if (compatibility != opts.options.end()
            && compatibility->second != "0" && compatibility->second != "1") {
            out.diagnostics.error(ErrorCode::E_PARSE, "cvc5_sets must be 0 or 1");
            return out;
        }
        const bool sets = compatibility != opts.options.end() && compatibility->second == "1";
        ParserPtr engine = newParser();
        engine->setCommandLogging(true);
        try {
            if (sets) {
                src = Cvc5Sets::normalize(src, set_rewrites);
            }
            if (!engine->parseStr(src)) {
                // Two different conclusions, and they feed two different
                // statistics. An unknown symbol says this build does not
                // implement the construct. Calling an unknown extension
                // malformed input is a wrong claim
                // about a valid benchmark, and it lands in the bucket that
                // measures file quality rather than the one that measures
                // coverage.
                const ParseErrorException* why = engine->lastParseError();
                if (why != nullptr && why->kind() == ParseErrorException::Kind::ARITY) {
                    out.diagnostics.error(
                        ErrorCode::E_PARSE,
                        "wrong number of arguments for '" + why->symbol() + "'",
                        Uir::SourceLoc{unit.main_path.empty() ? unit.display_name : unit.main_path,
                                       set_rewrites ? 0 : static_cast<int>(why->line()), 0});
                    return out;
                }
                if (why != nullptr
                    && why->kind() == ParseErrorException::Kind::UNKNOWN_SYMBOL) {
                    out.diagnostics.error(
                        ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'" + why->symbol() + "' is not a construct this build "
                        "reads; it is an extension or a gap, not a malformed "
                        "script",
                        Uir::SourceLoc{unit.main_path.empty() ? unit.display_name
                                                              : unit.main_path,
                                       set_rewrites ? 0 : static_cast<int>(why->line()), 0});
                    return out;
                }
                out.diagnostics.error(ErrorCode::E_PARSE,
                                      "not a well-formed SMT-LIB script");
                return out;
            }
        } catch (const std::bad_alloc&) {
            // translate() owns the common E_RESOURCE boundary. Do not turn an
            // allocation failure on a valid script into an E_PARSE diagnostic.
            throw;
        } catch (const std::exception& e) {
            out.diagnostics.error(ErrorCode::E_PARSE,
                                  std::string("SMT-LIB parse failed: ") + e.what());
            return out;
        }

        // Assumptions belong to one check, not to the final assertion set.
        // A single terminal query has an exact relational interpretation;
        // refuse ambiguous incremental scripts rather than silently dropping
        // the assumptions or conjoining independent checks.
        const auto query_assumptions = engine->getAssumptions();
        for (const auto& command : engine->getScript().commands()) {
            if (command.isCheckSat() || command.isCheckSatAssuming()) {
                out.terminal_responses.clear();
            } else if (command.type == CMD_TYPE::CT_GET_OBJECTIVES
                       || command.type == CMD_TYPE::CT_GET_MODEL) {
                out.terminal_responses.push_back(command.original);
            }
        }
        bool has_assumption_query = false;
        for (const auto& command : engine->getScript().commands()) {
            has_assumption_query = has_assumption_query || command.isCheckSatAssuming();
        }
        if (has_assumption_query) {
            std::size_t checks = 0;
            bool after_check = false, late_mutation = false;
            for (const auto& command : engine->getScript().commands()) {
                if (command.isCheckSat() || command.isCheckSatAssuming()) {
                    ++checks; after_check = true; continue;
                }
                const std::string name = command.kindName();
                if (after_check && name != "exit" && name != "echo" && name != "set-info"
                    && name.rfind("get-", 0) != 0) { late_mutation = true; }
            }
            if (checks != 1 || query_assumptions.size() != 1 || late_mutation) {
                out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "check-sat-assuming requires one terminal query; multiple queries "
                    "or later context mutations need an explicit query selection");
                return out;
            }
            for (const auto& assumption : query_assumptions.front()) {
                if (!assumption || !assumption->getSort()->isBool() || !engine->assert(assumption)) {
                    out.diagnostics.error(ErrorCode::E_TYPE, "query assumption must be Boolean");
                    return out;
                }
            }
        }

        auto model = std::make_shared<H::ConstraintModel>();
        Lower::ParserToHir up(engine);
        if (!up.lift(*model, out.diagnostics, true)) {
            // Deliberately fatal. See the header comment: a baseline that
            // dropped what it could not lift would replace the corpus while
            // keeping the name.
            return out;
        }

        const auto definitions = std::count_if(model->funs.begin(), model->funs.end(),
            [](const H::FunDecl& function) {
                return function.body && function.recursive_group.empty();
            });
        if (definitions) {
            Uir::EncodingChoice choice;
            choice.site = unit.main_path.empty() ? unit.display_name : unit.main_path;
            choice.unified_op = "define-fun";
            choice.strategy = "hir-defined-functions";
            choice.fidelity = Uir::Fidelity::exact();
            choice.rationale = std::to_string(definitions)
                + " nonrecursive source definitions retain their bodies and parameter "
                  "scopes in HIR rather than adding UF declarations and defining "
                  "assertions. Target lowering retains its bounded macro-sharing policy.";
            out.report.addChoice(std::move(choice));
        }

        // The expression lift handles hard assertions. Carry optimization
        // separately: accepting only the assertions silently changes the task.
        const auto soft = engine->getSoftAssertions();
        const auto objectives = engine->getObjectives();
        const auto& options = engine->getOptions()->options;
        const auto priority = options.find("opt.priority");
        if (!soft.empty()) {
            const auto groups = engine->getGroupedSoftAssertions();
            std::vector<std::string> group_of(soft.size());
            std::unordered_set<std::string> active_groups;
            for (const auto& group : groups) {
                for (const auto index : group.second) {
                    if (index >= soft.size()) {
                        out.diagnostics.error(ErrorCode::E_INTERNAL, "soft assertion group index out of range");
                        return out;
                    }
                    group_of[index] = group.first;
                }
            }
            for (const auto& group : group_of) { active_groups.insert(group); }
            if (!objectives.empty() || active_groups.size() != 1
                || (priority != options.end() && priority->second != "lex")) {
                out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "assert-soft lifting requires one cost group and no explicit objectives; "
                    "mixed objective ordering must not be guessed");
                return out;
            }
            const auto weights = engine->getSoftWeights();
            for (std::size_t i = 0; i < soft.size(); ++i) {
                H::Constraint constraint;
                constraint.formula = up.liftExpr(soft[i], out.diagnostics);
                if (!constraint.formula) { return out; }
                constraint.soft = true;
                constraint.group = group_of[i];
                constraint.weight_text = "1";
                if (i < weights.size() && weights[i]) {
                    const auto weight = up.liftExpr(weights[i], out.diagnostics);
                    if (!weight) { return out; }
                    if (weight->kind != H::ExprKind::LIT_INT || weight->name.empty()
                        || weight->name.find_first_not_of("0123456789") != std::string::npos
                        || weight->name.find_first_not_of('0') == std::string::npos) {
                        out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "assert-soft lifting requires an exact positive integer weight");
                        return out;
                    }
                    constraint.weight_text = weight->name;
                }
                model->constraints.push_back(std::move(constraint));
            }
        }
        if (!objectives.empty() && priority != options.end() && priority->second != "lex") {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "SMT-LIB objective lifting supports only opt.priority lex");
            return out;
        }
        if (objectives.size() > 1 && priority == options.end()) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "multiple SMT-LIB objectives require explicit opt.priority lex");
            return out;
        }
        for (const auto& objective : objectives) {
            if (!objective || (!objective->isMinimize() && !objective->isMaximize()) ||
                objective->getEpsilon() != NodeManager::NULL_NODE ||
                objective->getM() != NodeManager::NULL_NODE ||
                objective->getCompareOperator() != (objective->isMinimize()
                    ? COMP_KIND::COMP_LT : COMP_KIND::COMP_GT)) {
                out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                      "unsupported SMT-LIB objective kind, comparison, epsilon or M");
                return out;
            }
            const auto& term = objective->getObjectiveTerm();
            if (!term || !term->getSort() ||
                (!term->getSort()->isInt() && !term->getSort()->isReal()
                 && !term->getSort()->isIntOrReal())) {
                out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                      "SMT-LIB objective must have Int or Real sort");
                return out;
            }
            auto lifted = up.liftExpr(term, out.diagnostics);
            if (!lifted) { return out; }
            model->objectives.push_back({objective->isMinimize() ? H::ObjKind::MINIMIZE
                                                               : H::ObjKind::MAXIMIZE,
                                         std::move(lifted), "", {}});
        }
        if (objectives.size() > 1) {
            model->objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
        }

        // The logic the file asserts about itself. Recorded rather than
        // dropped: a results row that does not carry it cannot be grouped by
        // SMT-COMP division, and translating a QF_LIA benchmark under a wider
        // logic is not wrong but is no longer the same benchmark.
        const std::string logic = engine->getOptions()->logic;
        Uir::EncodingChoice ch;
        ch.site       = unit.main_path.empty() ? unit.display_name : unit.main_path;
        ch.unified_op = "set-logic";
        ch.strategy   = logic;
        ch.fidelity   = Uir::Fidelity::exact();
        ch.rationale =
            "the file declares logic '" + logic
            + "'; it is carried into the report because a row that loses it cannot be "
              "grouped by division, which is how these results are read";
        out.report.addChoice(std::move(ch));

        if (std::any_of(model->datatypes.begin(), model->datatypes.end(),
                        [](const H::DatatypeDecl& dt) { return dt.coinductive; })) {
            Uir::EncodingChoice co;
            co.site = unit.main_path.empty() ? unit.display_name : unit.main_path;
            co.unified_op = "codatatypes";
            co.strategy = "native-coinductive-declarations";
            co.fidelity = Uir::Fidelity::exact();
            co.rationale = "cvc5's greatest-fixed-point datatype extension is carried through HIR "
                "and emitted as declare-codatatypes; no finite or inductive replacement is made. "
                "The target solver must implement this extension.";
            out.report.addChoice(std::move(co));
        }

        if (set_rewrites) {
            Uir::EncodingChoice compatibility_choice;
            compatibility_choice.site = unit.main_path.empty() ? unit.display_name : unit.main_path;
            compatibility_choice.unified_op = "cvc5-finite-sets";
            compatibility_choice.strategy = "typed-set-identities";
            compatibility_choice.fidelity = Uir::Fidelity::exact();
            compatibility_choice.rationale = std::to_string(set_rewrites)
                + " explicit compatibility rewrites: is_empty(X) iff card(X)=0; "
                  "bare set.empty is explicitly ascribed Set Bool, matching cvc5 1.4. "
                  "Native typing is retained; other element sorts require an explicit ascription. "
                  "Diagnostic lines refer to normalized commands.";
            out.report.addChoice(std::move(compatibility_choice));
        }

        out.model = model;
        out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
            *out.model, "smtlib2", out.report.fidelity()));
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkSmtLib2Language() { return std::make_shared<SmtLib2Language>(); }

} // namespace SOMTParser::Lang
