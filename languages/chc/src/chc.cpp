/* -*- Source -*-
 * CHC-COMP frontend.
 *
 * The format is docs/languages/chc-comp.md; its `implicit-constraints` block is
 * the specification this file implements, and each entry has a fixture in
 * languages/chc/instances.
 *
 * CHC-COMP files ARE SMT-LIB 2 -- the same syntax, restricted to Horn clauses
 * over uninterpreted predicates. So this frontend does not carry a reader of
 * its own: it borrows the engine's parser and lifts the result with
 * Lower::ParserToHir, which is the direction that had to exist before this
 * language or the SMT-LIB baseline could be written at all.
 *
 * What makes it a language rather than a thin alias is its format and shape
 * check. The accepted command sequence and clause grammar are the CHC-COMP
 * format revision of 2023-03-31, not arbitrary SMT-LIB carrying set-logic HORN.
 * Predicate interpretations are ordinary components of an SMT model, so the
 * unchanged universally closed clause set is an exact first-order embedding:
 * target SAT means that an interpretation of every declared relation exists.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/chc.h"

#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/frontend/parser.h"

#include <filesystem>
#include <fstream>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <system_error>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

/** Names declared by CHC-COMP's `fun_decl`. A zero-argument Boolean function is
 *  a nullary relation, not a separate category of model variable. */
std::unordered_set<std::string> predicateNames(const H::ConstraintModel& m) {
    std::unordered_set<std::string> out;
    for (const H::VarDecl& v : m.decls) {
        if (v.sort.kind == H::SortKind::BOOL) { out.insert(v.name); }
    }
    for (const H::FunDecl& f : m.funs) {
        if (f.result.kind == H::SortKind::BOOL) { out.insert(f.name); }
    }
    return out;
}

bool isPredicateOccurrence(const H::ExprPtr& e,
                           const std::unordered_set<std::string>& preds) {
    if (!e || preds.count(e->name) == 0) { return false; }
    return e->kind == H::ExprKind::IDENT || e->kind == H::ExprKind::APPLY;
}

bool isFalseLiteral(const H::ExprPtr& e) {
    return e && e->kind == H::ExprKind::LIT_BOOL && !e->bool_value;
}

/** Does @p e contain an application of an uninterpreted predicate anywhere?
 *  Used to check that the interpreted part of a body really is interpreted. */
bool mentionsPredicate(const H::ExprPtr& e, const std::unordered_set<std::string>& preds) {
    if (!e) { return false; }
    if (isPredicateOccurrence(e, preds)) { return true; }
    for (const H::ExprPtr& a : e->args) {
        if (mentionsPredicate(a, preds)) { return true; }
    }
    return false;
}

struct Clause {
    std::vector<H::ExprPtr> body_predicates;   // applications of uninterpreted predicates
    H::ExprPtr              head;              // predicate application, or false
    bool                    is_query = false;  // head is false
};

class ChcLanguage : public Language {
public:
    ChcLanguage() {
        // SMT-LIB background terms, linear/non-linear clause bodies, arrays,
        // bit-vectors, Reals and ADTs all use the common typed HIR.
        coverage_.total = 7;
        coverage_.supported = 7;
    }

    std::string id() const override { return "chc"; }
    std::string displayName() const override { return "CHC-COMP (constrained Horn clauses)"; }
    std::string version() const override { return "smtlib2-horn"; }
    // .smt2 is shared with the SMT-LIB baseline, which is why sniff() below is
    // not optional: the extension cannot decide between them.
    std::vector<std::string> extensions() const override { return {".smt2"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    /** `(set-logic HORN)` is the declaration that this is a CHC file, and it is
     *  the only thing that distinguishes it from plain SMT-LIB at the level of
     *  a file's first bytes. Without it the two languages are
     *  indistinguishable by extension AND by head, which is exactly the
     *  ambiguity LanguageRegistry::detect refuses to guess through. */
    double sniff(std::string_view head) const override {
        return head.find("set-logic HORN") != std::string_view::npos ? 0.95 : 0.0;
    }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions&) override {
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

        ParserPtr engine = newParser();
        engine->setCommandLogging(true);
        try {
            if (!engine->parseStr(src)) {
                out.diagnostics.error(ErrorCode::E_PARSE,
                                      "not a well-formed SMT-LIB script");
                return out;
            }
        } catch (const std::exception& e) {
            out.diagnostics.error(ErrorCode::E_PARSE,
                                  std::string("SMT-LIB parse failed: ") + e.what());
            return out;
        }

        const std::string source_name = unit.main_path.empty()
                                            ? unit.display_name : unit.main_path;
        if (!validateScript(engine->getScript(), source_name, out.diagnostics)) {
            return out;
        }
        const bool uses_z3_hardware_division =
            usesZ3HardwareDivisionAlias(engine->getScript());

        auto model = std::make_shared<H::ConstraintModel>();
        Lower::ParserToHir up(engine);
        if (!up.lift(*model, out.diagnostics)) {
            return out;
        }

        const std::unordered_set<std::string> preds = predicateNames(*model);
        if (preds.empty()) {
            // Every CHC instance has at least one predicate to solve for. A
            // file without one is a plain SMT-LIB query that happens to declare
            // (set-logic HORN), and translating it here would put a row in the
            // CHC results table that no CHC solver was ever asked about.
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "no uninterpreted predicate is declared, so there is "
                                  "nothing to solve for; a CHC instance declares at "
                                  "least one Boolean `declare-fun`, including a possible "
                                  "nullary predicate");
            return out;
        }

        std::size_t queries = 0;
        std::size_t query_index = 0;
        for (std::size_t i = 0; i < model->constraints.size(); ++i) {
            Clause c;
            if (!clauseOf(model->constraints[i].formula, preds, c, out.diagnostics)) {
                return out;
            }
            if (c.is_query) {
                ++queries;
                query_index = i;
            }
        }

        if (queries == 0) {
            // Rules alone ARE trivially satisfiable -- interpret every predicate
            // as universally true and every implication holds. That is the case
            // chc-comp.md §4.1 describes, and it is a property of a file with no
            // query rather than of the translation. Refusing it is the honest
            // answer: the script would be satisfiable for a reason that has
            // nothing to do with the program it came from.
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "no query clause: every assertion has a predicate in "
                                  "its head, so interpreting every predicate as true "
                                  "satisfies all of them and the answer would say "
                                  "nothing about the program");
            return out;
        }
        if (queries != 1) {
            out.diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "CHC-COMP requires exactly one false-headed query clause; found "
                    + std::to_string(queries));
            return out;
        }
        if (query_index + 1 != model->constraints.size()) {
            out.diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "the unique false-headed query must be the final assertion in a "
                "CHC-COMP benchmark",
                model->constraints[query_index].loc);
            return out;
        }

        // The verdict reading, recorded rather than left to a reader. CHC's
        // `sat` means a solution exists and the program is SAFE, which is the
        // opposite of the intuition `unsat` = "no bug". The translated script
        // has the same polarity -- satisfiability in SMT already quantifies the
        // uninterpreted symbols existentially -- so this is documentation of
        // the mapping and not a fidelity loss.
        Uir::EncodingChoice ch;
        ch.site       = unit.main_path.empty() ? unit.display_name : unit.main_path;
        ch.unified_op = "horn-clauses";
        ch.strategy   = "assert-clauses-verbatim";
        ch.fidelity   = Uir::Fidelity::exact();
        ch.rationale =
            "the clause set is asserted as written; SMT satisfiability already "
            "quantifies the uninterpreted predicates existentially, so `sat` means a "
            "solution exists and the program is SAFE -- the opposite of the reading "
            "`unsat` = no bug that the names invite";
        out.report.addChoice(std::move(ch));

        if (uses_z3_hardware_division) {
            Uir::EncodingChoice alias;
            alias.site = source_name;
            alias.unified_op = "z3-bv-hardware-division";
            alias.strategy = "canonicalize-to-smtlib-2.6-total-bv-division";
            alias.fidelity = Uir::Fidelity::exact();
            alias.rationale =
                "the official CHC-COMP BV corpus uses Z3's *_i hardware "
                "division/remainder symbols; their divisor-zero values equal the "
                "total public SMT-LIB 2.6 operators, so the target uses canonical "
                "bvudiv/bvurem/bvsdiv/bvsrem/bvsmod spellings";
            out.report.addChoice(std::move(alias));
        }

        out.model = model;
        out.semantics.add(Uir::Sem::chcToRelationalContract(
            *out.model, out.report.fidelity()));
        return out;
    }

private:
    enum class ScriptPhase { PREFIX, AFTER_LOGIC, DATATYPES, PREDICATES,
                             ASSERTIONS, CHECKED, EXITED };

    static Uir::SourceLoc commandLoc(const Command& command,
                                     const std::string& source_name) {
        return {source_name, static_cast<int>(command.range.begin.line),
                static_cast<int>(command.range.begin.column)};
    }

    /** Validate the exact CHC-COMP command grammar before HIR lifting erases
     *  command order and command kinds. */
    static bool validateScript(const Script& script, const std::string& source_name,
                               Uir::Diagnostics& diags) {
        ScriptPhase phase = ScriptPhase::PREFIX;
        std::size_t logics = 0;
        std::size_t predicates = 0;
        std::size_t assertions = 0;
        std::size_t checks = 0;

        for (const Command& command : script.commands()) {
            bool accepted = false;
            switch (phase) {
            case ScriptPhase::PREFIX:
                if (command.type == CMD_TYPE::CT_SET_INFO) {
                    accepted = true;
                } else if (command.type == CMD_TYPE::CT_SET_LOGIC) {
                    accepted = true;
                    phase = ScriptPhase::AFTER_LOGIC;
                    ++logics;
                    if (command.logic != "HORN") {
                        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                    "CHC-COMP requires `(set-logic HORN)`, not `"
                                        + command.logic + "`",
                                    commandLoc(command, source_name));
                        return false;
                    }
                }
                break;
            case ScriptPhase::AFTER_LOGIC:
                if (command.type == CMD_TYPE::CT_SET_INFO) {
                    accepted = true;
                } else if (command.type == CMD_TYPE::CT_DECLARE_DATATYPES) {
                    accepted = true;
                    phase = ScriptPhase::DATATYPES;
                } else if (command.type == CMD_TYPE::CT_DECLARE_FUN) {
                    accepted = true;
                    phase = ScriptPhase::PREDICATES;
                }
                break;
            case ScriptPhase::DATATYPES:
                if (command.type == CMD_TYPE::CT_DECLARE_DATATYPES) {
                    accepted = true;
                } else if (command.type == CMD_TYPE::CT_DECLARE_FUN) {
                    accepted = true;
                    phase = ScriptPhase::PREDICATES;
                }
                break;
            case ScriptPhase::PREDICATES:
                if (command.type == CMD_TYPE::CT_DECLARE_FUN) {
                    accepted = true;
                } else if (command.type == CMD_TYPE::CT_ASSERT) {
                    accepted = true;
                    phase = ScriptPhase::ASSERTIONS;
                }
                break;
            case ScriptPhase::ASSERTIONS:
                if (command.type == CMD_TYPE::CT_ASSERT) {
                    accepted = true;
                } else if (command.type == CMD_TYPE::CT_CHECK_SAT) {
                    accepted = true;
                    phase = ScriptPhase::CHECKED;
                    ++checks;
                }
                break;
            case ScriptPhase::CHECKED:
                if (command.type == CMD_TYPE::CT_EXIT) {
                    accepted = true;
                    phase = ScriptPhase::EXITED;
                }
                break;
            case ScriptPhase::EXITED: break;
            }

            if (!accepted) {
                diags.error(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "command `" + std::string(command.kindName())
                        + "` is not allowed at this position by the CHC-COMP format",
                    commandLoc(command, source_name));
                return false;
            }
            if (command.type == CMD_TYPE::CT_DECLARE_FUN) {
                ++predicates;
                if (!command.sort || !command.sort->isBool()) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "CHC-COMP `declare-fun` declarations must return Bool",
                                commandLoc(command, source_name));
                    return false;
                }
            } else if (command.type == CMD_TYPE::CT_ASSERT) {
                ++assertions;
            }
        }

        if (logics != 1) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "CHC-COMP requires exactly one `(set-logic HORN)` command");
            return false;
        }
        if (predicates == 0) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "CHC-COMP requires at least one Boolean `declare-fun`");
            return false;
        }
        if (assertions == 0) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "CHC-COMP requires a false-headed query assertion");
            return false;
        }
        if (checks != 1 || phase == ScriptPhase::ASSERTIONS
            || phase == ScriptPhase::PREDICATES) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "CHC-COMP requires exactly one final `(check-sat)` command");
            return false;
        }
        return true;
    }

    static bool usesZ3HardwareDivisionAlias(const Script& script) {
        static const char* aliases[] = {
            "bvudiv_i", "bvurem_i", "bvsdiv_i", "bvsrem_i", "bvsmod_i",
        };
        for (const Command& command : script.commands()) {
            if (command.type != CMD_TYPE::CT_ASSERT) { continue; }
            for (const char* alias : aliases) {
                if (command.original.find(alias) != std::string::npos) { return true; }
            }
        }
        return false;
    }

    static bool predicateAtom(const H::ExprPtr& expression,
                              const std::unordered_set<std::string>& predicates,
                              bool distinct_arguments, const std::string& position,
                              Uir::Diagnostics& diags) {
        if (!isPredicateOccurrence(expression, predicates)) { return false; }
        if (expression->kind == H::ExprKind::IDENT) { return true; }

        std::set<std::string> names;
        for (const H::ExprPtr& argument : expression->args) {
            if (!argument || argument->kind != H::ExprKind::BOUND_VAR) {
                diags.error(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "an uninterpreted predicate in a CHC-COMP " + position
                        + " may be applied only to quantified variables, not terms",
                    argument ? argument->loc : expression->loc);
                return false;
            }
            if (distinct_arguments && !names.insert(argument->name).second) {
                diags.error(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "predicate arguments in a CHC-COMP head must be distinct variables",
                    argument->loc);
                return false;
            }
        }
        return true;
    }

    /** Decompose one assertion into a Horn clause, or refuse it by name.
     *
     *  The shape is `forall x. (body => head)`. Only a nullary predicate fact
     *  may omit the quantifier in the official grammar. */
    bool clauseOf(const H::ExprPtr& assertion,
                  const std::unordered_set<std::string>& preds, Clause& out,
                  Uir::Diagnostics& diags) {
        H::ExprPtr e = assertion;
        bool universally_quantified = false;
        if (e && (e->kind == H::ExprKind::FORALL)) {
            if (e->binders.empty()) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "CHC-COMP universal clauses require at least one bound variable",
                            e->loc);
                return false;
            }
            universally_quantified = true;
            e = e->args.empty() ? nullptr : e->args[0];
        } else if (e && e->kind == H::ExprKind::EXISTS) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "an existentially quantified assertion is not a Horn clause; "
                        "a clause is universally quantified over its free variables",
                        assertion->loc);
            return false;
        }
        if (!e) {
            diags.error(ErrorCode::E_PARSE, "empty assertion");
            return false;
        }

        H::ExprPtr body, head;
        if (e->kind == H::ExprKind::OP && e->op == H::Op::IMPLIES && e->args.size() == 2) {
            body = e->args[0];
            head = e->args[1];
        } else {
            Uir::Diagnostics atom_diags;
            if (predicateAtom(e, preds, true, "head", atom_diags)
                && (universally_quantified || e->kind == H::ExprKind::IDENT)) {
                body = H::mkBool(true);
                head = e;
            } else {
                if (atom_diags.hasErrors()) {
                    diags.merge(atom_diags);
                    return false;
                }
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "assertion is not a CHC-COMP Horn clause: a non-nullary "
                            "fact must be universally quantified, and its head must be "
                            "one predicate atom",
                            e->loc);
                return false;
            }
        }

        if (body && !universally_quantified
            && e->kind == H::ExprKind::OP && e->op == H::Op::IMPLIES) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "CHC-COMP implications, including the query, must be "
                        "universally quantified over at least one variable",
                        e->loc);
            return false;
        }

        if (isFalseLiteral(head)) {
            out.is_query = true;
        } else if (predicateAtom(head, preds, true, "head", diags)) {
            out.head = head;
        } else if (diags.hasErrors()) {
            return false;
        } else {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "the head of a Horn clause must be one uninterpreted predicate "
                        "application or `false`; a disjunction or an interpreted atom "
                        "in the head makes the instance non-Horn, and a CHC solver "
                        "would not accept it either",
                        head ? head->loc : e->loc);
            return false;
        }

        return collectBody(body, preds, out, diags);
    }

    /** A body is a conjunction whose conjuncts are interpreted constraints or
     *  predicate applications. A predicate under a negation or a disjunction is
     *  not Horn, and that is the check worth making: such a formula is legal
     *  SMT-LIB and its translation would be a fine SMT script for a problem no
     *  CHC solver was asked. */
    bool collectBody(const H::ExprPtr& e, const std::unordered_set<std::string>& preds,
                     Clause& out, Uir::Diagnostics& diags) {
        if (!e) { return true; }
        if (e->kind == H::ExprKind::OP && e->op == H::Op::AND) {
            for (const H::ExprPtr& a : e->args) {
                Uir::Diagnostics atom_diags;
                if (predicateAtom(a, preds, false, "body", atom_diags)) {
                    out.body_predicates.push_back(a);
                    continue;
                }
                if (atom_diags.hasErrors()) {
                    diags.merge(atom_diags);
                    return false;
                }
                if (mentionsPredicate(a, preds)) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "an uninterpreted predicate appears inside a body "
                                "connective rather than as a top-level conjunction atom",
                                a->loc);
                    return false;
                }
            }
            return true;
        }
        if (predicateAtom(e, preds, false, "body", diags)) {
            out.body_predicates.push_back(e);
            return true;
        }
        if (diags.hasErrors()) { return false; }
        if (mentionsPredicate(e, preds)) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "an uninterpreted predicate appears inside a body connective "
                        "other than a conjunction (under a negation or a disjunction, "
                        "say); that is not a Horn clause",
                        e->loc);
            return false;
        }
        return true;                 // an ordinary interpreted constraint
    }

    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkChcLanguage() { return std::make_shared<ChcLanguage>(); }

} // namespace SOMTParser::Lang
