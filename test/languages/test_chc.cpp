// The CHC-COMP frontend, and the obligations docs/languages/chc-comp.md wrote
// down before it existed.
//
// CHC-COMP files ARE SMT-LIB 2, so this frontend borrows the engine's parser
// and lifts with Lower::ParserToHir rather than carrying a reader. What makes
// it a language rather than an alias is validation against the official 2023
// command grammar and Horn normal form, and that is most of what this file tests.
//
// The obligations, and why each is a wrong answer rather than a missing
// feature:
//
//   * **The head must be one predicate application or `false`.** A disjunctive
//     head is legal SMT-LIB and not Horn. Accepting it produces a perfectly
//     good SMT script for a problem no CHC solver was asked, and the row lands
//     in a CHC results table looking comparable.
//   * **A predicate may not appear under a negation or a disjunction in the
//     body.** Same shape, same consequence.
//   * **There must be a query.** Rules alone are trivially satisfiable --
//     interpret every predicate as universally true and every implication
//     holds -- so the answer says nothing about the program. This is the case
//     §4.1 describes, and it is a property of a file with no query rather than
//     of the translation.
//   * **There must be a predicate to solve for.** Otherwise the file is a plain
//     SMT-LIB query wearing a CHC hat.
//
// And one obligation about what must SURVIVE: the universal quantifier is the
// semantics, not decoration. A clause read as ground says "for one state"
// instead of "for all states", which is a different and much weaker claim, so
// the test asserts the `forall` is still there after the round trip.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "chc";
    return translate(u, opts);
}

Translation runStr(const std::string& src, const std::string& name) {
    Lang::SourceUnit u;
    u.main_path = name;
    u.display_name = name;
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "chc";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= CHC-COMP frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* chc = Lang::LanguageRegistry::instance().byId("chc");
    assert(chc != nullptr);
    assert(chc->extensions().size() == 1 && chc->extensions()[0] == ".smt2");

    // ---- Detection: the extension cannot decide, so sniff() must. ----------
    {
        // .smt2 is shared with the SMT-LIB baseline. `(set-logic HORN)` is the
        // only thing in a file's first bytes that tells them apart, which is
        // why sniff() is not optional here.
        assert(chc->sniff("(set-logic HORN)\n(declare-fun P (Int) Bool)") > 0.5);
        assert(chc->sniff("(set-logic QF_LIA)\n(declare-fun x () Int)") == 0.0);
    }

    // ---- The clause set survives, quantifiers and all. ---------------------
    {
        const Translation t = runFile("languages/chc/instances/ok/loop.smt2");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The predicate is an uninterpreted relation, declared as such.
        assert(has(smt, "(declare-fun Inv (Int Int) Bool)"));
        // Three clauses in, three assertions out: a clause silently dropped
        // would leave a strictly weaker problem that still translates.
        assert(t.report().stats().num_constraints == 3);
        // The universal quantifier is the semantics. Reading a clause as ground
        // turns "for all states" into "for one state".
        assert(has(smt, "forall"));
        // The query survives as an implication to false rather than being
        // dropped for looking vacuous.
        assert(has(smt, "false"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A non-nullary fact introduces a variable in the interpreted body and
        // uses that same variable in the head; ground predicate terms are not
        // part of the CHC-COMP normal form.
        const Translation t = runFile("languages/chc/instances/ok/fact.smt2");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 3);
    }
    {
        const Translation t = runFile("languages/chc/instances/ok/nullary.smt2");
        assert(t.ok());
        assert(has(t.toSmt2(), "(declare-fun Ready () Bool)"));

        const auto& first = t.semantics().stages().front();
        assert(first.id == "chc-to-typed-relational-core-v2");
        assert(first.decision.source == Sem::DecisionKind::HORN_SATISFIABILITY);
        bool projects_relation = false;
        for (const Sem::Observable& observable : first.projection.observables) {
            if (observable.source_name == "Ready"
                && observable.target_name == "Ready") {
                projects_relation = true;
            }
        }
        assert(projects_relation);
    }
    {
        // ADT declarations and constructor/selector terms are interpreted
        // background theory symbols. Only Reach is synthesized as a relation.
        const Translation t = runFile("languages/chc/instances/ok/datatype.smt2");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-datatypes"));
        assert(has(smt, "(declare-fun Reach (List) Bool)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A quoted simple constructor name and its unquoted tester spelling
        // are the same SMT-LIB symbol. This pattern occurs in the official
        // Tricera ADT-array track (`|O_node|` declared, `O_node` tested).
        const Translation t = runStr(
            "(set-logic HORN)\n"
            "(declare-datatypes ((|HeapObject| 0)) "
            "(((|O_node| (|getnode| Int)) (|defObj|))))\n"
            "(declare-fun Reach (|HeapObject|) Bool)\n"
            "(assert (forall ((x |HeapObject|)) "
            "(=> (and ((_ is O_node) x) (= x (O_node (getnode x)))) (Reach x))))\n"
            "(assert (forall ((x |HeapObject|)) "
            "(=> (and ((_ is |O_node|) x) (= x (|O_node| (|getnode| x)))) (Reach x))))\n"
            "(assert (forall ((x |HeapObject|)) (=> (= x |defObj|) (Reach x))))\n"
            "(assert (forall ((x |HeapObject|)) (=> (Reach x) false)))\n"
            "(check-sat)\n", "quoted-datatype-members.smt2");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "is |O_node|"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The official BV corpus contains Z3's explicit hardware-division
        // aliases. SMT-LIB 2.6 assigns the canonical public operators the same
        // divisor-zero values, so the spelling change is exact and recorded.
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P ((_ BitVec 8)) Bool)\n"
            "(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) "
            "(=> (= (bvsrem_i x y) x) (P x))))\n"
            "(assert (forall ((x (_ BitVec 8))) (=> (P x) false)))\n"
            "(check-sat)\n", "z3-bv-alias.smt2");
        assert(t.ok());
        assert(!has(t.toSmt2(), "bvsrem_i"));
        assert(has(t.toSmt2(), "bvsrem"));
        bool recorded = false;
        for (const EncodingChoice& choice : t.report().choices()) {
            if (choice.unified_op == "z3-bv-hardware-division") {
                recorded = choice.fidelity.sound && choice.fidelity.complete && choice.fidelity.preserves_optimum && choice.fidelity.bounds.empty() && choice.fidelity.count_status == CountStatus::UNASSESSED;
            }
        }
        assert(recorded);
    }
    {
        // "Non-linear" in the CHC sense: two predicate applications in one
        // body. Unrelated to non-linear arithmetic, and §1 warns that
        // conflating the two is hard to spot -- so it is asserted to translate
        // rather than being refused as if it were the other kind.
        const Translation t = runFile("languages/chc/instances/ok/nonlinear.smt2");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(declare-fun A (Int) Bool)"));
        assert(has(smt, "(declare-fun B (Int) Bool)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- The verdict reading is on the record. -----------------------------
    {
        // CHC `sat` means a solution exists and the program is SAFE, which is
        // the opposite of the intuition `unsat` = "no bug found". A reader of
        // the experiment database has no other way to know.
        const Translation t = runFile("languages/chc/instances/ok/loop.smt2");
        assert(t.ok());
        const EncodingChoice* c = nullptr;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "horn-clauses") { c = &e; }
        }
        assert(c != nullptr);
        assert(has(c->rationale, "SAFE"));
        // exact(), and deliberately: SMT satisfiability already quantifies the
        // uninterpreted predicates existentially, so the translated question is
        // the competition's. Marking it approximate would put a false
        // degradation in the column the results tables stratify on.
        assert(c->fidelity.sound && c->fidelity.complete && c->fidelity.preserves_optimum && c->fidelity.bounds.empty() && c->fidelity.count_status == CountStatus::UNASSESSED);
        assert(t.report().fidelity().sound && t.report().fidelity().complete && t.report().fidelity().preserves_optimum && t.report().fidelity().bounds.empty() && t.report().fidelity().count_status == CountStatus::UNASSESSED);
    }

    // ---- Non-Horn shapes are refused BY NAME. ------------------------------
    {
        const Translation t = runFile("languages/chc/instances/reject/disjunctive_head.smt2");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "head"));
    }
    {
        const Translation t = runFile("languages/chc/instances/reject/negated_predicate.smt2");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "conjunction"));
    }
    {
        const Translation t = runFile("languages/chc/instances/reject/no_query.smt2");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        // The message says WHY, so the refusal is not mistaken for pedantry:
        // the file is satisfiable for a reason unrelated to the program.
        assert(has(t.diagnostics().all()[0].message, "nothing about the program"));
    }
    {
        const Translation t = runFile("languages/chc/instances/reject/no_predicate.smt2");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "return Bool"));
    }
    {
        // An existentially quantified assertion is not a clause. Checked
        // separately from the head and body shapes because it fails earlier,
        // before either is looked at.
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (exists ((x Int)) (P x)))\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(check-sat)\n", "e.smt2");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "universally quantified"));
    }
    {
        // A ground argument is a legal SMT term but not a CHC-COMP u_pred_atom:
        // predicate arguments in the normal form are quantified variables.
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (P 0))\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(check-sat)\n", "ground.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "quantified variables"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (=> (= x 0) (P (+ x 1)))))\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(check-sat)\n", "term-head.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "only to quantified variables"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int Int) Bool)\n"
            "(assert (forall ((x Int)) (P x x)))\n"
            "(assert (forall ((x Int)) (=> (= x 0) false)))\n"
            "(check-sat)\n", "duplicate-head.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "distinct variables"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (=> (P (+ x 1)) (P x))))\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(check-sat)\n", "term-body.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "only to quantified variables"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(assert (forall ((x Int)) (=> (= x 0) false)))\n"
            "(check-sat)\n", "two-query.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "exactly one"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(assert (forall ((x Int)) (=> (= x 0) (P x))))\n"
            "(check-sat)\n", "query-order.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "final assertion"));
    }
    {
        const Translation t = runStr(
            "(set-logic QF_LIA)\n(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(check-sat)\n", "wrong-logic.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "set-logic HORN"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-const P Bool)\n"
            "(assert (forall ((x Int)) (=> P false)))\n"
            "(check-sat)\n", "declare-const.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "declare-const"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n",
            "missing-check.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "check-sat"));
    }
    {
        const Translation t = runStr(
            "(set-logic HORN)\n(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (=> (P x) false)))\n"
            "(check-sat)\n(get-model)\n", "get-model.smt2");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "get-model"));
    }
    {
        const Translation t = runFile("languages/chc/instances/nosuch.smt2");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- The shape every CHC-COMP benchmark is written in. -----------------
    {
        // Predicates declared as QUOTED symbols and applied unquoted:
        //
        //     (declare-fun |inv| ( Int Int ) Bool)   ...   (inv B A)
        //
        // SMT-LIB 2.6 §3.1 makes those the same symbol -- enclosing a simple
        // symbol in vertical bars does not produce a new one -- and the engine
        // treated them as two, so the ENTIRE competition corpus read as
        // `Unknown or unexpected symbol "inv"`. On a sample of eight CHC-COMP
        // 2024 LIA-Lin instances this frontend went from 0 to 8.
        //
        // The competition files are not vendored (their redistribution terms
        // were not established), so the construct is reproduced in a fixture
        // this project owns.
        Lang::SourceUnit u;
        u.main_path = "languages/chc/instances/ok/quoted_predicate.smt2";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "chc";
        const Translation t = translate(u, opts);
        assert(t.ok());

        const std::string smt = t.toSmt2();
        // One predicate, not two: if the spellings were distinct symbols the
        // three clauses would mention two unrelated `inv`s and the problem
        // would be trivially satisfiable.
        std::size_t decls = 0;
        for (std::size_t i = smt.find("(declare-fun "); i != std::string::npos;
             i = smt.find("(declare-fun ", i + 1)) {
            ++decls;
        }
        assert(decls == 1);
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }

    // ---- Coverage is honest. -----------------------------------------------
    {
        const Lang::OpCoverage& cov = chc->coverage();
        assert(cov.supported == cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    std::cout << "All CHC-COMP tests passed." << std::endl;
    return 0;
}
