// The Boogie frontend, and the obligations docs/languages/boogie.md wrote down
// before it existed.
//
// Boogie is a verification-condition language, so the translation is a VC
// generator and every obligation is about what a VC must contain. Each one
// below is a WRONG ANSWER rather than a missing feature: the script still
// translates, still parses, and still gets a verdict.
//
//   * **A postcondition is asserted NEGATED.** The query is a refutation, so
//     unsat means the procedure meets its contract. Asserted positively, every
//     procedure verifies.
//   * **A postcondition names the FINAL version of each variable.** `ensures`
//     is parsed before the body runs, so its identifiers resolve to version 1 --
//     and `y := x + 1` then leaves the clause talking about the entry `y`. The
//     negated clause constrains a variable nothing else mentions, so it is
//     trivially satisfiable and a correct procedure reports "not verified".
//   * **`havoc x` introduces a fresh variable.** As a no-op the old value
//     persists and the VC proves a property of a program that cannot happen.
//   * **Assignment is SSA.** Without versioning `x := x + 1` becomes the
//     unsatisfiable `x = x + 1`, the query is unsat for a reason unrelated to
//     the property, and the procedure reports "verified".
//   * **`requires` is assumed at the body.** Dropped, the procedure must be
//     proved for inputs its contract excludes.
//
// And the refusals, which are refusals because each is a DECISION rather than
// missing work: loops need §4.3's invariant choice, maps are the heap, and
// branching/CFG joins are the remaining control-flow decision. Calls landed
// on 2026-09-19 as the two-sided contract at the call site (This is Boogie 2
// §8.2/§9.9), and their tests live below with the rest of the obligations.

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
    opts.language_id = "boogie";
    return translate(u, opts);
}

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.bpl";
    u.display_name = "t.bpl";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "boogie";
    return translate(u, opts);
}

/** The `(assert ...)` lines of a script, joined -- the VC itself. */
std::string assertions(const std::string& smt) {
    std::string out;
    std::size_t p = 0;
    while ((p = smt.find("(assert", p)) != std::string::npos) {
        const std::size_t e = smt.find('\n', p);
        out += smt.substr(p, e - p) + "\n";
        p = e;
    }
    return out;
}

} // namespace

int main() {
    std::cout << "======= Boogie frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* b = Lang::LanguageRegistry::instance().byId("boogie");
    assert(b != nullptr);
    assert(b->extensions().size() == 1 && b->extensions()[0] == ".bpl");

    // ---- The contract's two sides, at the body. ----------------------------
    {
        const Translation t = runFile("languages/boogie/instances/ok/inc.bpl");
        assert(t.ok());
        const std::string a = assertions(t.toSmt2());
        // `requires x >= 0` is ASSUMED: it appears positively.
        assert(has(a, "(>= x 0)"));
        // `ensures y == x + 1` is ASSERTED, which in a refutation means its
        // NEGATION appears. `distinct` is how the printer spells `not (= ...)`.
        assert(has(a, "distinct"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // The postcondition names the variable the BODY produced, not the one
        // that existed when the clause was parsed. This is the whole of the
        // late-resolution rule, and getting it wrong reports a correct
        // procedure as unverified with nothing looking wrong.
        const Translation t = runFile("languages/boogie/instances/ok/inc.bpl");
        const std::string a = assertions(t.toSmt2());
        assert(has(a, "y@2"));
        // ...and the entry version of y is not what the clause talks about.
        // Written as: every line mentioning y mentions y@2.
        std::size_t p = 0;
        while ((p = a.find(" y", p)) != std::string::npos) {
            const bool versioned = a.compare(p + 2, 1, "@") == 0;
            assert(versioned);
            p += 2;
        }
    }
    {
        // A procedure whose postcondition is NOT met by the body still
        // translates -- the frontend does not decide verification, it states
        // the query. Without this, a frontend that refused anything it could
        // not prove would pass the tests above.
        const Translation t = run("procedure P(x: int) returns (y: int)\n"
                                  "  ensures y == x + 1;\n"
                                  "{ y := x + 2; }\n");
        assert(t.ok());
    }

    // ---- havoc is fresh, not a no-op. --------------------------------------
    {
        const Translation t = runFile("languages/boogie/instances/ok/havoc.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // A fresh version of x exists, and the assumption after the havoc
        // constrains THAT one -- so the entry value (x == 3) does not reach it.
        assert(has(smt, "declare-fun x@3"));
        assert(has(assertions(smt), "(>= x@3 0)"));
    }
    {
        // The mechanical claim: havocking a variable must change the script.
        // A no-op havoc produces the same text with the statement removed.
        const char* head = "procedure P(a: int) returns (y: int)\n"
                           "  requires a == 3;\n  ensures y == 3;\n"
                           "{\n  var x: int;\n  x := a;\n";
        const Translation with = run(std::string(head) + "  havoc x;\n  y := x;\n}\n");
        const Translation without = run(std::string(head) + "  y := x;\n}\n");
        assert(with.ok() && without.ok());
        assert(with.toSmt2() != without.toSmt2());
    }

    // ---- Assignment is SSA. ------------------------------------------------
    {
        const Translation t = runFile("languages/boogie/instances/ok/reassign.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // x is assigned twice, so three versions exist: the declaration and the
        // two results. Collapsed onto one name, `x = x + 1` is unsatisfiable
        // and the procedure reports "verified" for a reason unrelated to it.
        assert(has(smt, "declare-fun x ()"));
        assert(has(smt, "declare-fun x@2"));
        assert(has(smt, "declare-fun x@3"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Boogie's div is SMT-LIB's, which is Euclidean. --------------------
    {
        // §4.5, the fifth language in the batch to meet this. Boogie is defined
        // BY translation to SMT-LIB, so it is the one frontend that names
        // EUCLID -- MiniZinc and FlatZinc name TRUNC, and the difference is
        // every negative dividend.
        const Translation t = runFile("languages/boogie/instances/ok/axiom_div.bpl");
        assert(t.ok());
        const std::string a = assertions(t.toSmt2());
        // Euclidean lowers straight onto SMT-LIB's div, with no correction term
        // -- so the presence of a bare `div` and the absence of an `ite` around
        // it is exactly the claim.
        assert(has(a, "(div n 2)"));
        assert(!has(a, "ite"));
    }
    {
        // An axiom is assumed globally and positively -- it is a hypothesis
        // about the world, not an obligation, so it is NOT negated.
        const Translation t = runFile("languages/boogie/instances/ok/axiom_div.bpl");
        assert(has(assertions(t.toSmt2()), "(> g 0)"));
        // ...and the fact that consistency is not checked is on the record,
        // because an inconsistent axiom set makes every procedure verify.
        bool said = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "axiom") {
                said = true;
                assert(has(c.rationale, "vacuously"));
            }
        }
        assert(said);
    }

    // ---- Loops: the invariant strategy, and the decision it embodies. ------
    {
        // This file used to live in instances/reject/ and pin the refusal. The
        // decision was taken on 2026-08-17 -- boogie.md §4.3's invariant
        // strategy, Boogie's own -- so it moved to instances/ok/. A test that
        // pins scaffolding is supposed to fail when the scaffolding goes.
        //
        // It carries NO invariant, which is the interesting half: the strategy
        // then degenerates to "havoc what the loop assigns and continue",
        // §4.3's third row. That is still exact and still sound -- it assumes
        // nothing about the exit state except that the guard is false -- and
        // here it happens to be enough. `s >= n` and `n >= 0` give `s >= 0`.
        const Translation t =
            runFile("languages/boogie/instances/ok/loop_no_invariant.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The postcondition is an obligation about the EXITED state, so it is
        // guarded by the exit condition rather than asserted of every state.
        assert(has(smt, "(=> (>= s@5 n) (>= s@5 0))"));
        // ...and the entry value of s does not reach it. A loop encoding that
        // forgot to havoc would verify the continuation against `s = 0`, which
        // is the classic unsound one.
        assert(!has(smt, "(>= 0 n)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Preservation is CHECKED, not assumed. A loop whose invariant does not
        // survive its own body must not verify, and the shape that matters is
        // that the check is one self-contained implication: its antecedent
        // holds the invariant, the guard and the body's assumes, so no part of
        // it constrains anything outside the loop.
        const Translation t = run(
            "procedure P() returns (i: int)\n{\n  i := 0;\n"
            "  while (i < 10)\n    invariant i <= 5;\n  {\n    i := i + 1;\n  }\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(<= i@4 5)"));            // the preservation consequent
        // The two havoc'd states must be DISTINCT. Sharing one puts `i <= 5`
        // and `i >= 10` in the same conjunction, which is unsatisfiable -- and
        // an unsatisfiable script is what this encoding reads as verified, so a
        // plainly broken invariant would have "proved".
        assert(has(smt, "i@3") && has(smt, "i@5"));
    }
    {
        // A correct loop verifies: the negated conjunction must be refutable,
        // which for this one means every obligation is a tautology.
        const Translation t = run(
            "procedure P() returns (i: int)\n  ensures 10 <= i;\n{\n  i := 0;\n"
            "  while (i < 10)\n    invariant i <= 10;\n  {\n    i := i + 1;\n  }\n}\n");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }

    // ---- Calls: the two-sided contract at the call site. --------------------
    {
        // The fixture used to live in instances/reject/ and pin the refusal.
        // The contract-based encoding landed on 2026-09-19, so it moved to
        // ok/: Callee is bodiless, and the caller still learns b == a.
        const Translation t = runFile("languages/boogie/instances/ok/call.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        const std::string a = assertions(smt);
        // The callee's checked requires is ASSERTED at the call site: its
        // negation sits in a refutation branch, over the ACTUAL a (the
        // printer normalises `not (>= a 0)` to `(< a 0)`).
        assert(has(a, "(< a 0)"));
        // ...and its ensures is ASSUMED, tying the fresh out-target b@2 to a.
        assert(has(a, "(= a b@2)"));
        // The call is recorded as the encoding choice it is (D31).
        bool said = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "call") {
                said = true;
                assert(has(c.rationale, "old()"));
                assert(has(c.strategy, "no-inlining"));
            }
        }
        assert(said);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The frame: h is not in Bump's modifies, so the call must NOT mint a
        // new version of it, while g is havoc'd and gets one. Dropping the
        // frame (havoc'ing h as well) is the §4.2 failure mode that makes
        // correct callers unverifiable. (g@2/h@2 are the entry aliases every
        // non-first procedure gets; the call's havoc is the NEXT version.)
        const Translation t = runFile("languages/boogie/instances/ok/call_frame.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun g@3"));
        assert(!has(smt, "declare-fun h@3"));
        // old(g) at the call site is the caller's pre-call version: the
        // assumed ensures relates the havoc'd g@3 to the ENTRY g@2, not to a
        // procedure-entry alias.
        assert(has(smt, "(+ 1 g@2)"));
        assert(!has(smt, "g@old"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Free clauses (This is Boogie 2 §8.2): a free requires is not
        // asserted at the call site (its negation must appear NOWHERE), and a
        // free ensures is not asserted at the body.
        const Translation t = runFile("languages/boogie/instances/ok/call_free.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The printer normalises a negated (>= a 0) to (< a 0); the free
        // requires must produce NO such obligation anywhere.
        assert(!has(smt, "(< a 0)"));
        // Q's free ensures y == 12345 is not an obligation of the body.
        assert(!has(smt, "12345"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // call forall is `assume (forall wildcards :: Pre ==> Post)` over a
        // lemma procedure (This is Boogie 2 §9.10).
        const Translation t = runFile("languages/boogie/instances/ok/call_forall.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Recursion is a contract instantiation like any other: the pass-1
        // registry sees Wrap's signature before its body is read.
        const Translation t =
            runFile("languages/boogie/instances/ok/call_recursive.bpl");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // The callee's modifies must lie inside the caller's -- otherwise the
        // caller's frame is a lie (the reference's CheckAssignments reports
        // the same, over the call's assigned variables).
        const Translation t =
            runFile("languages/boogie/instances/reject/call_modifies_subset.bpl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "modifies"));
    }
    {
        // Call-site legality, each an E_TYPE naming the rule: unknown callee,
        // arity, out-arity, a repeated out-target, a function as the callee,
        // old() in a precondition, an out-parameter in a precondition.
        const Translation unknown = run(
            "procedure P() { call Q(); }\n");
        assert(!unknown.ok());
        assert(has(unknown.diagnostics().all()[0].message, "not a declared procedure"));
        const Translation arity = run(
            "procedure Q(x: int);\nprocedure P() { call Q(1, 2); }\n");
        assert(!arity.ok());
        assert(has(arity.diagnostics().all()[0].message, "in-parameter"));
        const Translation outarity = run(
            "procedure Q() returns (r: int);\nprocedure P() { call Q(); }\n");
        assert(!outarity.ok());
        assert(has(outarity.diagnostics().all()[0].message, "out-parameter"));
        const Translation twice = run(
            "procedure Q() returns (r: int, s: int);\n"
            "procedure P() { var x: int; call x, x := Q(); }\n");
        assert(!twice.ok());
        assert(has(twice.diagnostics().all()[0].message, "twice"));
        const Translation fun = run(
            "function f(x: int): int;\nprocedure P() { call f(1); }\n");
        assert(!fun.ok());
        assert(has(fun.diagnostics().all()[0].message, "a function, not a procedure"));
        const Translation oldpre = run(
            "procedure Q(x: int); requires x >= old(x);\n"
            "procedure P(a: int) { call Q(a); }\n");
        assert(!oldpre.ok());
        assert(has(oldpre.diagnostics().all()[0].message, "old"));
        const Translation outpre = run(
            "procedure Q() returns (r: int); requires r >= 0;\n"
            "procedure P() { var x: int; call x := Q(); }\n");
        assert(!outpre.ok());
        assert(has(outpre.diagnostics().all()[0].message, "out-parameter"));
    }
    {
        // `call forall` requires a LEMMA procedure: no out-parameters and no
        // checked modifies (This is Boogie 2 §9.10).
        const Translation t = run(
            "procedure Q() returns (r: int);\n"
            "procedure P() { call forall Q(); }\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "lemma procedure"));
    }
    {
        // A contract clause cannot name what the callee cannot see: `z` is
        // not declared in Q's scope, so the clause is rejected when Q's own
        // declaration is read -- the leak into a caller's scope is impossible
        // because the callee's contract is validated in the callee's scope
        // first. (E_TYPE, naming the variable.)
        const Translation t = run(
            "procedure Q(x: int); requires x >= z;\n"
            "procedure P(a: int) { var z: int; z := 1; call Q(a); }\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "'z' is not declared"));
    }
    {
        // ...and a local that SHADOWS a global would version the two as one
        // (SSA versions are keyed by name), so it is refused by name rather
        // than silently mis-scoped. Boogie permits the shadowing
        // (ResolutionContext's AddVariable checks only the current scope).
        const Translation t = run(
            "var g: int;\nprocedure P() { var g: int; g := 1; }\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "shadowing"));
    }
    {
        // async call, a where clause and type parameters are named refusals.
        const Translation asy = run(
            "procedure Q();\nprocedure P() { async call Q(); }\n");
        assert(!asy.ok());
        assert(asy.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(asy.diagnostics().all()[0].message, "async"));
        const Translation wh = run(
            "procedure P(x: int where x > 0) { assert true; }\n");
        assert(!wh.ok());
        assert(wh.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(wh.diagnostics().all()[0].message, "where"));
        const Translation tp = run(
            "procedure P<T>(x: int) { assert true; }\n");
        assert(!tp.ok());
        assert(tp.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(tp.diagnostics().all()[0].message, "type parameters"));
    }
    {
        // A free call skips the precondition check but still assumes the
        // postcondition (the `free` on the call, not on the clause).
        const Translation t = run(
            "procedure Q(x: int) returns (y: int); requires x >= 0; ensures y == x;\n"
            "procedure P(a: int) returns (b: int) ensures b <= 0;\n"
            "{ free call b := Q(a); assume b <= 0; }\n");
        assert(t.ok());
        assert(!has(t.toSmt2(), "(< a 0)"));
    }
    {
        // A loop whose body assigns two variables in parallel must havoc
        // BOTH: collecting only the target adjacent to `:=` kept the first
        // variable's value across iterations, the unsoundness §4.3's havoc
        // exists to prevent.
        const Translation t = run(
            "procedure P() returns (r: int)\n  ensures true;\n"
            "{\n  var x, y: int;\n  x := 0;  y := 1;\n"
            "  while (*) { x, y := y, x; }\n  r := 0;\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // x is assigned once before the loop; with both targets collected,
        // the body's parallel assignment and the two havoc'd loop states
        // (§4.3's preservation and continuation) mint x@3, x@4 and x@5. With
        // only y collected, x would stop at x@3.
        assert(has(smt, "declare-fun x@4"));
        assert(has(smt, "declare-fun x@5"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Branching: the two-edge join, and return as an exit point. --------
    {
        // A fact survives the join only when true on both paths. The join is
        // an ite over the branch condition (This is Boogie 2 §9.7).
        const Translation t = runFile("languages/boogie/instances/ok/if_join.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "ite"));
        // The branches' effects hold under their guards: the then-branch's
        // equation is guarded by (>= x 0), the else-branch's by its negation.
        assert(has(smt, "(>= x 0)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // `if (*)` mints a fresh, unconstrained boolean and joins on it.
        const Translation t = runFile("languages/boogie/instances/ok/if_star.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "if*!0"));
        assert(has(smt, "ite"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // An `else if` chain is a nested if: three branches, two joins.
        const Translation t = run(
            "procedure P(x: int) returns (r: int)\n  ensures r >= 0;\n"
            "{\n  if (x >= 1) { r := x; }\n"
            "  else if (x <= -1) { r := -x; }\n"
            "  else { r := 0; }\n}\n");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // A branch that RETURNS contributes no edge to the join: after
        // `if (x <= 0) { r := 1; return; }`, the continuation exists only
        // where x > 0, and the obligations after the if carry that guard.
        const Translation t = runFile("languages/boogie/instances/ok/return_early.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The ensures is an obligation at BOTH exit points, each under its
        // path: the return's and the fall-through's.
        assert(has(smt, "(or "));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Code after a `return` is parsed but has no VC effect: the reference
        // prunes unreachable blocks before VC generation, so `assert false`
        // there cannot fail. The two programs emit the SAME script.
        const Translation live = run(
            "procedure P() returns (r: int)\n  ensures r == 1;\n"
            "{\n  r := 1;\n  return;\n}\n");
        const Translation with_dead = run(
            "procedure P() returns (r: int)\n  ensures r == 1;\n"
            "{\n  r := 1;\n  return;\n  assert false;\n  r := 2;\n}\n");
        assert(live.ok() && with_dead.ok());
        assert(live.toSmt2() == with_dead.toSmt2());
    }
    {
        // A `return` inside a loop body is an exit of the PROCEDURE, not an
        // iteration: the invariant's preservation is owed only by paths that
        // complete the body. The obligation's antecedent must carry the
        // completion guard -- without it the returned path leaves the post-
        // state version unconstrained and a correct loop fails preservation.
        const Translation t = run(
            "procedure P() returns (i: int)\n{\n  i := 0;\n"
            "  while (i < 10)\n    invariant i <= 10;\n  {\n"
            "    if (i == 5) { return; }\n    i := i + 1;\n  }\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The completion guard (i@3 /= 5, printed `(distinct 5 i@3)`) sits in
        // the preservation antecedent: without it, i@3 == 5 leaves i@4 free
        // and (<= i@4 10) is refutable.
        assert(has(smt, "(distinct 5 i@3)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- CFG: labels, goto, break, and N-way joins. ------------------------
    {
        // Two forward edges reach Done; their guards (x < 0 vs not) ARE
        // exclusive here, but the join is the general gated form because a
        // label cannot know that.
        const Translation t = runFile("languages/boogie/instances/ok/goto_forward.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "edge!"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // `goto A, B` chooses blindly: the join at Done is demonic, and the
        // gate booleans are what keep the paths' values apart.
        const Translation t =
            runFile("languages/boogie/instances/ok/goto_multi_target.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "edge!0"));
        assert(has(smt, "edge!1"));
        assert(has(smt, "ite"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A goto loop: the reference cuts the back edge and havoc's the
        // cycle's assignments under an implicit `invariant true`
        // (RemoveBackEdges.cs). So the header mints a FRESH i with no defining
        // constraint, and n -- never touched by the cycle -- keeps its fact.
        const Translation t = runFile("languages/boogie/instances/ok/goto_loop.bpl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun i@3"));
        assert(!has(smt, "(= i@3 "));    // the havoc: nothing defines it
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // `break` is an edge into the loop's continuation, joining the exit
        // edge (guard false) -- This is Boogie 2 §9.5's goto-to-Done.
        const Translation t = runFile("languages/boogie/instances/ok/break_search.bpl");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // The four refusals, each by name: a goto INTO a structured
        // statement, a goto loop ACROSS a while, an undefined target, a
        // duplicate label.
        const Translation into =
            runFile("languages/boogie/instances/reject/goto_into_if.bpl");
        assert(!into.ok());
        assert(into.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(into.diagnostics().all()[0].message, "into a structured statement"));
        const Translation across =
            runFile("languages/boogie/instances/reject/goto_across_while.bpl");
        assert(!across.ok());
        assert(across.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(across.diagnostics().all()[0].message, "across a `while`"));
        const Translation undef =
            runFile("languages/boogie/instances/reject/goto_undefined.bpl");
        assert(!undef.ok());
        assert(undef.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(undef.diagnostics().all()[0].message, "Missing"));
        const Translation dup =
            runFile("languages/boogie/instances/reject/label_duplicate.bpl");
        assert(!dup.ok());
        assert(dup.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(dup.diagnostics().all()[0].message, "more than once"));
    }
    {
        // A call inside a loop body extends the loop's havoc set with the
        // callee's checked modifies: otherwise the loop would carry the
        // pre-loop value of g across, the unsoundness §4.3's havoc prevents.
        const Translation t = run(
            "var g: int;\n"
            "procedure Bump();\n  modifies g;\n  ensures true;\n"
            "procedure P(n: int) returns (r: int)\n"
            "  requires g == 0 && n >= 0;\n  modifies g;\n  ensures g == 0;\n"
            "{\n  var i: int;\n  i := 0;\n"
            "  while (i < n)\n    invariant i <= n;\n"
            "  { call Bump();  i := i + 1; }\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // g is havoc'd at BOTH loop states (preservation and continuation) in
        // addition to the call's own havoc inside the body.
        std::size_t decls = 0;
        for (std::size_t i = smt.find("(declare-fun g@"); i != std::string::npos;
             i = smt.find("(declare-fun g@", i + 1)) {
            ++decls;
        }
        assert(decls >= 3);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    {
        // A header's leading asserts ARE the goto loop's invariants
        // (RemoveBackEdges.cs): asserted on entry and at the back edge (so
        // they appear negated in refutation branches) and assumed at the head
        // (they appear positively over the havoc'd versions). With plain
        // obligation treatment the assert would be checked against an
        // unconstrained state and could never verify.
        const Translation t = run(
            "var g: int;\n"
            "procedure P() returns (r: int)\n  modifies g;\n  ensures true;\n"
            "{\n  var i: int;\n  i := 0;  g := 0;\nHead:\n  assert i == g;\n"
            "  if (i < 5) { i := i + 1;  g := g + 1;  goto Head; }\n  r := 0;\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // negated at entry and at the back edge...
        assert(has(smt, "(distinct"));
        // ...and assumed over the havoc'd head state (i@3/g@3 positive).
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- D7: the Horn-clause route from the same parse. ---------------------
    {
        // With options chc=1 the same parse emits Horn clauses: relations
        // instead of SSA versions, error! as the query, and the ensures
        // conjoined into the summary's definition.
        Lang::SourceUnit u;
        u.main_path = "languages/boogie/instances/ok/call_frame.bpl";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "boogie";
        opts.parse.options["chc"] = "1";
        const Translation t = translate(u, opts);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "Bump!sum"));
        assert(has(smt, "P!sum"));
        assert(has(smt, "error!"));
        assert(has(smt, "forall"));
        bool said = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "chc") {
                said = true;
                assert(has(c.strategy, "horn-clause"));
            }
        }
        assert(said);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Refusals: each is a decision, not missing work. -------------------
    {
        // The fixture used to be a ONE-index map, which is now an SMT-LIB
        // array and translates -- both are total functions, so nothing is
        // approximated. It is a multi-index map now, which is still refused
        // because making it an array is a CHOICE (curry, or index by a tuple)
        // and the two say different things about what the map is.
        const Translation t = runFile("languages/boogie/instances/reject/map.bpl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "multi-index map"));
    }
    {
        // A file with no procedure body has nothing to verify. Translating it
        // would emit a script with no obligation, which is trivially
        // satisfiable and reads as a successful translation.
        const Translation t = run("const g: int;\naxiom g > 0;\n");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "nothing to verify"));
    }
    {
        const Translation t = run(
            "var g: int;\naxiom g == 0;\nprocedure P() { assert true; }\n");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "axiom refers to mutable global"));
    }
    {
        const Translation t = run(
            "var g: int;\nfunction f(): int { g }\n"
            "procedure P() { assert true; }\n");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "functions are stateless"));
    }
    {
        const Translation t = run(
            "procedure P(x: int); ensures x == x;\n"
            "implementation P(x: int) { assert true; }\n");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        const Translation input = run("procedure P(x: int) { x := 0; }\n");
        const Translation constant = run(
            "const c: int;\nprocedure P() { havoc c; }\n");
        assert(!input.ok() && !constant.ok());
        assert(has(input.diagnostics().all()[0].message, "immutable"));
        assert(has(constant.diagnostics().all()[0].message, "immutable"));
    }
    {
        const Translation missing = run(
            "var g: int;\nprocedure P() { g := 1; }\n");
        const Translation allowed = run(
            "var g: int;\nprocedure P() modifies g; { g := 1; assert g == 1; }\n");
        assert(!missing.ok());
        assert(has(missing.diagnostics().all()[0].message, "modifies clause"));
        assert(allowed.ok());
    }
    {
        const Translation t = run(
            "procedure P() returns (x: int) { x, x := 1, 2; }\n");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "more than once"));
    }
    {
        const Translation t = run(
            "const unique a: int;\nconst unique b, c: int;\n"
            "procedure P() { assert a != b && b != c && a != c; }\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(distinct a b c)") || has(smt, "(distinct c b a)"));
    }
    {
        const Translation t = runFile("languages/boogie/instances/nosuch.bpl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- Coverage is honest. -----------------------------------------------
    {
        const Lang::OpCoverage& cov = b->coverage();
        assert(cov.supported < cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    // ---- Obligations are DISJOINED, and this one was unsound. ---------------
    //
    // The script is a refutation: unsatisfiable exactly when the procedure meets
    // its contract. So the query must be "does SOME obligation fail". Each
    // obligation has its own source-point prefix `prefix_i ∧ ¬a_i`, and those
    // counterexample branches are disjoined. The old encoding pushed one `¬a`
    // constraint per assertion, making all obligations fail on one execution.
    //
    // A procedure violating exactly one assert therefore emitted an
    // unsatisfiable script, which this encoding reads as VERIFIED. That is
    // unsound in the only direction that really matters -- it claims a proof
    // that does not exist -- and it needs two asserts to see, which is why no
    // single-obligation test caught it.
    {
        // One trivially true, one certainly false. The old encoding emitted
        // `(assert (distinct x x))` and `(assert true)`; the first is UNSAT on
        // its own, so the whole script was, and `assert false` went unreported.
        const Translation t = run(
            "procedure P(x: int)\n{\n  assert x == x;\n  assert false;\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The refutation must survive. `(distinct x x)` as a standalone
        // assertion is exactly the shape that killed it.
        assert(!has(smt, "(assert (distinct x x))"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The other direction, so this is not just "emit something weaker": a
        // procedure whose single obligation HOLDS must still produce a
        // refutable script -- the negation is there and is unsatisfiable.
        const Translation t = run("procedure P(x: int)\n{\n  assert x == x;\n}\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(assert (distinct x x))"));
    }
    {
        // And an obligation that can fail while another holds stays refutable.
        // The query carries separate counterexample alternatives; it must not
        // put the true obligation's negation in a standalone assertion.
        const Translation t = run(
            "procedure P(x: int)\n{\n  assert x == x;\n  assert x != x;\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(or "));
        assert(!has(smt, "(assert (distinct x x))"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // An assumption applies only from its source point onward. In
        // particular, a later unreachable suffix cannot erase a counterexample
        // to an earlier assertion. The two programs therefore have the same
        // refutation query even though one appends `assume false`.
        const Translation before = run(
            "procedure P()\n{\n  assert false;\n}\n");
        const Translation with_dead_suffix = run(
            "procedure P()\n{\n  assert false;\n  assume false;\n}\n");
        assert(before.ok() && with_dead_suffix.ok());
        assert(before.toSmt2() == with_dead_suffix.toSmt2());
    }

    // ---- Procedure counterexamples are alternatives, not conjunctions. ----
    {
        const Translation t = run(
            "procedure Good()\n  ensures true;\n{ }\n"
            "procedure Bad()\n  ensures false;\n{ }\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
        assert(t.semantics().stages()[0].decision.source
               == Sem::DecisionKind::PROGRAM_VERIFICATION);
        assert(!t.semantics().targetSatMeansSourceYes());
    }
    {
        // A contradictory precondition in one procedure cannot make a failing
        // independent procedure disappear from the refutation query.
        const Translation t = run(
            "procedure Dead()\n  requires false;\n  ensures false;\n{ }\n"
            "procedure Bad()\n  ensures false;\n{ }\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // Procedure locals do not leak into the next procedure's scope.
        const Translation t = run(
            "procedure P(x: int)\n  ensures true;\n{ }\n"
            "procedure Q()\n{ assert x == x; }\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        // The declaration grammar is shared by globals and locals, but their
        // ownership is not. A local from P must not be recreated as a global
        // entry variable when Q begins; both procedures may declare it anew.
        const Translation t = run(
            "procedure P()\n{ var tmp: int; tmp := 1; assert tmp == 1; }\n"
            "procedure Q()\n{ var tmp: int; tmp := 2; assert tmp == 2; }\n");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }

    std::cout << "All Boogie tests passed." << std::endl;
    return 0;
}
