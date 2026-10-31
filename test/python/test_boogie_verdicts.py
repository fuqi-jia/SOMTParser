"""Boogie verdict tests, and the corpus the D7 Horn-clause cross-check reuses.

The C++ tests pin the SHAPE of the verification condition; these pin the
VERDICT, which is what docs/languages/boogie.md §4.2 actually demands: a suite
of programs that all verify tests nothing about soundness, so half of this
corpus MUST FAIL to verify. `verified` means the emitted refutation is unsat;
`fails` means sat -- a counterexample exists (boogie.md §2.4's polarity).

The corpus is a module-level list so the D7 cross-check
(test_boogie_chc_crosscheck.py) runs the Horn route over exactly the same
programs: agreement between the routes is the §4.1 instrument.
"""

import pathlib

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp

ROOT = pathlib.Path(__file__).resolve().parents[2]
OK_DIR = ROOT / "languages" / "boogie" / "instances" / "ok"


def _fixture(name):
    return (OK_DIR / name).read_text()


# (name, source, expected) with expected in {"verified", "fails"}.
VERDICT_CORPUS = [
    # The pre-existing fixtures all verify.
    ("inc", _fixture("inc.bpl"), "verified"),
    ("havoc", _fixture("havoc.bpl"), "verified"),
    ("reassign", _fixture("reassign.bpl"), "verified"),
    ("axiom_div", _fixture("axiom_div.bpl"), "verified"),
    ("loop_no_invariant", _fixture("loop_no_invariant.bpl"), "verified"),
    # Calls: the two-sided contract, the frame, free clauses, call forall,
    # recursion.
    ("call", _fixture("call.bpl"), "verified"),
    ("call_frame", _fixture("call_frame.bpl"), "verified"),
    ("call_free", _fixture("call_free.bpl"), "verified"),
    ("call_forall", _fixture("call_forall.bpl"), "verified"),
    ("call_recursive", _fixture("call_recursive.bpl"), "verified"),
    # §4.2's unsound half-done rows, each a program that must FAIL to verify:
    # a caller that violates the callee's requires (asserted at the call).
    # The ensures is `y >= 0`, which the call alone establishes -- so the
    # requires clause is the ONLY thing that can fail, and dropping the
    # assertion flips the verdict.
    ("call_requires_violated",
     "procedure Callee(x: int) returns (y: int);\n"
     "  requires x >= 0;\n  ensures y >= 0;\n"
     "procedure Caller(a: int) returns (b: int)\n  ensures b >= 0;\n"
     "{ call b := Callee(a); }\n",
     "fails"),
    # a callee that does not establish its ensures (asserted at the body).
    ("callee_breaks_ensures",
     "procedure Q(x: int) returns (y: int)\n  ensures y == x + 1;\n"
     "{ y := x + 2; }\n",
     "fails"),
    # a caller that relies on a MODIFIED global's old value -- provable only
    # if the call forgot to havoc, which is the frame bug this pins.
    ("call_havoc_loses_global",
     "var g: int;\n"
     "procedure Bump();\n  modifies g;\n  ensures true;\n"
     "procedure P() returns (r: int)\n"
     "  requires g == 5;\n  modifies g;\n  ensures r == 5;\n"
     "{ call Bump();  r := g; }\n",
     "fails"),
    # old() at the call site is the call-entry value: g goes 0 -> 1.
    ("call_old_at_entry",
     "var g: int;\n"
     "procedure Bump();\n  modifies g;\n  ensures g == old(g) + 1;\n"
     "procedure P() returns (r: int)\n"
     "  requires g == 0;\n  modifies g;\n  ensures r == 1;\n"
     "{ call Bump();  r := g; }\n",
     "verified"),
    # An assertion that is simply false.
    ("assert_false", "procedure P() { assert false; }\n", "fails"),
    # A loop whose parallel-assignment body must havoc BOTH targets: with x
    # not collected, the body reads the PRE-LOOP x (0), so the preservation
    # check proves the invariant from the entry value -- x is 0, then 1, then
    # 2 in reality, and the invariant breaks on the second iteration. The
    # correct encoding reasons from an arbitrary x and must fail it.
    ("loop_parallel_assign",
     "procedure P() returns (r: int)\n"
     "{\n  var x, y: int;\n  x := 0;  y := 1;\n"
     "  while (*) invariant x <= 1; { x, y := x + 1, x; }\n  r := 0;\n}\n",
     "fails"),
    # A loop with a checked, inductive invariant verifies; the same loop with
    # a broken invariant must fail (the §4.3 two-path encoding's case).
    ("loop_invariant_ok",
     "procedure P() returns (i: int)\n  ensures 10 <= i;\n"
     "{\n  i := 0;\n  while (i < 10)\n    invariant i <= 10;\n"
     "  { i := i + 1; }\n}\n",
     "verified"),
    # Branching: facts known after a join only if true on both paths, if (*)
    # as demonic choice, return as an exit point, dead code after a transfer.
    ("if_join", _fixture("if_join.bpl"), "verified"),
    ("if_star", _fixture("if_star.bpl"), "verified"),
    ("return_early", _fixture("return_early.bpl"), "verified"),
    # The else path gives r = 7 and the then path r = 0, so r >= 5 fails; a
    # join that kept only one path's value would wrongly verify.
    ("if_star_join_lost",
     "procedure P() returns (r: int)\n  ensures r >= 5;\n"
     "{ if (*) { r := 0; } else { r := 7; } }\n",
     "fails"),
    # The early return's r == 1 violates r >= 2; if return did not emit the
    # ensures obligation, this would wrongly verify.
    ("return_early_bad",
     "procedure P(x: int) returns (r: int)\n  ensures r >= 2;\n"
     "{ if (x <= 0) { r := 1; return; }\n  r := x + 1; }\n",
     "fails"),
    # Code after a return is dead: the reference prunes unreachable blocks
    # before VC generation, so `assert false` there cannot fail.
    ("dead_after_return",
     "procedure P() returns (r: int)\n  ensures r == 1;\n"
     "{ r := 1;  return;\n  assert false;\n  r := 2; }\n",
     "verified"),
    # A return inside a loop body owes no invariant preservation; the
    # completing paths (i /= 5) restore i <= 10, and without the completion
    # guard in the preservation antecedent this correct loop fails.
    ("loop_return_completion",
     "procedure P() returns (i: int)\n"
     "{ i := 0;\n  while (i < 10)\n    invariant i <= 10;\n"
     "  { if (i == 5) { return; }\n    i := i + 1; }\n}\n",
     "verified"),
    ("loop_invariant_broken",
     "procedure P() returns (i: int)\n"
     "{\n  i := 0;\n  while (i < 10)\n    invariant i <= 5;\n"
     "  { i := i + 1; }\n}\n",
     "fails"),
    # CFG: forward gotos, demonic multi-target, a goto loop with the
    # implicit-true invariant cut, and break as an exit edge.
    ("goto_forward", _fixture("goto_forward.bpl"), "verified"),
    ("goto_multi_target", _fixture("goto_multi_target.bpl"), "verified"),
    ("goto_loop", _fixture("goto_loop.bpl"), "verified"),
    ("break_search", _fixture("break_search.bpl"), "verified"),
    # A fact about a cycle variable must NOT carry across the header: with
    # the havoc dropped, x == 0 is wrongly verified.
    ("goto_loop_forgets",
     "procedure P() returns (r: int)\n  ensures r == 0;\n"
     "{\n  var x: int;\n  x := 0;\nHead:\n  x := x + 1;\n"
     "  if (x < 3) { goto Head; }\n  r := x;\n}\n",
     "fails"),
    # break can exit early, so i == n fails; if the break edge were dropped
    # from the continuation, only the guard-false exit would remain and this
    # would wrongly verify.
    ("break_early_exit",
     "procedure P(n: int) returns (i: int)\n"
     "  requires n >= 0;\n  ensures i == n;\n"
     "{\n  i := 0;\n  while (i < n)\n    invariant i <= n;\n"
     "  { if (*) { break; }\n    i := i + 1; }\n}\n",
     "fails"),
    # The demonic join at Done can produce 2, so r == 1 fails; collapsing the
    # two edges into one would wrongly verify it.
    ("nondet_goto_join",
     "procedure P() returns (r: int)\n  ensures r == 1;\n"
     "{\n  goto A, B;\nA:\n  r := 1;\n  goto Done;\nB:\n  r := 2;\nDone:\n}\n",
     "fails"),
    # A header's assert prefix IS the loop's invariants (the reference's
    # RemoveBackEdges turns it into the invariant set): i == g is checked on
    # entry and at the back edge, assumed at the head. Verified exactly when
    # the treatment is there.
    ("goto_loop_header_invariant",
     "var g: int;\n"
     "procedure P() returns (r: int)\n  modifies g;\n  ensures true;\n"
     "{\n  var i: int;\n  i := 0;  g := 0;\nHead:\n  assert i == g;\n"
     "  if (i < 5) { i := i + 1;  g := g + 1;  goto Head; }\n  r := 0;\n}\n",
     "verified"),
    # ...and the same shape with a broken header invariant must fail: the back
    # edge is where preservation is checked.
    ("goto_loop_header_invariant_broken",
     "procedure P() returns (r: int)\n  ensures true;\n"
     "{\n  var i: int;\n  i := 0;\nHead:\n  assert i <= 2;\n"
     "  if (*) { i := i + 1;  goto Head; }\n  r := 0;\n}\n",
     "fails"),
    # A call inside a loop body extends the loop's havoc set with the callee's
    # checked modifies: Bump may change g each iteration, so g == 0 must FAIL
    # (with the scanner missing it, g keeps its pre-loop value and this
    # wrongly verifies).
    ("loop_call_modifies",
     "var g: int;\n"
     "procedure Bump();\n  modifies g;\n  ensures true;\n"
     "procedure P(n: int) returns (r: int)\n"
     "  requires g == 0 && n >= 0;\n  modifies g;\n  ensures g == 0;\n"
     "{\n  var i: int;\n  i := 0;\n"
     "  while (i < n)\n    invariant i <= n;\n"
     "  { call Bump();  i := i + 1; }\n}\n",
     "fails"),
    # ...and with an invariant about g, the same shape verifies: the
    # invariant is assumed at the head and the call's ensures preserves it.
    ("loop_call_ok",
     "var g: int;\n"
     "procedure Bump();\n  modifies g;\n  ensures g >= old(g);\n"
     "procedure P(n: int) returns (r: int)\n"
     "  requires g == 0 && n >= 0;\n  modifies g;\n  ensures g >= 0;\n"
     "{\n  var i: int;\n  i := 0;\n"
     "  while (i < n)\n    invariant i <= n;\n    invariant g >= 0;\n"
     "  { call Bump();  i := i + 1; }\n}\n",
     "verified"),
]

def verdict(source):
    t = sp.translate(source=source, language="boogie")
    assert t.ok, t.diagnostic_items[0].message if t.diagnostic_items else "no model"
    solver = z3.Solver()
    solver.from_string(t.to_smt2())
    return solver.check()


@pytest.mark.parametrize("name,source,expected", VERDICT_CORPUS,
                         ids=[c[0] for c in VERDICT_CORPUS])
def test_boogie_verdict(name, source, expected):
    result = verdict(source)
    if expected == "verified":
        assert result == z3.unsat, f"{name}: expected verified (unsat), got {result}"
    else:
        assert result == z3.sat, f"{name}: expected a counterexample (sat), got {result}"
