"""Actual Boogie002 failures: check source types before VC pruning,
preserve unique constants in Horn entry states, and fold signed BV mod exactly.
"""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

BAD_ASSIGNMENTS = [
    "type A,B;procedure P(x:A) returns(y:B){y:=x;}",
    "type A,B;procedure P(x:A) returns(y:B){return;y:=x;}",
    "type A,B;procedure P(x:A,m:[int]B){var n:[int]B;n:=m;n[0]:=x;}",
    "type A,B;procedure P(x:A,m:[B]int){var n:[B]int;n:=m;n[x]:=1;}",
    "procedure P(x:bv8) returns(y:bv16){y:=x;}",
    "procedure P(x:bool) returns(y:int){y:=x;}",
]


@pytest.mark.parametrize("source", BAD_ASSIGNMENTS)
@pytest.mark.parametrize("horn", [False, True])
def test_bad_assignment_rejected_even_without_a_live_obligation(source, horn):
    translated = sp.translate(source=source, language="boogie",
                              options={"chc": "1"} if horn else {})
    assert not translated.ok
    assert any("assignment" in diagnostic.message for diagnostic in translated.diagnostic_items)


@pytest.mark.parametrize("constants,assertion,expected", [
    ("const unique a,b:bool;", "a!=b", "sat"),
    ("const unique a,b:bool;", "false", "unsat"),
    ("const unique a,b,c:bool;", "false", "sat"),
])
def test_horn_unique_constants_constrain_entry_states(constants, assertion, expected):
    translated = sp.translate(source=constants + "procedure P(){assert " + assertion + ";}",
                              language="boogie", options={"chc": "1"})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    # Horn satisfiability means a safe program, the reverse of direct VC SAT.
    assert str(solver.check()) == expected, solver.reason_unknown()


@pytest.mark.parametrize("width", [1, 8, 65])
@pytest.mark.parametrize("left,right", [(-7,3), (7,-3), (-7,-3), (7,3), (-6,-3), (-7,0)])
def test_signed_mod_constant_folding_matches_independent_symbolic_operator(width, left, right):
    mask = (1 << width) - 1
    left &= mask
    right &= mask
    source = (f"(declare-const observed (_ BitVec {width}))"
              f"(assert (= observed (bvsmod (_ bv{left} {width}) (_ bv{right} {width}))))")
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    observed = z3.BitVec("observed", width, ctx=context)
    expected = observed == z3.BitVecVal(left, width, ctx=context) % z3.BitVecVal(right, width, ctx=context)
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat, solver.reason_unknown()
