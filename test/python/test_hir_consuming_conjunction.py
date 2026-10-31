"""Splitting hard assertions preserves the entire satisfying assignment set."""
import pytest
import z3

from somtparser.hir import HirBuilder


@pytest.mark.parametrize("nested", [False, True])
def test_consuming_hard_conjunction_matches_independent_formula(nested):
    builder = HirBuilder()
    for name in ("p", "q", "r"):
        builder.declare(name, "Bool")
    p, q, r = ({"var": name} for name in ("p", "q", "r"))
    either = {"op": "or", "args": [p, q]}
    excludes = {"op": "not", "args": [r]}
    rhs = {"op": "and", "args": [q, excludes]} if nested else excludes
    builder.constrain({"op": "and", "args": [either, rhs]})
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    pz, qz, rz = z3.Bools("p q r", ctx=context)
    expected = z3.And(z3.Or(pz, qz), z3.Not(rz), qz) if nested else z3.And(
        z3.Or(pz, qz), z3.Not(rz))
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
