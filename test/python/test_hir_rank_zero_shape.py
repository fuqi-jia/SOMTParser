"""Rank-zero declaration shape preserves scalar semantics and candidate data."""
import copy
import pytest
import z3
from somtparser import HirBuilder, propose_nl, compile_candidate
from somtparser.hir import ModelError


def expression(op, *args):
    return {"op": op, "args": list(args)}


def formula(builder):
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def same(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("shape", [None, []])
def test_rank_zero_bounds_and_distinct_are_scalar_relations(shape):
    b = HirBuilder()
    b.declare("x", "Int", lower=-2, upper=3, shape=shape)
    b.declare("y", "Int", shape=[])
    b.constrain(expression("all_different", {"var": "x"}, {"var": "y"}))
    x, y = z3.Ints("x y")
    same(formula(b), z3.And(x >= -2, x <= 3, x != y))


def test_zero_axis_is_not_a_zero_length_axis():
    b = HirBuilder()
    b.declare("scalar", "Int", lower=1, upper=0, shape=[])
    same(formula(b), z3.BoolVal(False))
    empty = HirBuilder()
    empty.declare("array", "Int", lower=1, upper=0, shape=[0])
    same(formula(empty), z3.BoolVal(True))


def test_rank_zero_does_not_invent_extent_for_a_total_array_sort():
    b = HirBuilder()
    b.declare("open", {"Array": ["Int", "Int"]}, shape=[])
    with pytest.raises(ModelError, match="scalar Int"):
        b.expr(expression("all_different", {"var": "open"}))


def test_provider_candidate_rank_zero_keeps_snapshot_and_objective():
    source = "Choose integer x between -2 and 3 to maximize x."
    raw = {"schema": "somt-hir-model-v1", "language": "hir",
           "decision": "optimization", "declarations": [
               {"name": "x", "sort": "Int", "shape": [], "lower": -2, "upper": 3}],
           "functions": [], "constraints": [], "goal": None, "objective_order": "single",
           "objectives": [{"sense": "maximize", "expr": {"var": "x"}, "span": [0, len(source)]}],
           "assumptions": [], "unresolved": []}
    saved = copy.deepcopy(raw)
    candidate = propose_nl(source, language="hir", provider=lambda request: raw)
    assert candidate.valid, candidate.diagnostics
    result = compile_candidate(candidate, accept_digest=candidate.digest)
    assert result.ok, result.diagnostics
    assert raw == saved and candidate.model["declarations"][0]["shape"] == []
    model = z3.Optimize()
    model.from_string(result.to_smt2())
    x = z3.Int("x")
    same(z3.And(*model.assertions()), z3.And(x >= -2, x <= 3))
    assert len(model.objectives()) == 1
    # Z3 represents maximize as minimization of the negated cost.
    solver = z3.Solver()
    solver.add(model.objectives()[0] != -x)
    assert solver.check() == z3.unsat
