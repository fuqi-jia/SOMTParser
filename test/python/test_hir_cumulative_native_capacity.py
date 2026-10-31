"""Native cumulative accepts large vectors without eager CP expansion."""
from copy import deepcopy

import jsonschema
import pytest
import z3

from somtparser._nl_model import ModelError
from somtparser.hir import HirBuilder, build_hir, hir_schema
from somtparser.hir_cp import cumulative_inputs, expand_cp_expression


def lit(value):
    return {"literal": value, "sort": "Int"}


def relation(count=1001):
    return {"cp": "cumulative", "starts": [{"var": "s"}] * count,
            "durations": [{"var": "d"}] * count,
            "demands": [{"var": "r"}] * count, "capacity": {"var": "b"}}


def model(expr):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=[dict(name=name, sort="Int") for name in ("s", "d", "r", "b")],
                functions=[], constraints=[dict(expr=expr, span=[0, 1])],
                objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])


@pytest.mark.parametrize("negated", [False, True])
def test_1001_tasks_preserve_all_assignments_and_polarity(negated):
    expr = relation()
    if negated:
        expr = {"op": "not", "args": [expr]}
    source = model(expr)
    before = deepcopy(source)
    result = build_hir(source, "x").translate()
    assert result.ok, [entry.message for entry in result.diagnostic_items]
    assert source == before
    assert "cumulative-start-events-shared-load" in result.report.to_json()
    target = result.to_smt2()
    assert len(target) < 1001 * 1000
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(target, ctx=context))
    d, r, b = z3.Ints("d r b", ctx=context)
    # Identical starts and durations make every positive-duration task overlap.
    # Negative durations/resources remain forbidden even under negation.
    expected = z3.And(d >= 0, r >= 0, b >= 0, z3.Or(d == 0, 1001 * r <= b))
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, z3.Not(expected) if negated else expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()


def test_10000_descriptor_tasks_reach_native_hir_without_json_node_inflation():
    builder = HirBuilder()
    for name in ("starts", "durations", "demands"):
        builder.declare(name, "Int", shape=[10000])
    expr = {"cp": "cumulative", **{
        name: {"array": name, "length": 10000}
        for name in ("starts", "durations", "demands")}, "capacity": lit(1)}
    # This verifies the actual native constructor; whole SMT loading is covered
    # separately at 1001 tasks to avoid duplicating the existing lowering tests.
    assert repr(builder.expr(expr).sort) == "Bool"
    candidate = model(expr)
    candidate["declarations"] = [dict(name=name, sort="Int", shape=[10000])
                                 for name in ("starts", "durations", "demands")]
    jsonschema.Draft202012Validator(hir_schema()).validate(candidate)


def test_nested_cp_capacity_reaches_native_builder_without_eager_json_expansion():
    expr = relation()
    expr["capacity"] = {"cp": "maximum", "items": [{"var": "b"}] * 40}
    result = build_hir(model(expr), "x").translate()
    assert result.ok, [entry.message for entry in result.diagnostic_items]
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(), ctx=context))
    d, r, b = z3.Ints("d r b", ctx=context)
    expected = z3.And(d >= 0, r >= 0, b >= 0, z3.Or(d == 0, 1001 * r <= b))
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()


@pytest.mark.parametrize("field", ["starts", "durations", "demands"])
def test_large_descriptor_keeps_rank_and_final_axis_checks(field):
    builder = HirBuilder()
    builder.declare("matrix", "Int", shape=[2, 1001])
    builder.declare("s", "Int")
    builder.declare("d", "Int")
    builder.declare("r", "Int")
    builder.declare("b", "Int")
    expr = relation()
    expr[field] = {"array": "matrix", "length": 1001}
    with pytest.raises(ModelError, match="fixed prefix"):
        builder.expr(expr)
    expr[field]["prefix"] = [lit(1)]
    assert repr(builder.expr(expr).sort) == "Bool"
    expr[field]["length"] = 1002
    with pytest.raises(ModelError, match="final-axis size"):
        builder.expr(expr)


@pytest.mark.parametrize("field", ["starts", "durations", "demands"])
def test_large_native_vectors_preserve_exact_int_types(field):
    expr = relation()
    expr[field][-1] = {"literal": True, "sort": "Bool"}
    with pytest.raises(ModelError, match="exact sort Int"):
        build_hir(model(expr), "x")


def test_mismatch_negative_data_and_explicit_expansion_still_fail():
    expr = relation()
    expr["demands"] = [1] * 1000
    with pytest.raises(ModelError, match="length mismatch"):
        cumulative_inputs(expr)
    expr["demands"] = [1] * 1000 + [-1]
    with pytest.raises(ModelError, match="nonnegative"):
        cumulative_inputs(expr)
    expr = relation()
    with pytest.raises(ModelError, match="1000 elements"):
        expand_cp_expression(expr)
    # Native scheduling now accepts a wider descriptor than finite-shape
    # declarations; the builder still enforces its caller-owned node budget.
    wide = relation(10001)
    assert len(cumulative_inputs(wide)[0]) == 10001
    expr["starts"] = {"array": "s", "length": 100001}
    with pytest.raises(ModelError, match="invalid CP array vector"):
        cumulative_inputs(expr)
