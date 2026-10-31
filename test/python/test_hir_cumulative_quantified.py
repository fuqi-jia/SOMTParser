"""Quantified cumulative retains exact load semantics and linear SMT size."""
import pytest
import z3
from somtparser import _somtparser as native
from somtparser.hir import HirBuilder


def lit(value):
    return {"literal": value, "sort": "Int"}


@pytest.mark.parametrize("negated", [False, True])
def test_quantified_load_equals_independent_finite_time_grid(negated):
    names = ["s0", "s1", "d0", "d1", "r0", "r1", "b"]
    builder = HirBuilder()
    for name in names:
        builder.declare(name, "Int")
    expr = {"cp": "cumulative", "starts": [{"var": f"s{i % 2}"} for i in range(128)],
            "durations": [{"var": f"d{i % 2}"} for i in range(128)],
            "demands": [{"var": f"r{i % 2}"} for i in range(128)], "capacity": {"var": "b"}}
    builder.constrain({"op": "not", "args": [expr]} if negated else expr)
    result = builder.translate(profile="quantified")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert "cumulative-integer-time-quantified" in result.report.to_json()
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(), ctx=context))
    values = {name: z3.Int(name, ctx=context) for name in names}
    expected = z3.And(values["b"] >= 0, *[values[name] >= 0 for name in names[2:6]], *[
        64 * z3.Sum(*[z3.If(z3.And(values[f"s{i}"] <= t,
                                  t < values[f"s{i}"] + values[f"d{i}"]), values[f"r{i}"], 0)
                     for i in range(2)]) <= values["b"] for t in range(-2, 6)])
    proof = z3.Solver(ctx=context)
    for name, term in values.items():
        proof.add(term >= (-2 if name.startswith("s") else -1))
        proof.add(term <= (2 if name.startswith("s") else 256 if name == "b" else 3))
    proof.add(z3.Xor(actual, z3.Not(expected) if negated else expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()


def test_25600_tasks_construct_export_and_load_without_event_cross_product():
    builder = HirBuilder()
    builder.declare("starts", {"Array": ["Int", "Int"]})
    builder.constrain({"cp": "cumulative", "starts": {"array": "starts", "length": 25600},
                       "durations": [1] * 25600, "demands": [1] * 25600, "capacity": lit(100)})
    result = builder.translate(profile="quantified")
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = result.to_smt2()
    assert "cumulative-integer-time-quantified" in result.report.to_json()
    assert len(target) < 25600 * 500
    parsed = z3.Optimize(ctx=z3.Context())
    parsed.from_string(target)
    assert len(parsed.assertions()) > 0


def test_fresh_time_binder_does_not_capture_source_demand():
    raw = native.HirModel()
    integer = native.HirSort.integer()
    name = "!cumulative_time0"
    demand = raw.declare(name, integer)
    number = lambda n: native._hir_literal(integer, str(n))
    raw.constrain(native._hir_global("cumulative", [number(1), number(0), number(3), demand]))
    result = raw.translate(profile="quantified")
    assert result.ok, [d.message for d in result.diagnostic_items]
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(), ctx=context))
    expected = z3.And(z3.Int(name, ctx=context) >= 0, z3.Int(name, ctx=context) <= 1)
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()


@pytest.mark.parametrize("capacity,negated,expected", [(0, False, False), (0, True, True), (1, False, True)])
def test_nested_lexical_start_scope_is_preserved(capacity, negated, expected):
    builder = HirBuilder()
    relation = {"cp": "cumulative", "starts": [{"var": "t"}, {"op": "add", "args": [{"var": "t"}, lit(1)]}],
                "durations": [1, 1], "demands": [1, 1], "capacity": lit(capacity)}
    if negated:
        relation = {"op": "not", "args": [relation]}
    builder.constrain({"quantifier": "forall", "binders": [{"name": "t", "sort": "Int"}], "body": relation})
    result = builder.translate(profile="quantified")
    assert result.ok, [d.message for d in result.diagnostic_items]
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(), ctx=context))
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, z3.BoolVal(expected, ctx=context)))
    assert proof.check() == z3.unsat, proof.reason_unknown()
