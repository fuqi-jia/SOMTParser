"""Large no_overlap uses a shared global and preserves all interval choices."""
import pytest
import z3
from somtparser.hir import HirBuilder, ModelError


def lit(value):
    return {"literal": value, "sort": "Int"}


@pytest.mark.parametrize("negated", [False, True])
def test_large_unit_intervals_equal_independent_forbidden_integer_positions(negated):
    builder = HirBuilder()
    builder.declare("tail", "Int")
    builder.declare("zero_duration_start", "Int")
    positions = [2 * i - 128 for i in range(64)]
    relation = {"cp": "no_overlap",
                "starts": [lit(i) for i in positions] + [{"var": "tail"}, {"var": "zero_duration_start"}],
                "durations": [1] * 65 + [0]}
    builder.constrain({"op": "not", "args": [relation]} if negated else relation)
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert "cumulative-start-events-shared-load" in translated.report.to_json()
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    tail = z3.Int("tail", ctx=context)
    expected = z3.And(*[tail != position for position in positions])
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, z3.Not(expected) if negated else expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()


def test_one_thousand_intervals_construct_with_linear_hir_budget():
    builder = HirBuilder()
    builder.declare("starts", {"Array": ["Int", "Int"]})
    relation = {"cp": "no_overlap", "starts": {"array": "starts", "length": 1000},
                "durations": [2] * 1000}
    expression = builder.expr(relation)
    assert repr(expression.sort) == "Bool"
    assert builder.nodes < 10000


def test_zero_duration_bad_operand_is_rejected_during_construction():
    builder = HirBuilder()
    builder.declare("scalar", "Int")
    bad = {"op": "select", "args": [{"var": "scalar"}, lit(0)]}
    relation = {"cp": "no_overlap", "starts": [lit(2 * i) for i in range(64)] + [bad],
                "durations": [1] * 64 + [0]}
    with pytest.raises((ModelError, ValueError), match="array"):
        builder.constrain({"op": "not", "args": [relation]})


def test_zero_duration_selector_keeps_deep_native_operand_validation():
    builder = HirBuilder()
    builder.declare_datatype({"name": "Box", "constructors": [
        {"name": "box", "fields": [{"name": "value", "sort": "Int"}]}]})
    bad = {"dt_selector": "value", "sort": "Int",
           "value": {"literal": True, "sort": "Bool"}}
    relation = {"cp": "no_overlap", "starts": [lit(2 * i) for i in range(64)] + [bad],
                "durations": [1] * 64 + [0]}
    # The declared selector result is Int, but its Boolean argument is invalid.
    # Zero duration must not erase that error from native HIR checking.
    builder.constrain({"op": "not", "args": [relation]})
    with pytest.raises(ModelError):
        builder.validate()
    assert not builder.translate().ok


def test_large_no_overlap_retains_lexical_quantifier_binding():
    builder = HirBuilder()
    builder.declare("threshold", "Int")
    relation = {"cp": "no_overlap",
                "starts": [lit(2 * i - 128) for i in range(64)] + [{"var": "tail"}],
                "durations": [1] * 65}
    guard = {"op": "ge", "args": [{"var": "tail"}, {"var": "threshold"}]}
    builder.constrain({"quantifier": "forall", "binders": [{"name": "tail", "sort": "Int"}],
                       "body": {"op": "implies", "args": [guard, relation]}})
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, z3.Int("threshold", ctx=context) >= -1))
    assert proof.check() == z3.unsat, proof.reason_unknown()
