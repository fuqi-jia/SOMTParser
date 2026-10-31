"""Caller-controlled finite sizes preserve exact domains and all sum terms."""
import pytest
import z3
import somtparser as sp

from somtparser.construction_limits import construction_limits, current_construction_limits
from somtparser.hir import HirBuilder, ModelError


def lit(value):
    return {"literal": value, "sort": "Int"}


def op(name, *args):
    return {"op": name, "args": list(args)}


def loaded(builder):
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    ctx = z3.Context()
    assertions = z3.parse_smt2_string(result.to_smt2(), ctx=ctx)
    return ctx, assertions


@pytest.mark.parametrize("value", [0, -1, True, 1.5, "25600"])
def test_finite_size_policy_requires_positive_integer_or_none(value):
    with pytest.raises(ValueError):
        with construction_limits(max_finite_elements=value):
            pass


def test_finite_size_policy_is_snapshotted_and_default_is_restored():
    before = current_construction_limits()
    default = HirBuilder()
    with construction_limits(max_finite_elements=None):
        unlimited = HirBuilder()
    assert current_construction_limits() == before
    with pytest.raises(ModelError, match="shape"):
        default.declare("a", "Int", shape=[25600])
    unlimited.declare("a", "Int", shape=[25600])
    assert unlimited.validate() == []
    with construction_limits(max_finite_elements=2):
        tiny = HirBuilder()
    with pytest.raises(ModelError, match="2 elements"):
        tiny.expr({"fold": "forall", "var": "i", "range": [0, 3],
                   "body": {"literal": True, "sort": "Bool"}})


@pytest.mark.parametrize("negated", [False, True])
def test_large_boolean_fold_has_exact_half_open_domain(negated):
    with construction_limits(max_finite_elements=None):
        builder = HirBuilder()
    builder.declare("bound", "Int")
    expression = {"fold": "forall", "var": "i", "range": [-2, 25598],
                  "body": op("le", {"var": "i"}, {"var": "bound"})}
    builder.constrain(op("not", expression) if negated else expression)
    ctx, assertions = loaded(builder)
    expected = z3.Int("bound", ctx=ctx) >= 25597
    proof = z3.Solver(ctx=ctx)
    proof.add(z3.Xor(z3.And(*assertions), z3.Not(expected) if negated else expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()


def test_large_sum_preserves_every_term_beyond_one_native_application():
    with construction_limits(max_finite_elements=None, max_hir_nodes=None):
        builder = HirBuilder()
    builder.declare("offset", "Int")
    builder.declare("total", "Int")
    summation = {"fold": "sum", "var": "i", "range": [0, 25600],
                 "body": op("add", {"var": "i"}, {"var": "offset"})}
    builder.constrain(op("eq", {"var": "total"}, summation))
    ctx, assertions = loaded(builder)
    expected = (z3.Int("total", ctx=ctx) ==
                25600 * z3.Int("offset", ctx=ctx) + 25600 * 25599 // 2)
    proof = z3.Solver(ctx=ctx)
    proof.add(z3.Xor(z3.And(*assertions), expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()


def test_large_shaped_array_keeps_all_explicit_bounds():
    with construction_limits(max_finite_elements=None):
        builder = HirBuilder()
    builder.declare("a", "Int", shape=[25600], lower=-3)
    ctx, assertions = loaded(builder)
    array = z3.Array("a", z3.IntSort(ctx), z3.IntSort(ctx))
    assert len(assertions) == 25600
    # Check every bound after normalizing SMT unary minus and Z3 numerals.
    for index, assertion in enumerate(assertions):
        expected = z3.Select(array, index) >= -3
        assert z3.eq(z3.simplify(assertion), z3.simplify(expected)), index


def test_large_provider_fold_normalizes_its_body_with_lexical_scope():
    model = dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                 declarations=[dict(name="a", sort={"Array": ["Int", "Int"]})],
                 functions=[], constraints=[dict(span=[0, 1], expr={"finite_fold": {
                     "fold": "forall", "var": "i", "range": [0, 25600],
                     "body": op("ge", {"var": "a", "indices": [{"var": "i"}]}, lit(0))}})],
                 objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])
    with construction_limits(max_finite_elements=None):
        candidate = sp.propose_nl("x", language="hir", provider=lambda request: model)
        assert candidate.valid, candidate.diagnostics
        result = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert result.ok, [d.message for d in result.diagnostics]
    ctx = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(), ctx=ctx))
    array = z3.Array("a", z3.IntSort(ctx), z3.IntSort(ctx))
    index = z3.Int("source_index", ctx=ctx)
    expected = z3.ForAll(index, z3.Implies(z3.And(index >= 0, index < 25600),
                                          z3.Select(array, index) >= 0))
    proof = z3.Solver(ctx=ctx)
    proof.add(z3.Xor(actual, expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()
