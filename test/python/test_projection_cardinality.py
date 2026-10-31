"""Integration differentials for exact cardinality compression in projection."""
import pytest
z3 = pytest.importorskip("z3")

from tools.semantic_checks.checker_adapter import (
    candidate_projection,
    reference_projection,
)
from tools.semantic_checks.finite_at_most_one import (
    rewrite_top_level_and_conjuncts,
)
from tools.semantic_checks.projection import (
    free_constants,
    optimize_observation_projection,
)


def _equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.set(timeout=5000)
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


def _pairwise_relation(array, enabled, collision=None):
    ctx = array.ctx
    row_a, row_b, index_a, index_b = z3.Ints(
        "projection_row_a projection_row_b projection_index_a projection_index_b",
        ctx=ctx,
    )
    guard = [row_a >= 0, row_a < 3, row_b >= 0, row_b < 3,
             row_a < row_b, index_a >= 0, index_a < 3,
             index_a < index_b, index_b < 3, enabled]
    if collision is not None:
        guard.append(collision == 11)
    same_a = z3.Select(z3.Select(array, row_a), index_a) == \
        z3.Select(z3.Select(array, row_b), index_a)
    same_b = z3.Select(z3.Select(array, row_a), index_b) == \
        z3.Select(z3.Select(array, row_b), index_b)
    return z3.ForAll(
        [row_a, row_b, index_a, index_b],
        z3.Implies(z3.And(*guard), z3.Or(z3.Not(same_a), z3.Not(same_b))),
    )


def _uninterpreted_ids(expressions):
    return {constant.get_id() for constant in free_constants(expressions)}


def test_projection_reuses_exact_rewrite_with_observations_cost_and_free_guards():
    ctx = z3.Context()
    array = z3.Array(
        "projection_matrix", z3.IntSort(ctx=ctx),
        z3.ArraySort(z3.IntSort(ctx=ctx), z3.IntSort(ctx=ctx)),
    )
    enabled = z3.Bool("projection_enabled", ctx=ctx)
    # This free name collided with a FreshConst spelling in earlier Z3 output.
    collision = z3.Int("pair_left!0", ctx=ctx)
    quantified = _pairwise_relation(array, enabled, collision)
    enabled_alias = z3.Bool("projected_enabled", ctx=ctx)
    collision_alias = z3.Int("projected_collision", ctx=ctx)

    aliases = [
        [z3.Int(f"projected_{r}_{i}", ctx=ctx) for i in range(3)]
        for r in range(3)
    ]
    observation_bridges = [
        (enabled_alias, enabled),
        (collision_alias, collision),
        *[
        (aliases[r][i], z3.Select(z3.Select(array, r), i))
        for r in range(3) for i in range(3)
        ],
    ]
    cost = z3.Real("projected_cost", ctx=ctx)
    cost_term = z3.ToReal(
        z3.Select(z3.Select(array, 0), 0)
        + z3.Select(z3.Select(array, 2), 2))
    cost_bridge = (cost, cost_term)

    candidate = candidate_projection(
        [quantified], observation_bridges, cost_bridge)
    reference = reference_projection(
        [quantified], observation_bridges, cost_bridge)
    assert candidate.optimization.cardinality_rewrites == 1

    # The array is read only at these nine observed coordinates. Projection
    # removes the array while retaining all alias equations and the cost bridge.
    assert "projection_matrix" in candidate.optimization.eliminated_array_roots
    free_ids = _uninterpreted_ids([candidate.formula])
    assert all(alias.get_id() in free_ids for row in aliases for alias in row)
    assert cost.get_id() in free_ids
    assert enabled_alias.get_id() in free_ids
    assert collision_alias.get_id() in free_ids
    assert enabled.get_id() not in free_ids
    assert collision.get_id() not in free_ids
    assert not any(constant.sort().kind() == z3.Z3_ARRAY_SORT
                   and constant.get_id() in free_ids
                   for constant in free_constants([candidate.formula]))

    expected_constraints = [
        z3.Implies(
            z3.And(enabled_alias, collision_alias == 11),
            z3.Sum(*[
                z3.If(aliases[row_a][index] == aliases[row_b][index], 1, 0)
                for index in range(3)
            ]) <= 1,
        )
        for row_a in range(3)
        for row_b in range(row_a + 1, 3)
    ]
    expected_constraints.append(
        cost == z3.ToReal(aliases[0][0] + aliases[2][2]))
    expected = z3.And(*expected_constraints)
    assert _equivalent(candidate.formula, expected)
    assert _equivalent(reference, expected)
    assert _equivalent(candidate.formula, reference)


def test_top_level_conjunct_entry_does_not_cross_negation_or_disjunction():
    ctx = z3.Context()
    array = z3.Array(
        "negative_context_array", z3.IntSort(ctx=ctx),
        z3.ArraySort(z3.IntSort(ctx=ctx), z3.IntSort(ctx=ctx)),
    )
    enabled = z3.Bool("negative_context_enabled", ctx=ctx)
    q1 = _pairwise_relation(array, enabled)
    q2 = _pairwise_relation(array, z3.Not(enabled))

    for formula in (z3.Not(q1), z3.Or(q1, q2)):
        result = rewrite_top_level_and_conjuncts(formula)
        assert result.rewrite_count == 0
        assert not result.budget_exhausted
        assert result.formula.eq(formula)

    optimized = optimize_observation_projection(z3.Not(q1), [])
    assert optimized.cardinality_rewrites == 0


def test_top_level_and_rewrite_budget_rolls_back_the_whole_formula():
    ctx = z3.Context()
    array = z3.Array(
        "budget_context_array", z3.IntSort(ctx=ctx),
        z3.ArraySort(z3.IntSort(ctx=ctx), z3.IntSort(ctx=ctx)),
    )
    enabled = z3.Bool("budget_context_enabled", ctx=ctx)
    formula = z3.And(_pairwise_relation(array, enabled))
    result = rewrite_top_level_and_conjuncts(
        formula, max_generated_nodes=1)
    assert result.budget_exhausted
    assert result.rewrite_count == 0
    assert result.formula.eq(formula)
