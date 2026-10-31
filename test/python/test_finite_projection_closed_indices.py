"""Semantic regressions for shifted reads left by finite instantiation."""
import pytest
import z3

from tools.semantic_checks.checker_adapter import candidate_projection
from tools.semantic_checks.finite_quantifiers import expand_finite_int_quantifiers
from tools.semantic_checks.projection import free_constants


def assert_equivalent(left, right):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat, solver.reason_unknown()


def array_roots(expression):
    return [term for term in free_constants([expression])
            if term.sort().kind() == z3.Z3_ARRAY_SORT]


@pytest.mark.parametrize('index,cells', [
    (lambda i: 1 + i, [1, 2, 3]),
    (lambda i: i - 2, [-2, -1, 0]),
    (lambda i: -i, [0, -1, -2]),
    (lambda i: 2 * (i - 1) + 3, [1, 3, 5]),
    (lambda i: (i - 5) / 2, [-3, -2, -2]),
    (lambda i: (i - 5) / -2, [3, 2, 2]),
    (lambda i: (i - 5) % 3, [1, 2, 0]),
], ids=['shift', 'negative-offset', 'negation', 'nested-arithmetic',
        'negative-int-division', 'negative-divisor', 'negative-modulus'])
def test_finite_indices_project_to_observed_scalar_specification(index, cells):
    array = z3.Array('index_array', z3.IntSort(), z3.IntSort())
    i = z3.Int('index_i')
    quantified = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 3), array[index(i)] >= i))
    unique_cells = list(dict.fromkeys(cells))
    aliases = {cell: z3.Int('observed_' + str(cell)) for cell in unique_cells}
    bridges = [(alias, array[cell]) for cell, alias in aliases.items()]
    optimized = candidate_projection([quantified], bridges, guarded_bool_budget_ms=0)
    expected = z3.And(*[aliases[cell] >= value for value, cell in enumerate(cells)])
    assert optimized.optimization.eliminated_array_roots == ('index_array',)
    assert not array_roots(optimized.formula)
    assert_equivalent(optimized.formula, expected)
    # Independently compare the expanded source over the original array. This
    # also checks negative division/modulus against explicit expected cells.
    expanded = expand_finite_int_quantifiers(quantified)
    assert_equivalent(expanded.formula,
                      z3.And(*[array[cell] >= value for value, cell in enumerate(cells)]))


def test_shifted_windows_keep_every_constraint_and_duplicate_observation():
    array = z3.Array('window_array', z3.IntSort(), z3.IntSort())
    i = z3.Int('window_i')
    observations = z3.Ints('window_0 window_1 window_2 window_3 window_1_duplicate')
    bridges = [(observations[n], array[n]) for n in range(4)]
    bridges.append((observations[4], array[1]))
    constraints = [array[0] >= 0, array[3] <= 9,
        z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 3), array[i + 1] >= array[i]))]
    result = candidate_projection(constraints, bridges, guarded_bool_budget_ms=0)
    expected = z3.And(observations[0] >= 0, observations[3] <= 9,
        observations[1] >= observations[0], observations[2] >= observations[1],
        observations[3] >= observations[2], observations[4] == observations[1])
    assert not array_roots(result.formula)
    assert_equivalent(result.formula, expected)


def test_nested_array_read_indices_are_canonicalized_without_prefix_loss():
    array = z3.Array('nested_array', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    i = z3.Int('nested_i')
    left, right = z3.Ints('nested_left nested_right')
    source = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 2), array[i + 1][-i] >= i))
    result = candidate_projection([source], [(left, array[1][0]), (right, array[2][-1])],
                                  guarded_bool_budget_ms=0)
    assert not array_roots(result.formula)
    assert_equivalent(result.formula, z3.And(left >= 0, right >= 1))


def test_unobserved_outside_cells_remain_distinct_existential_witnesses():
    array = z3.Array('outside_array', z3.IntSort(), z3.IntSort())
    i = z3.Int('outside_i')
    observed = z3.Int('outside_observed')
    bounds = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 2), array[i + 8] >= i))
    # A[8] and A[9] lie beyond the only observed cell; neither may be dropped
    # or merged with A[0]. Their common lower bound constrains the observation.
    result = candidate_projection([bounds, array[8] <= array[0], array[9] <= array[0]],
        [(observed, array[0])], guarded_bool_budget_ms=0)
    assert result.optimization.finite_array_read_cells == 3
    assert not array_roots(result.formula)
    assert_equivalent(result.formula, observed >= 1)


def test_unobserved_outside_cell_contradiction_is_not_discarded():
    array = z3.Array('outside_conflict', z3.IntSort(), z3.IntSort())
    i = z3.Int('outside_conflict_i')
    observed = z3.Int('outside_conflict_observed')
    quantified = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 1), array[i + 8] == 1))
    result = candidate_projection([quantified, array[8] == 0],
                                 [(observed, array[0])], guarded_bool_budget_ms=0)
    assert_equivalent(result.formula, z3.BoolVal(False))


def test_symbolic_indices_preserve_the_entire_array_root():
    array = z3.Array('symbolic_array', z3.IntSort(), z3.IntSort())
    i, offset, observed = z3.Ints('symbolic_i symbolic_offset symbolic_observed')
    quantified = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 2), array[i + offset] >= i))
    result = candidate_projection([quantified], [(observed, array[0])], guarded_bool_budget_ms=0)
    assert result.optimization.retained_array_roots == ('symbolic_array',)
    expected = z3.And(array[0 + offset] >= 0, array[1 + offset] >= 1, observed == array[0])
    assert_equivalent(result.optimization.body, expected)


def test_whole_array_equality_blocks_partial_root_elimination():
    left, right = (z3.Array(name, z3.IntSort(), z3.IntSort())
                   for name in ('whole_left', 'whole_right'))
    i, observed = z3.Ints('whole_i whole_observed')
    quantified = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 1), left[i + 0] >= 0))
    result = candidate_projection([left == right, quantified], [(observed, left[0])],
                                  guarded_bool_budget_ms=0)
    assert {str(root) for root in array_roots(result.optimization.body)} == {'whole_left', 'whole_right'}
    assert_equivalent(result.optimization.body,
                      z3.And(left == right, left[0] >= 0, observed == left[0]))


def test_division_by_zero_index_is_not_replaced_by_a_numeral():
    array = z3.Array('divzero_array', z3.IntSort(), z3.IntSort())
    i, observed = z3.Ints('divzero_i divzero_observed')
    quantified = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 2), array[(i + 1) / 0] >= i))
    result = candidate_projection([quantified], [(observed, array[0])], guarded_bool_budget_ms=0)
    assert result.optimization.retained_array_roots == ('divzero_array',)
    expected = z3.And(array[z3.IntVal(1) / 0] >= 0,
                      array[z3.IntVal(2) / 0] >= 1, observed == array[0])
    assert_equivalent(result.optimization.body, expected)


def test_recursive_function_indices_are_not_unfolded_by_canonicalization():
    array = z3.Array('recursive_index_array', z3.IntSort(), z3.IntSort())
    function = z3.RecFunction('recursive_index', z3.IntSort(), z3.IntSort())
    n, i = z3.Ints('recursive_n recursive_i')
    z3.RecAddDefinition(function, n, z3.If(n <= 0, 0, function(n - 1) + 1))
    source = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 2), array[i + function(0)] >= i))
    result = expand_finite_int_quantifiers(source)
    expected = z3.And(array[0 + function(0)] >= 0, array[1 + function(0)] >= 1)
    assert result.formula.eq(expected)
    assert_equivalent(result.formula, expected)


def test_unbounded_nested_quantifier_is_preserved_without_capturing_indices():
    array = z3.Array('capture_array', z3.IntSort(), z3.IntSort())
    i, j = z3.Ints('capture_i capture_j')
    body = z3.ForAll(j, array[i + j] >= i)
    source = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 2), body))
    result = expand_finite_int_quantifiers(source)
    expected = z3.And(z3.ForAll(j, array[0 + j] >= 0),
                      z3.ForAll(j, array[1 + j] >= 1))
    assert result.stats.skipped_quantifiers == 2
    assert result.formula.eq(expected)
    assert_equivalent(result.formula, expected)


def test_quantifier_budget_failure_returns_original_index_expressions():
    array = z3.Array('rollback_array', z3.IntSort(), z3.IntSort())
    i = z3.Int('rollback_i')
    source = z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 4), array[i + 1] >= i))
    result = expand_finite_int_quantifiers(source, max_emitted_instances=2)
    assert result.stats.budget_exhausted
    assert result.formula.eq(source)


def test_unquantified_arithmetic_read_indices_remain_untouched():
    array = z3.Array('unquantified_array', z3.IntSort(), z3.IntSort())
    source = array[z3.IntVal(1) + 2] >= 0
    result = expand_finite_int_quantifiers(source)
    assert result.stats.expanded_quantifiers == 0
    assert result.formula.eq(source)
