"""Exact finite table normalization, including domain and shadowing controls."""
import time

import z3

from tools.semantic_checks.finite_scalar_tables import normalize_finite_scalar_tables
from tools.semantic_checks.directional_equivalence import check_equivalence


def normalized(expression, **options):
    result = normalize_finite_scalar_tables(expression, **options)
    assert result.completed
    return result.formula


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.set(timeout=0)
    solver.add(left != right)
    assert solver.check() == z3.unsat


def lookup(index, keys, default=0):
    array = z3.K(index.sort(), z3.IntVal(default, ctx=index.ctx))
    for key in keys:
        array = z3.Store(array, key, 1)
    return z3.Select(array, index)


def indicator(index, keys):
    return z3.If(z3.Or(*[index == key for key in keys]), 1, 0)


def prove_instantiated_cell_rewrites(index, candidate_template, reference_template,
                                    xs, candidate_cells, reference_cells):
    # The free integer is arbitrary: these UNSAT checks establish the complete
    # scalar rewrite, including every value outside the finite literal table.
    candidate_rewrite = normalized(candidate_template)
    reference_rewrite = normalized(reference_template)
    equivalent(candidate_template, candidate_rewrite)
    equivalent(reference_template, reference_rewrite)
    assert candidate_rewrite.eq(reference_rewrite)
    assert len(xs) == len(candidate_cells) == len(reference_cells)
    for x, candidate, reference in zip(xs, candidate_cells, reference_cells):
        # Bind every cell used by the large model to the proved template.
        assert z3.substitute(candidate_template, (index, x)).eq(candidate)
        assert z3.substitute(reference_template, (index, x)).eq(reference)


def prove_count_congruence(size, operations):
    left = z3.IntVector('count_congruence_left', size)
    right = z3.IntVector('count_congruence_right', size)
    for positions, kind, bound in operations:
        assert kind in ('le', 'eq')
        lhs = z3.Sum(*[left[position] for position in reversed(positions)])
        rhs = z3.Sum(*[right[position] for position in positions])
        assumptions = z3.And(*[left[position] == right[position] for position in positions])
        left_constraint = lhs <= bound if kind == 'le' else lhs == bound
        right_constraint = rhs <= bound if kind == 'le' else rhs == bound
        # Once the scalar rewrites are proved, every window and total count is
        # an exact integer congruence. No arrays or combinatorial search remain.
        conclusion = z3.And(lhs == rhs, left_constraint == right_constraint)
        equivalent(z3.Implies(assumptions, conclusion), z3.BoolVal(True))


def test_guarded_lookup_indicator_matches_reference_for_every_integer():
    x = z3.Int('table_x')
    keys = [0, 3, 4, 5, 8, 11, 14, 18, 19, 20, 23]
    candidate = z3.If(z3.If(z3.And(x >= 0, x < 25), lookup(x, keys), 0) != 0, 1, 0)
    reference = indicator(x, list(reversed(keys)))
    equivalent(candidate, normalized(candidate))
    assert normalized(candidate).eq(normalized(reference))


def test_twenty_five_windows_factor_without_entailment_queries():
    xs = z3.IntVector('window_table_x', 29)
    keys = [0, 3, 4, 5, 8, 11, 14, 18, 19, 20, 23]
    reference, candidate = [], []
    for start in range(25):
        reference.append(z3.Sum(*[indicator(x, keys) for x in xs[start:start+5]]) <= 2)
        candidate.append(z3.Sum(*[z3.If(
            z3.If(z3.And(x < 25, 0 <= x), lookup(x, keys), 0) != 0, 1, 0)
            for x in reversed(xs[start:start+5])]) <= 2)
    left, right = z3.And(*reference), z3.And(*reversed(candidate))
    result = check_equivalence(left, right, total_timeout_ms=None)
    assert result.equivalent is True
    assert result.left_only_conjuncts == result.right_only_conjuncts == 0
    assert result.common_conjuncts == 25
    assert result.finite_table_rewrites > 0
    equivalent(left, normalized(left))
    equivalent(right, normalized(right))


def test_duplicate_stores_obey_last_write_even_when_it_restores_default():
    x = z3.Int('shadow_table_x')
    array = z3.Store(z3.Store(z3.Store(z3.K(z3.IntSort(), 7), -3, 1), 5, 2), -3, 7)
    original = z3.Select(array, x)
    result = normalized(original)
    equivalent(original, result)
    assert result.eq(normalized(z3.If(x == 5, 2, 7)))


def test_outside_guard_and_nonzero_default_are_preserved():
    x = z3.Int('outside_table_x')
    original = z3.If(z3.And(x >= 0, x < 3), lookup(x, [0, 8]), 4)
    result = normalized(original)
    equivalent(original, result)
    assert z3.simplify(z3.substitute(result, (x, z3.IntVal(8)))).as_long() == 4
    assert z3.simplify(z3.substitute(result, (x, z3.IntVal(-1)))).as_long() == 4


def test_distinct_symbolic_indices_are_not_merged():
    x, y = z3.Ints('separate_table_x separate_table_y')
    original = z3.If(lookup(x, [1]) == lookup(y, [2]), 7, 9)
    result = normalized(original)
    equivalent(original, result)
    solver = z3.Solver()
    solver.add(x == 1, y == 0, result != 9)
    assert solver.check() == z3.unsat


def test_symbolic_store_and_whole_array_equality_remain_exact():
    x, value = z3.Ints('symbolic_store_x symbolic_store_value')
    array = z3.Store(z3.K(z3.IntSort(), 0), x, value)
    original = z3.And(array == z3.K(z3.IntSort(), 0), z3.Select(array, 3) == 1)
    equivalent(original, normalized(original))
    assert normalized(z3.Select(array, 3)).eq(z3.Select(array, 3))


def test_bound_bodies_and_annotations_remain_physically_unchanged():
    x = z3.Int('bound_table_x')
    original = z3.ForAll([x], lookup(x, [1, 3]) == indicator(x, [1, 3]))
    assert normalized(original).eq(original)


def test_size_threshold_falls_back_without_rejecting_or_truncating():
    x = z3.Int('large_table_x')
    original = lookup(x, [0, 1, 2, 3])
    assert normalized(original, max_table_entries=2).eq(original)
    equivalent(original, normalized(original, max_table_entries=2))
    interval = z3.And(x >= -100, x < 100)
    equivalent(interval, normalized(interval, max_table_entries=2))
    shared = x
    for _ in range(40):
        shared = shared + shared
    result = normalized(shared)
    equivalent(shared, result)
    seen, pending = set(), [result]
    while pending:
        node = pending.pop()
        if node.get_id() not in seen:
            seen.add(node.get_id())
            pending.extend(node.children())
    assert len(seen) < 100


def test_bool_tables_nondefault_context_and_negative_indices():
    ctx = z3.Context()
    x = z3.Int('bool_table_x', ctx=ctx)
    array = z3.Store(z3.K(z3.IntSort(ctx), z3.BoolVal(True, ctx)), -2, False)
    original = z3.Select(array, x)
    result = normalized(original)
    equivalent(original, result)
    # Compare canonical forms, not the incidental operand order of raw equality.
    assert result.eq(normalized(z3.Not(x == -2)))
    assert z3.is_false(z3.simplify(z3.substitute(result, (x, z3.IntVal(-2, ctx)))))
    for outside in (-3, 0):
        assert z3.is_true(z3.simplify(z3.substitute(result, (x, z3.IntVal(outside, ctx)))))


def test_deadline_returns_original_and_zero_budget_still_unknown():
    x = z3.Int('expired_table_x')
    original = lookup(x, [1, 2])
    result = normalize_finite_scalar_tables(original, deadline=time.monotonic()-1)
    assert not result.completed and result.formula.eq(original)
    result = check_equivalence(original == 1, indicator(x, [1, 2]) == 1, total_timeout_ms=0)
    assert result.status == 'unknown' and result.equivalent is None


def test_wrong_lookup_entry_still_has_a_counterexample():
    x = z3.Int('wrong_table_x')
    result = check_equivalence(lookup(x, [1, 2]) == 1, indicator(x, [1, 3]) == 1,
                               total_timeout_ms=2000)
    assert result.status == 'counterexample' and result.equivalent is False


def test_nested_tables_keep_multiple_outputs_and_unbounded_default():
    x = z3.Int('lazy_nested_table_x')
    array = z3.Store(z3.Store(z3.K(z3.IntSort(), 4), -3, 7), 5, 9)
    original = z3.If(z3.Or(x == -3, x == 5, x == 12),
                     z3.If(z3.Select(array, x) == 7, -11, z3.Select(array, x)), 6)
    expected = z3.If(x == -3, -11, z3.If(x == 5, 9, z3.If(x == 12, 4, 6)))
    actual = normalized(original)
    equivalent(original, actual)
    assert actual.eq(normalized(expected))
    for outside in (-1000, 0, 1000):
        assert z3.simplify(z3.substitute(actual, (x, z3.IntVal(outside)))).as_long() == 6


def test_boolean_and_integer_literals_do_not_share_a_cached_sort():
    ctx = z3.Context()
    x = z3.Int('lazy_mixed_sort_table_x', ctx=ctx)
    bool_array = z3.Store(z3.K(z3.IntSort(ctx), z3.BoolVal(False, ctx)), 1, True)
    int_array = z3.Store(z3.K(z3.IntSort(ctx), z3.IntVal(0, ctx)), 1, 1)
    original = z3.And(z3.Select(bool_array, x) == (z3.Select(int_array, x) == 1),
                      z3.If(z3.Select(bool_array, x), 1, 0) == z3.Select(int_array, x))
    actual = normalized(original)
    equivalent(original, actual)
    solver = z3.Solver(ctx=ctx)
    solver.add(z3.Not(actual))
    assert solver.check() == z3.unsat


def test_table_materializes_exactly_below_an_uninterpreted_parent():
    x, y = z3.Ints('lazy_function_table_x lazy_function_table_y')
    f = z3.Function('lazy_table_function', z3.IntSort(), z3.IntSort())
    original = f(z3.If(lookup(x, [-2, 4]) != 0, 3, 8)) == y
    expected = f(z3.If(z3.Or(x == -2, x == 4), 3, 8)) == y
    equivalent(original, normalized(original))
    assert normalized(original).eq(normalized(expected))


def test_shared_sliding_windows_and_cardinalities_match_in_one_traversal():
    xs = z3.IntVector('lazy_overlap_table_x', 32)
    keys = [-3, -1, 0, 3, 4, 8, 10, 11, 15]
    candidate_cells = [z3.If(z3.If(z3.And(x >= -3, x < 16),
                           lookup(x, keys), 0) != 0, 1, 0) for x in xs]
    reference_cells = [indicator(x, list(reversed(keys))) for x in xs]
    candidate = z3.And(*[z3.Sum(*reversed(candidate_cells[start:start+5])) <= 2
                          for start in reversed(range(28))],
                       z3.Sum(*reversed(candidate_cells)) == 12)
    reference = z3.And(*[z3.Sum(*reference_cells[start:start+5]) <= 2
                          for start in range(28)], z3.Sum(*reference_cells) == 12)
    # Keep the whole 32-coordinate sharing and matching check. Prove semantic
    # preservation compositionally rather than asking one XOR query to search
    # through all 32 independent literal arrays and overlapping windows.
    assert normalized(candidate).eq(normalized(reference))
    x = z3.Int('lazy_overlap_template_x')
    template = z3.If(z3.If(z3.And(x >= -3, x < 16), lookup(x, keys), 0) != 0, 1, 0)
    prove_instantiated_cell_rewrites(x, template, indicator(x, list(reversed(keys))),
                                    xs, candidate_cells, reference_cells)
    prove_count_congruence(len(xs),
        [(list(range(start, start+5)), 'le', 2) for start in range(28)]
        + [(list(range(len(xs))), 'eq', 12)])


def test_nary_distinct_remains_nary_after_child_tables_materialize():
    x = z3.Int('lazy_distinct_table_x')
    original = z3.Distinct(lookup(x, [1, 2]), lookup(x, [2, 3]), z3.IntVal(2))
    actual = normalized(original)
    equivalent(original, actual)
    assert z3.is_false(z3.simplify(z3.substitute(actual, (x, z3.IntVal(2)))))
    assert z3.is_true(z3.simplify(z3.substitute(actual, (x, z3.IntVal(1)))))


def test_real_table_values_are_not_coerced_to_integer_literals():
    x = z3.Int('lazy_real_table_x')
    array = z3.Store(z3.K(z3.IntSort(), z3.RealVal('1/3')), -2, z3.RealVal('2/3'))
    original = z3.Select(array, x)
    actual = normalized(original)
    equivalent(original, actual)
    assert actual.sort() == z3.RealSort()
    assert z3.simplify(z3.substitute(actual, (x, z3.IntVal(8)))).eq(z3.RealVal('1/3'))


def test_domain_bounds_match_when_grouped_beside_table_constraints():
    xs = z3.IntVector('lazy_domain_table_x', 8)
    keys = [0, 2, 3, 7, 10, 12, 16, 19, 21, 24]
    grouped_domains = [z3.And(x >= 0, x <= 24) for x in xs]
    flat_domains = [bound for x in xs for bound in (x >= 0, x <= 24)]
    candidate_cells = [z3.If(z3.If(z3.And(x >= 0, x < 25),
                            lookup(x, keys), 0) != 0, 1, 0) for x in xs]
    reference_cells = [indicator(x, keys) for x in xs]
    candidate = z3.And(*grouped_domains, z3.Sum(*reversed(candidate_cells)) <= 3)
    reference = z3.And(*flat_domains, z3.Sum(*reference_cells) <= 3)
    equivalent(z3.And(*grouped_domains), z3.And(*flat_domains))
    x = z3.Int('lazy_domain_template_x')
    template = z3.If(z3.If(z3.And(x >= 0, x < 25), lookup(x, keys), 0) != 0, 1, 0)
    prove_instantiated_cell_rewrites(x, template, indicator(x, keys),
                                    xs, candidate_cells, reference_cells)
    prove_count_congruence(len(xs), [(list(range(len(xs))), 'le', 3)])
    checked = check_equivalence(reference, candidate, total_timeout_ms=10000)
    assert checked.equivalent is True
    assert checked.left_only_conjuncts == checked.right_only_conjuncts == 0
    assert checked.common_conjuncts == 17


def test_standalone_interval_stays_compact_and_wrong_guard_still_fails():
    x = z3.Int('lazy_guard_default_x')
    bounds = z3.And(x >= -3, x < 25)
    assert normalized(bounds).eq(bounds)
    # Key 24 is outside this narrower guard. It must not be recovered merely
    # because the underlying literal array contains a one at that coordinate.
    candidate = z3.If(z3.And(x >= -3, x < 24), lookup(x, [-3, 24]), 0) == 1
    reference = z3.Or(x == -3, x == 24)
    checked = check_equivalence(reference, candidate, total_timeout_ms=2000)
    assert checked.equivalent is False and checked.status == 'counterexample'


def test_changed_window_bound_has_a_concrete_counterexample_after_rewriting():
    xs = z3.IntVector('mutated_window_table_x', 3)
    keys = [-3, -1, 0, 3, 4, 8, 10, 11, 15]
    cells = [z3.If(z3.If(z3.And(x >= -3, x < 16), lookup(x, keys), 0) != 0, 1, 0)
             for x in xs]
    correct = z3.Sum(*cells) <= 2
    mutated = z3.Sum(*cells) <= 3
    left, right = normalized(correct), normalized(mutated)
    assert not left.eq(right)
    solver = z3.Solver()
    solver.set(timeout=0)
    solver.add(*[x == -3 for x in xs], left != right)
    assert solver.check() == z3.sat
    model = solver.model()
    assert z3.is_false(model.eval(correct)) and z3.is_false(model.eval(left))
    assert z3.is_true(model.eval(mutated)) and z3.is_true(model.eval(right))
