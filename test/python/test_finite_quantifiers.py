"""Differential checks for finite_quantifier_expansion.py.

Run with the root checker's pinned Z3 Python environment. These deliberately
use solver equivalence obligations rather than inspecting generated syntax.
"""
import unittest

import z3

from tools.semantic_checks.finite_quantifiers import expand_finite_int_quantifiers


def array_constants(expr):
    from tools.semantic_checks.projection import free_constants
    return [constant for constant in free_constants([expr])
            if constant.sort().kind() == z3.Z3_ARRAY_SORT]


def equivalent(left, right, timeout_ms=5000):
    solver = z3.Solver(ctx=left.ctx)
    solver.set(timeout=timeout_ms)
    solver.add(z3.Xor(left, right))
    return solver.check()


class FiniteExpansionTests(unittest.TestCase):
    def test_forall_multivariable_pairwise_bounds(self):
        x, y, g, h = z3.Ints("x y g h")
        guard = z3.And(0 <= x, x < 4, x < y, y < 4,
                       0 <= g, g < h, h < 3)
        original = z3.ForAll([x, y, g, h], z3.Implies(guard, x + g <= y + h))
        result = expand_finite_int_quantifiers(original)
        self.assertEqual(result.stats.expanded_quantifiers, 1)
        self.assertEqual(result.stats.skipped_quantifiers, 0)
        self.assertEqual(equivalent(original, result.formula), z3.unsat)

    def test_exists_and_guard_with_reversed_comparisons(self):
        x = z3.Int("exists_x")
        original = z3.Exists([x], z3.And(3 > x, 0 <= x, x != 2))
        result = expand_finite_int_quantifiers(original)
        self.assertEqual(result.stats.expanded_quantifiers, 1)
        self.assertEqual(equivalent(original, result.formula), z3.unsat)

    def test_nested_quantifier_does_not_capture_outer_value(self):
        x, y = z3.Ints("outer_x inner_y")
        inner = z3.Exists([y], z3.And(0 <= y, y < 3, y != x))
        original = z3.ForAll([x], z3.Implies(z3.And(0 <= x, x < 3), inner))
        result = expand_finite_int_quantifiers(original)
        self.assertEqual(result.stats.expanded_quantifiers, 4)
        self.assertEqual(equivalent(original, result.formula), z3.unsat)

    def test_empty_guard_interval_has_correct_identity(self):
        x = z3.Int("empty_x")
        impossible = z3.And(x >= 0, x < 0)
        forall = z3.ForAll([x], z3.Implies(impossible, x == 7))
        exists = z3.Exists([x], z3.And(impossible, x == 7))
        forall_result = expand_finite_int_quantifiers(forall)
        exists_result = expand_finite_int_quantifiers(exists)
        self.assertEqual(equivalent(forall, forall_result.formula), z3.unsat)
        self.assertEqual(equivalent(exists, exists_result.formula), z3.unsat)

    def test_unbounded_and_non_int_quantifiers_are_preserved(self):
        x = z3.Int("unbounded_x")
        unsupported = z3.ForAll([x], x >= 0)
        result = expand_finite_int_quantifiers(unsupported)
        self.assertTrue(result.formula.eq(unsupported))
        self.assertEqual(result.stats.skipped_quantifiers, 1)
        b = z3.Bool("bound_bool")
        non_int = z3.ForAll([b], z3.Implies(b, b))
        non_int_result = expand_finite_int_quantifiers(non_int)
        self.assertTrue(non_int_result.formula.eq(non_int))

    def test_budget_exhaustion_returns_whole_original_formula(self):
        x, y = z3.Ints("budget_x budget_y")
        qx = z3.ForAll([x], z3.Implies(z3.And(0 <= x, x < 2), x == x))
        qy = z3.ForAll([y], z3.Implies(z3.And(0 <= y, y < 2), y == y))
        formula = z3.And(qx, qy)
        result = expand_finite_int_quantifiers(formula, max_enumerated_tuples=3)
        self.assertTrue(result.stats.budget_exhausted)
        self.assertTrue(result.formula.eq(formula))

    def test_nested_instances_are_reserved_against_one_budget(self):
        x, y = z3.Ints("reserved_outer reserved_inner")
        inner = z3.Exists([y], z3.And(0 <= y, y < 4, y != x))
        formula = z3.ForAll(
            [x], z3.Implies(z3.And(0 <= x, x < 3), inner))
        result = expand_finite_int_quantifiers(
            formula, max_emitted_instances=5)
        self.assertTrue(result.stats.budget_exhausted)
        self.assertTrue(result.formula.eq(formula))

    def test_large_integer_width_is_budgeted_without_len_range_overflow(self):
        x = z3.Int("very_wide")
        upper = 2 ** 100
        formula = z3.ForAll(
            [x], z3.Implies(z3.And(0 <= x, x < upper), x == x))
        result = expand_finite_int_quantifiers(formula)
        self.assertTrue(result.stats.budget_exhausted)
        self.assertTrue(result.formula.eq(formula))

    def test_empty_dimension_short_circuits_huge_cartesian_product(self):
        x, y = z3.Ints("empty_dimension huge_dimension")
        upper = 2 ** 100
        empty_guard = z3.And(x >= 0, x < 0, y >= 0, y < upper)
        forall = z3.ForAll([x, y], z3.Implies(empty_guard, y == 0))
        exists = z3.Exists([x, y], z3.And(empty_guard, y == 0))

        forall_result = expand_finite_int_quantifiers(forall)
        exists_result = expand_finite_int_quantifiers(exists)

        self.assertFalse(forall_result.stats.budget_exhausted)
        self.assertFalse(exists_result.stats.budget_exhausted)
        self.assertEqual(forall_result.stats.expanded_quantifiers, 1)
        self.assertEqual(exists_result.stats.expanded_quantifiers, 1)
        self.assertTrue(z3.is_true(forall_result.formula))
        self.assertTrue(z3.is_false(exists_result.formula))

    def test_repeated_quantifier_dag_is_expanded_once(self):
        # The same source AST is visited twice. Its cache entry must remain
        # stable while the original input DAG owns that AST; the implementation
        # also retains source nodes for temporary instantiated DAG entries.
        x = z3.Int("shared_x")
        q = z3.ForAll([x], z3.Implies(z3.And(0 <= x, x < 2), x >= 0))
        formula = z3.Or(q, q)
        result = expand_finite_int_quantifiers(formula)
        self.assertEqual(result.stats.expanded_quantifiers, 1)
        self.assertEqual(equivalent(formula, result.formula), z3.unsat)

    def test_empty_expansions_preserve_nondefault_context(self):
        ctx = z3.Context()
        x = z3.Int("context_x", ctx=ctx)
        impossible = z3.And(x >= 0, x < 0)
        forall = z3.ForAll([x], z3.Implies(impossible, x == 1))
        exists = z3.Exists([x], z3.And(impossible, x == 1))
        forall_result = expand_finite_int_quantifiers(forall)
        exists_result = expand_finite_int_quantifiers(exists)
        self.assertEqual(forall_result.formula.ctx, ctx)
        self.assertEqual(exists_result.formula.ctx, ctx)
        self.assertTrue(z3.is_true(forall_result.formula))
        self.assertTrue(z3.is_false(exists_result.formula))





class FiniteProjectionSemanticsTests(unittest.TestCase):
    def test_distinct_domains_and_nontrivial_array_relation(self):
        x, y = z3.Ints('distinct_x distinct_y')
        a = z3.Array('distinct_a', z3.IntSort(), z3.IntSort())
        original = z3.ForAll([x, y], z3.Implies(
            z3.And(-2 <= x, x < 0, 3 <= y, y <= 4), a[x + y] == x - y))
        result = expand_finite_int_quantifiers(original)
        self.assertEqual(result.stats.expanded_instances, 4)
        self.assertEqual(equivalent(original, result.formula), z3.unsat)
        self.assertEqual(equivalent(result.formula,
            z3.And(*[a[i+j] == i-j for i in [-2, -1] for j in [3, 4]])), z3.unsat)

    def test_nested_capture_with_free_array_values(self):
        x, y = z3.Ints('capture_x capture_y')
        a = z3.Array('capture_a', z3.IntSort(), z3.IntSort())
        inner = z3.Exists([y], z3.And(0 <= y, y < 3, y != x, a[x] == y))
        original = z3.ForAll([x], z3.Implies(z3.And(0 <= x, x < 2), inner))
        result = expand_finite_int_quantifiers(original)
        self.assertEqual(equivalent(original, result.formula), z3.unsat)
        self.assertEqual(equivalent(result.formula,
            z3.And(z3.Or(a[0] == 1, a[0] == 2), z3.Or(a[1] == 0, a[1] == 2))), z3.unsat)

    def test_residual_free_guard_is_not_dropped(self):
        x = z3.Int('residual_x')
        enabled = z3.Bool('enabled')
        a = z3.Array('residual_a', z3.IntSort(), z3.IntSort())
        original = z3.ForAll([x], z3.Implies(z3.And(0 <= x, x < 2, enabled), a[x] > 0))
        result = expand_finite_int_quantifiers(original)
        self.assertEqual(equivalent(original, result.formula), z3.unsat)
        self.assertEqual(equivalent(result.formula,
            z3.Implies(enabled, z3.And(a[0] > 0, a[1] > 0))), z3.unsat)

    def test_array_projection_eliminates_only_fully_observed_roots(self):
        from tools.semantic_checks.checker_adapter import candidate_projection
        from tools.semantic_checks.projection import existential_projection
        x = z3.Int('projection_x')
        a = z3.Array('projection_a', z3.IntSort(), z3.IntSort())
        q = z3.ForAll([x], z3.Implies(z3.And(0 <= x, x < 2), a[x] > x))
        obs = [z3.Int('fresh_projection_0'), z3.Int('fresh_projection_1')]
        bridges = [(obs[i], a[i]) for i in range(2)]
        result = candidate_projection([q], bridges)
        self.assertEqual(result.optimization.eliminated_array_roots, ('projection_a',))
        self.assertEqual(result.optimization.quantifier_expansion.expanded_quantifiers, 1)
        self.assertEqual(equivalent(result.formula, z3.And(obs[0] > 0, obs[1] > 1)), z3.unsat)
        partial = candidate_projection([q], bridges[:1])
        self.assertEqual(partial.optimization.eliminated_array_roots, ('projection_a',))
        self.assertEqual(partial.optimization.finite_array_read_cells, 2)
        self.assertEqual(array_constants(partial.optimization.body), [])
        self.assertEqual(equivalent(partial.formula, obs[0] > 0), z3.unsat)

    def test_unbounded_quantifier_stays_visible_in_projection_diagnostics(self):
        from tools.semantic_checks.checker_adapter import candidate_projection
        x = z3.Int('unbounded_projection_x')
        a = z3.Array('unbounded_projection_a', z3.IntSort(), z3.IntSort())
        q = z3.ForAll([x], a[x] > x)
        obs = z3.Int('unbounded_projection_obs')
        result = candidate_projection([q], [(obs, a[0])])
        self.assertTrue(result.optimization.skipped_quantifier_context)
        self.assertEqual(result.optimization.quantifier_expansion.expanded_quantifiers, 0)
