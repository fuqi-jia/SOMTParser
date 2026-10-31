"""Exact directional equivalence checks for projected relations."""
import unittest

import z3

from tools.semantic_checks.directional_equivalence import check_equivalence


class DirectionalEquivalenceTests(unittest.TestCase):
    def test_same_formula_with_quantified_structure_is_proved(self):
        x, y = z3.Ints("directional_same_x directional_same_y")
        hidden = z3.ForAll([x], z3.Implies(x == 2, y >= 0))
        formula = z3.And(hidden, y == 3)

        result = check_equivalence(formula, formula,
                                   total_timeout_ms=1000,
                                   per_obligation_timeout_ms=100)

        self.assertEqual(result.status, "equivalent")
        self.assertTrue(result.equivalent)
        self.assertEqual(result.left_only_conjuncts, 0)
        self.assertEqual(result.right_only_conjuncts, 0)

    def test_explicit_context_true_and_false_constants(self):
        ctx = z3.Context()
        true = z3.BoolVal(True, ctx=ctx)
        false = z3.BoolVal(False, ctx=ctx)

        self.assertTrue(check_equivalence(true, true, total_timeout_ms=1000).equivalent)
        self.assertTrue(check_equivalence(false, false, total_timeout_ms=1000).equivalent)
        self.assertFalse(check_equivalence(false, true, total_timeout_ms=1000).equivalent)

    def test_objective_only_difference_returns_counterexample(self):
        x, cost = z3.Ints("directional_objective_x directional_cost")
        constraints = x >= 0
        left = z3.And(constraints, cost == x)
        right = z3.And(constraints, cost == x + 1)

        result = check_equivalence(left, right,
                                   total_timeout_ms=2000,
                                   per_obligation_timeout_ms=500)

        self.assertEqual(result.status, "counterexample")
        self.assertFalse(result.equivalent)
        self.assertTrue(result.left_implies_right.counterexample_model
                        or result.right_implies_left.counterexample_model)

    def test_hidden_quantifier_is_kept_in_the_relation(self):
        bound, observed = z3.Ints("directional_bound directional_observed")
        hidden_quantifier = z3.ForAll(
            [bound], z3.Implies(bound == 3, observed == 0))
        left = z3.And(hidden_quantifier, observed == 0)
        right = z3.And(hidden_quantifier, observed == 1)

        result = check_equivalence(left, right,
                                   total_timeout_ms=2000,
                                   per_obligation_timeout_ms=1000)

        self.assertEqual(result.status, "counterexample")
        self.assertFalse(result.equivalent)
        self.assertEqual(result.left_implies_right.proved, 0)
        self.assertIsNotNone(result.left_implies_right.counterexample_model)

    def test_common_contradiction_makes_both_relations_empty(self):
        x, y = z3.Ints("directional_conflict_x directional_conflict_y")
        contradiction = [x == 0, x == 1]
        left = z3.And(*(contradiction + [y == 2]))
        right = z3.And(*(contradiction + [y == 9]))

        result = check_equivalence(left, right,
                                   total_timeout_ms=2000,
                                   per_obligation_timeout_ms=500,
                                   simplify=False)

        self.assertEqual(result.status, "equivalent")
        self.assertTrue(result.equivalent)
        self.assertGreaterEqual(result.common_conjuncts, 2)

    def test_exhausted_total_budget_stays_unknown(self):
        x = z3.Int("directional_budget_x")
        result = check_equivalence(x == 0, x == 1,
                                   total_timeout_ms=0,
                                   per_obligation_timeout_ms=10,
                                   simplify=False)

        self.assertEqual(result.status, "unknown")
        self.assertIsNone(result.equivalent)
        self.assertEqual(result.left_implies_right.unknown_obligations, 1)
        self.assertEqual(result.right_implies_left.unknown_obligations, 1)

        same = check_equivalence(x == 0, x == 0, total_timeout_ms=0,
                                 per_obligation_timeout_ms=10, simplify=False)
        self.assertEqual(same.status, "unknown")
        self.assertIsNone(same.equivalent)

    def test_timeout_arguments_must_be_finite_integers(self):
        x = z3.Int("directional_timeout_type")
        for value in (1.5, float("nan"), float("inf"), True):
            with self.subTest(value=value):
                with self.assertRaises(TypeError):
                    check_equivalence(x == 0, x == 0,
                                      total_timeout_ms=value)

    def test_early_counterexample_reports_remaining_obligations(self):
        x, y, z = z3.Ints("directional_early_x directional_early_y directional_early_z")
        left = z3.And(x == 0, y == 0, z == 0)
        right = z3.And(x == 0, y == 1, z == 2)

        result = check_equivalence(left, right, total_timeout_ms=2000,
                                   per_obligation_timeout_ms=500,
                                   simplify=False)

        self.assertEqual(result.status, "counterexample")
        direction = result.left_implies_right
        self.assertEqual(direction.obligations, 2)
        self.assertEqual(direction.not_run_obligations, 1)


if __name__ == "__main__":
    unittest.main()
