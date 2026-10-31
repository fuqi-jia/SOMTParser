"""Semantic differentials for hidden-array ground-read scalarization."""
import unittest

import z3

from tools.semantic_checks.checker_adapter import candidate_projection
from tools.semantic_checks.finite_array_reads import scalarize_finite_array_reads
from tools.semantic_checks.projection import existential_projection


def equivalent(left, right, timeout_ms=5000):
    solver = z3.Solver(ctx=left.ctx)
    solver.set(timeout=timeout_ms)
    solver.add(z3.Xor(left, right))
    return solver.check()


def array_constants(expr):
    from tools.semantic_checks.projection import free_constants
    return [constant for constant in free_constants([expr])
            if constant.sort().kind() == z3.Z3_ARRAY_SORT]


class FiniteArrayReadProjectionTests(unittest.TestCase):
    def test_repeated_one_dimensional_cell_preserves_existential_relation(self):
        array = z3.Array("ground_repeat", z3.IntSort(), z3.IntSort())
        x, y = z3.Ints("ground_repeat_x ground_repeat_y")
        body = z3.And(array[0] == x, array[0] == y, array[1] >= 0)

        result = scalarize_finite_array_reads(body, [array])
        original = existential_projection(body, [x, y])
        projected = existential_projection(result.body, [x, y])

        self.assertEqual(result.eliminated_roots, ("ground_repeat",))
        self.assertEqual(result.cell_counts, (("ground_repeat", 2),))
        self.assertEqual(array_constants(result.body), [])
        self.assertEqual(equivalent(original, projected), z3.unsat)
        solver = z3.Solver()
        solver.add(projected, x != y)
        self.assertEqual(solver.check(), z3.unsat)

    def test_checker_projection_hides_fresh_cell_witnesses_after_scalarization(self):
        array = z3.Array("checker_hidden_cells", z3.IntSort(), z3.IntSort())
        x, y = z3.Ints("checker_output_x checker_output_y")
        alias_x, alias_y = z3.Ints("checker_alias_x checker_alias_y")
        assertions = [array[0] == x, array[0] == y, array[1] >= 0]

        result = candidate_projection(
            assertions, [(alias_x, x), (alias_y, y)])

        self.assertIn("checker_hidden_cells",
                      result.optimization.eliminated_array_roots)
        self.assertEqual(result.optimization.finite_array_read_cells, 2)
        self.assertEqual(array_constants(result.formula), [])
        self.assertEqual(equivalent(result.formula, alias_x == alias_y), z3.unsat)

    def test_nested_two_dimensional_cells_project_exactly(self):
        inner = z3.ArraySort(z3.IntSort(), z3.IntSort())
        matrix = z3.Array("ground_matrix", z3.IntSort(), inner)
        x, y, repeated = z3.Ints("matrix_x matrix_y matrix_repeated")
        cell01 = matrix[0][1]
        cell10 = matrix[1][0]
        body = z3.And(cell01 == x, cell01 == repeated, cell10 == y,
                      x + y >= 0)

        result = scalarize_finite_array_reads(body, [matrix])

        self.assertEqual(result.cell_counts, (("ground_matrix", 2),))
        self.assertEqual(array_constants(result.body), [])
        # Z3 is incomplete for this nested-array existential XOR. Prove the
        # projection exactly through both constructive directions instead:
        # any matrix supplies its read values, and any scalar tuple extends to
        # the displayed total nested-array Store witness.
        cell_values = {old.get_id(): witness
                       for old, witness in result.substitutions}
        mapped_back = z3.substitute(
            result.body,
            *((witness, old) for old, witness in result.substitutions))
        self.assertEqual(equivalent(body, mapped_back), z3.unsat)

        default_row = z3.K(z3.IntSort(), z3.IntVal(0))
        matrix_witness = z3.Store(
            z3.Store(z3.K(z3.IntSort(), default_row), 0,
                     z3.Store(default_row, 1, cell_values[cell01.get_id()])),
            1, z3.Store(default_row, 0, cell_values[cell10.get_id()]))
        instantiated_original = z3.substitute(body, (matrix, matrix_witness))
        self.assertEqual(equivalent(instantiated_original, result.body), z3.unsat)
        # These two implications witness the same free-coordinate relation:
        # projecting an array yields a cell tuple, and every tuple has a total
        # array extension with the required cells.
        visible_projection = existential_projection(result.body,
                                                    [x, y, repeated])
        solver = z3.Solver()
        solver.add(visible_projection, x != repeated)
        self.assertEqual(solver.check(), z3.unsat)

    def test_fixed_out_of_shape_cell_is_a_distinct_preserved_coordinate(self):
        array = z3.Array("ground_oob", z3.IntSort(), z3.IntSort())
        x, y = z3.Ints("oob_x oob_y")
        body = z3.And(array[0] == x, array[99] == y)

        result = scalarize_finite_array_reads(body, [array])
        original = existential_projection(body, [x, y])
        projected = existential_projection(result.body, [x, y])

        self.assertEqual(result.cell_counts, (("ground_oob", 2),))
        self.assertEqual(equivalent(original, projected), z3.unsat)
        solver = z3.Solver()
        solver.add(projected, x == 1, y == 2)
        self.assertEqual(solver.check(), z3.sat)

    def test_dynamic_read_retains_the_whole_array_group(self):
        array = z3.Array("dynamic_read", z3.IntSort(), z3.IntSort())
        index, value = z3.Ints("dynamic_index dynamic_value")
        body = z3.And(array[0] == value, array[index] >= 0)

        result = scalarize_finite_array_reads(body, [array])
        self.assertTrue(result.body.eq(body))
        self.assertEqual(result.eliminated_roots, ())
        self.assertEqual(result.retained_roots, ("dynamic_read",))
        self.assertEqual(len(array_constants(result.body)), 1)

    def test_quantified_array_read_retains_the_whole_array_group(self):
        array = z3.Array("quantified_read", z3.IntSort(), z3.IntSort())
        index = z3.Int("quantified_read_index")
        body = z3.ForAll([index], z3.Implies(
            z3.And(0 <= index, index < 3), array[index] == index))

        result = scalarize_finite_array_reads(body, [array])
        self.assertTrue(result.body.eq(body))
        self.assertEqual(result.retained_roots, ("quantified_read",))
        self.assertEqual(len(array_constants(result.body)), 1)

    def test_whole_array_comparison_retains_the_root(self):
        a = z3.Array("whole_read_a", z3.IntSort(), z3.IntSort())
        b = z3.Array("whole_read_b", z3.IntSort(), z3.IntSort())
        body = z3.And(a[0] >= 0, a == b)

        result = scalarize_finite_array_reads(body, [a])
        self.assertTrue(result.body.eq(body))
        self.assertEqual(result.retained_roots, ("whole_read_a",))
        self.assertEqual(len(array_constants(result.body)), 2)

    def test_store_use_retains_the_root(self):
        array = z3.Array("stored_read", z3.IntSort(), z3.IntSort())
        body = z3.Select(z3.Store(array, 0, 7), 0) == 7

        result = scalarize_finite_array_reads(body, [array])
        self.assertTrue(result.body.eq(body))
        self.assertEqual(result.retained_roots, ("stored_read",))
        self.assertEqual(len(array_constants(result.body)), 1)

    def test_observed_cells_keep_bridge_and_project_the_full_relation(self):
        array = z3.Array("observed_partial", z3.IntSort(), z3.IntSort())
        visible = z3.Int("observed_partial_alias")
        body = z3.And(array[0] == 3, array[1] >= 0)

        result = candidate_projection([body], [(visible, array[0])])

        self.assertEqual(result.optimization.finite_array_read_cells, 2)
        self.assertIn("observed_partial", result.optimization.eliminated_array_roots)
        self.assertEqual(array_constants(result.optimization.body), [])
        expected = z3.Exists([array], z3.And(visible == array[0], array[0] == 3,
                                             array[1] >= 0))
        self.assertEqual(equivalent(expected, result.formula), z3.unsat)
        self.assertEqual(equivalent(result.formula, visible == 3), z3.unsat)

    def test_existing_definition_elimination_runs_before_finite_read_witnesses(self):
        array = z3.Array("definition_before_cells", z3.IntSort(), z3.IntSort())
        visible = z3.Int("definition_before_cells_alias")
        assertions = [array[0] == 3, array[1] == 7]

        result = candidate_projection(assertions, [(visible, array[0])])

        self.assertIn("definition_before_cells",
                      result.optimization.eliminated_array_roots)
        self.assertNotIn("definition_before_cells",
                         result.optimization.retained_array_roots)
        self.assertEqual(result.optimization.finite_array_read_cells, 0)
        self.assertEqual(equivalent(result.formula, visible == 3), z3.unsat)

    def test_explicitly_visible_array_root_is_not_touched(self):
        array = z3.Array("observable_root", z3.IntSort(), z3.IntSort())
        body = array[0] == 9
        result = scalarize_finite_array_reads(
            body, [array], visible_roots=[array])
        self.assertTrue(result.body.eq(body))
        self.assertEqual(result.eliminated_roots, ())
        self.assertEqual(result.retained_roots, ("observable_root",))


if __name__ == "__main__":
    unittest.main()
