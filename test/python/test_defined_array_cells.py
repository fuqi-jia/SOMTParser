"""Differential obligations for the concrete-cell elimination draft.

Run in the root's chosen Z3 Python environment. These tests are not executed
by the static review task.
"""
import unittest

import z3

from tools.semantic_checks.defined_array_cells import eliminate_defined_array_cells
from tools.semantic_checks.projection import existential_projection, free_constants


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.set(timeout=5000)
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


class DefinitionalArrayCellTests(unittest.TestCase):
    def test_duplicate_definitions_preserve_their_consistency_constraint(self):
        array = z3.Array("hidden_degree", z3.IntSort(), z3.IntSort())
        x, y = z3.Ints("degree_x degree_y")
        cell0, cell1 = z3.Select(array, 0), z3.Select(array, 1)
        body = z3.And(cell0 == x + 1, cell0 == y, cell1 == x,
                      cell0 >= 0, cell1 <= 10)

        result = eliminate_defined_array_cells(body, [array])
        expected = z3.Exists([array], body)

        self.assertEqual(result.eliminated_roots, ("hidden_degree",))
        self.assertEqual(result.definition_counts, (("hidden_degree", 2),))
        self.assertFalse(any(c.get_id() == array.get_id()
                             for c in free_constants([result.body])))
        self.assertTrue(equivalent(expected, result.body))

    def test_nested_array_concrete_index_tuples_are_distinct_cells(self):
        inner = z3.ArraySort(z3.IntSort(), z3.IntSort())
        matrix = z3.Array("hidden_nested", z3.IntSort(), inner)
        x, y = z3.Ints("nested_x nested_y")
        cell01 = z3.Select(z3.Select(matrix, 0), 1)
        cell10 = z3.Select(z3.Select(matrix, 1), 0)
        body = z3.And(cell01 == x, cell10 == y,
                      cell01 + cell10 >= 0)

        result = eliminate_defined_array_cells(body, [matrix])
        self.assertEqual(result.definition_counts, (("hidden_nested", 2),))
        # Constructive elimination proof: necessity for every original array,
        # and an explicit total-array witness for every projected assignment.
        zero_row = z3.K(z3.IntSort(), z3.IntVal(0))
        witness = z3.Store(z3.Store(z3.K(z3.IntSort(), zero_row),
                                   0, z3.Store(zero_row, 1, x)),
                           1, z3.Store(zero_row, 0, y))
        instantiated = z3.substitute(body, (matrix, witness))
        self.assertTrue(equivalent(result.body, x + y >= 0))
        self.assertTrue(equivalent(z3.Implies(body, result.body), z3.BoolVal(True)))
        self.assertTrue(equivalent(z3.Implies(result.body, instantiated), z3.BoolVal(True)))

    def test_symbolic_read_refuses_the_entire_group(self):
        array = z3.Array("partly_defined", z3.IntSort(), z3.IntSort())
        index, value = z3.Ints("symbolic_index defined_value")
        body = z3.And(z3.Select(array, 0) == value,
                      z3.Select(array, index) >= 0)

        result = eliminate_defined_array_cells(body, [array])
        self.assertEqual(result.retained_roots, ("partly_defined",))
        self.assertTrue(result.body.eq(body))

    def test_self_dependent_definition_is_not_used(self):
        array = z3.Array("cyclic_cells", z3.IntSort(), z3.IntSort())
        value = z3.Int("cycle_value")
        body = z3.And(z3.Select(array, 0) == z3.Select(array, 1),
                      z3.Select(array, 1) == value)

        result = eliminate_defined_array_cells(body, [array])
        self.assertEqual(result.retained_roots, ("cyclic_cells",))
        self.assertTrue(result.body.eq(body))

    def test_definition_nested_under_disjunction_is_not_promoted(self):
        array = z3.Array("conditional_def", z3.IntSort(), z3.IntSort())
        guard = z3.Bool("definition_guard")
        value = z3.Int("definition_value")
        # The conditional body is not an unconditional top-level definition.
        body = z3.Or(z3.And(guard, z3.Select(array, 0) == 1),
                     z3.Select(array, 0) == value)

        result = eliminate_defined_array_cells(body, [array])
        self.assertEqual(result.retained_roots, ("conditional_def",))
        self.assertTrue(result.body.eq(body))



    def test_unmentioned_or_whole_array_reads_block_elimination(self):
        a = z3.Array('missing_a', z3.IntSort(), z3.IntSort())
        b = z3.Array('whole_b', z3.IntSort(), z3.IntSort())
        value = z3.Int('missing_value')
        for body in [z3.And(a[0] == value, a[1] >= 0),
                     z3.And(a[0] == value, a == b)]:
            result = eliminate_defined_array_cells(body, [a])
            self.assertTrue(result.body.eq(body))
            self.assertEqual(result.retained_roots, ('missing_a',))

    def test_complete_candidate_projection_preserves_free_observations_and_cost(self):
        from tools.semantic_checks.checker_adapter import candidate_projection
        matrix = z3.Array('visible_matrix', z3.IntSort(), z3.BoolSort())
        degree = z3.Array('private_degree', z3.IntSort(), z3.IntSort())
        obs = [z3.Bool('visible_0'), z3.Bool('visible_1')]
        cost = z3.Real('free_cost')
        assertions = [degree[0] == z3.If(matrix[0], 1, 0) + z3.If(matrix[1], 1, 0),
                      degree[0] >= 1]
        observations = [(obs[i], matrix[i]) for i in range(2)]
        result = candidate_projection(assertions, observations, (cost, degree[0]))
        self.assertEqual(set(result.optimization.eliminated_array_roots),
                         {'visible_matrix', 'private_degree'})
        expected = z3.And(z3.Or(*obs), cost == z3.If(obs[0], 1, 0) + z3.If(obs[1], 1, 0))
        self.assertTrue(equivalent(expected, result.formula))

    def test_acyclic_array_dependencies(self):
        a = z3.Array('acyclic_a', z3.IntSort(), z3.IntSort())
        b = z3.Array('acyclic_b', z3.IntSort(), z3.IntSort())
        value = z3.Int('acyclic_value')
        body = z3.And(a[0] == b[0] + 1, b[0] == value, a[0] > 0)
        result = eliminate_defined_array_cells(body, [a, b])
        self.assertEqual(set(result.eliminated_roots), {'acyclic_a', 'acyclic_b'})
        zero = z3.K(z3.IntSort(), z3.IntVal(0))
        instantiated = z3.substitute(body, (a, z3.Store(zero, 0, value + 1)),
                                    (b, z3.Store(zero, 0, value)))
        self.assertTrue(equivalent(result.body, value + 1 > 0))
        self.assertTrue(equivalent(z3.Implies(body, result.body), z3.BoolVal(True)))
        self.assertTrue(equivalent(z3.Implies(result.body, instantiated), z3.BoolVal(True)))

    def test_quantifiers_are_rejected_before_substitution(self):
        a = z3.Array('quantified_aux', z3.IntSort(), z3.IntSort())
        i = z3.Int('quantified_index')
        with self.assertRaises(ValueError):
            eliminate_defined_array_cells(z3.ForAll([i], a[i] == i), [a])


if __name__ == "__main__":
    unittest.main()
