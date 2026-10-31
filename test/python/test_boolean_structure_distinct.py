"""Whole formulas preserve DISTINCT semantics across frontend operand order."""
import pytest
import z3

from tools.semantic_checks.boolean_structure import structural_equivalence


def sort_for(name):
    return {'int': z3.IntSort, 'real': z3.RealSort, 'bool': z3.BoolSort,
            'bv': lambda: z3.BitVecSort(9),
            'array': lambda: z3.ArraySort(z3.IntSort(), z3.IntSort()),
            'uninterpreted': lambda: z3.DeclareSort('DistinctElement'),
            'float': z3.Float32}[name]()


@pytest.mark.parametrize('name', ['int', 'real', 'bool', 'bv', 'array', 'uninterpreted', 'float'])
def test_permuted_distinct_is_a_sufficient_proof_for_each_sort(name):
    a, b, c = z3.Consts('distinct_a distinct_b distinct_c', sort_for(name))
    left, right = z3.Distinct(a, b, c), z3.Distinct(c, a, b)
    assert structural_equivalence(left, right)['equivalent']
    solver = z3.Solver(); solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('mutation', ['drop-duplicate', 'drop-coordinate', 'different-coordinate'])
def test_operand_changes_are_not_accepted_as_permutations(mutation):
    a, b, c, d = z3.Ints('distinct_a distinct_b distinct_c distinct_d')
    if mutation == 'drop-duplicate':
        left, right = z3.Distinct(a, a, b), z3.Distinct(a, b)
    elif mutation == 'drop-coordinate':
        left, right = z3.Distinct(a, b, c), z3.Distinct(a, b)
    else:
        left, right = z3.Distinct(a, b, c), z3.Distinct(a, b, d)
    assert not structural_equivalence(left, right)['equivalent']
    solver = z3.Solver(); solver.add(z3.Xor(left, right))
    assert solver.check() == z3.sat


def test_order_change_inside_binder_preserves_guard_and_free_coordinate():
    i, j, p = z3.Ints('distinct_i distinct_j distinct_public')
    guard = z3.And(i == 0, j == 1)
    left = z3.ForAll([i, j], z3.Implies(guard, z3.Distinct(i, j, p)))
    right = z3.ForAll([i, j], z3.Implies(guard, z3.Distinct(p, i, j)))
    changed = z3.ForAll([i, j], z3.Implies(z3.And(i == 0, j == 2), z3.Distinct(p, i, j)))
    assert structural_equivalence(left, right)['equivalent']
    assert not structural_equivalence(left, changed)['equivalent']
    solver = z3.Solver(); solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat
    solver = z3.Solver(); solver.add(z3.Xor(left, changed))
    assert solver.check() == z3.sat


def test_complete_relation_keeps_domains_and_signed_cost_observation():
    a, b, c, cost = z3.Ints('distinct_a distinct_b distinct_c distinct_cost')
    bounds = z3.And(a >= -2, a <= 3, b >= -2, b <= 3, c >= -2, c <= 3)
    signed_cost = cost == -(3*a - 2*b + c + 7)
    left = z3.And(bounds, z3.Distinct(a, b, c), signed_cost)
    right = z3.And(z3.Distinct(c, a, b), signed_cost, bounds)
    assert structural_equivalence(left, right)['equivalent']
    changed = z3.And(bounds, z3.Distinct(c, a, b), cost == 3*a - 2*b + c + 7)
    assert not structural_equivalence(left, changed)['equivalent']
    solver = z3.Solver(); solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat
    solver = z3.Solver(); solver.add(z3.Xor(left, changed))
    assert solver.check() == z3.sat
