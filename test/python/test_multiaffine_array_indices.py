"""Exact finite-read projection under original multivariate affine bounds."""
import pytest
import z3
from tools.semantic_checks.symbolic_array_projection import (
    _affine_index_domain, scalarize_symbolic_array_reads)


def test_marte_stride_enclosure():
    row, column = z3.Ints('row column')
    bounds = {row.get_id(): (row, 0, 4), column.get_id(): (column, 0, 24)}
    assert _affine_index_domain(75*row + 3*column + 2, bounds) == (2, 374, 3)


@pytest.mark.parametrize('scales,expected', [((3, 1), (0, 8, 1)), ((-3, 2), (-6, 4, 1)), ((4, 6), (0, 20, 2)), ((-4, -6), (-20, 0, 2))])
def test_signs_and_gcd_contain_every_index(scales, expected):
    x, y = z3.Ints('x y')
    bounds = {x.get_id(): (x, 0, 2), y.get_id(): (y, 0, 2)}
    domain = _affine_index_domain(scales[0]*x + scales[1]*y, bounds)
    assert domain == expected
    lower, upper, stride = domain
    for a in range(3):
        for b in range(3):
            value = scales[0]*a + scales[1]*b
            assert lower <= value <= upper and (value-lower) % stride == 0


def test_unbounded_term_does_not_acquire_a_domain():
    x, y = z3.Ints('x y')
    assert _affine_index_domain(3*x + y, {x.get_id(): (x, 0, 2)}) is None


def test_partial_bound_can_only_use_explicit_whole_index_domain():
    x, y = z3.Ints('x y')
    term = 3*x+y
    bounds = {x.get_id(): (x, 0, 2), term.get_id(): (term, 2, 9)}
    assert _affine_index_domain(term, bounds) == (2, 9, 1)


def test_nonlinear_index_is_not_treated_as_multiaffine():
    x, y = z3.Ints('x y')
    bounds = {x.get_id(): (x, 0, 2), y.get_id(): (y, 0, 2)}
    assert _affine_index_domain(x*y, bounds) is None


def test_explicit_bound_intersection_preserves_congruence():
    x, y = z3.Ints('x y')
    term = 6*x+4*y+1
    bounds = {x.get_id(): (x, 0, 2), y.get_id(): (y, 0, 2), term.get_id(): (term, 4, 18)}
    assert _affine_index_domain(term, bounds) == (5, 18, 2)


@pytest.mark.parametrize('complete', [False, True])
def test_only_complete_enclosure_coverage_eliminates_symbolic_cell(complete):
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    x, y, result = z3.Ints('x y result')
    # The image is {0,4,6,10}, but the certified enclosure also has {2,8}.
    keys = [0, 2, 4, 6, 8, 10] if complete else [0, 4, 6, 10]
    body = z3.And(x >= 0, x <= 1, y >= 0, y <= 1,
                  *(array[k] == k+3 for k in keys), result == array[4*x+6*y])
    projected = scalarize_symbolic_array_reads(body, [array])
    assert bool(projected.bounded_read_definitions) == complete
    target = z3.Exists(projected.private_variables, projected.body)
    expected = z3.And(x >= 0, x <= 1, y >= 0, y <= 1, result == 4*x+6*y+3)
    solver = z3.Solver()
    solver.add(z3.Xor(target, expected))
    assert solver.check() == z3.unsat


def test_correlated_indices_need_no_independence_assumption():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    x, y, result = z3.Ints('x y result')
    body = z3.And(x >= 0, x <= 2, y >= 0, y <= 2, x+y == 2,
                  *(array[k] == 2*k for k in range(9)), result == array[3*x+y])
    projection = scalarize_symbolic_array_reads(body, [array])
    assert len(projection.bounded_read_definitions) == 1
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2, x+y == 2, result == 2*(3*x+y))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.Exists(projection.private_variables, projection.body), expected))
    assert solver.check() == z3.unsat


def test_conditional_bounds_are_not_used_as_global_bounds():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    x, y, result = z3.Ints('x y result')
    guard = z3.Bool('guard')
    body = z3.And(z3.Implies(guard, z3.And(x >= 0, x <= 2, y >= 0, y <= 2)),
                  *(array[k] == k for k in range(9)), result == array[3*x+y])
    projection = scalarize_symbolic_array_reads(body, [array])
    assert not projection.bounded_read_definitions
