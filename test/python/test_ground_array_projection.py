"""Complete relation checks for finite reads of existential arrays."""
import pytest
import z3

from tools.semantic_checks.ground_array_projection import (
    UnsupportedArrayProjection,
    scalarize_ground_array_reads,
)


def close(variables, body):
    return z3.Exists(variables, body) if variables else body


def check_equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def check_projection(body, private):
    result = scalarize_ground_array_reads(body, private)
    check_equivalent(close(private, body), close(result.private_variables, result.body))
    return result


@pytest.mark.parametrize('index', [-100, 0, 1, 10**50])
def test_domain_and_signed_cost_over_all_observations(index):
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    x, y, cost = z3.Ints('x y cost')
    left, right = z3.Select(a, index), z3.Select(a, index + 1)
    body = z3.And(x == left, y == right, left >= 1, left <= 7,
                  right > left, cost == -3 * left + 2 * right)
    result = check_projection(body, [a])
    assert len(result.cells) == 2 and len(result.eliminated_arrays) == 1
    check_equivalent(close(result.private_variables, result.body),
                     z3.And(x >= 1, x <= 7, y > x, cost == -3*x + 2*y))
    mutation = z3.And(x >= 1, x <= 7, y > x, cost == 3*x - 2*y)
    solver = z3.Solver()
    solver.add(z3.Xor(close(result.private_variables, result.body), mutation))
    assert solver.check() == z3.sat


def test_equal_index_spellings_share_one_cell():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    x, y = z3.Ints('x y')
    body = z3.And(x == a[2], y == a[z3.IntVal(1)+1])
    result = check_projection(body, [a])
    assert len(result.cells) == 1
    check_equivalent(close(result.private_variables, result.body), x == y)


def test_arrays_at_same_index_remain_independent():
    a, b = [z3.Array(n, z3.IntSort(), z3.IntSort()) for n in ('a', 'b')]
    x, y = z3.Ints('x y')
    result = check_projection(z3.And(x == a[1], y == b[1], a[1] != b[1]), [a, b])
    assert len(result.cells) == 2
    check_equivalent(close(result.private_variables, result.body), x != y)


def test_private_scalar_equations_are_retained():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    hidden, x, cost = z3.Ints('hidden x cost')
    body = z3.And(x == a[-1], hidden == a[-1]+4, hidden < 9, cost == hidden)
    result = check_projection(body, [a, hidden])
    check_equivalent(close(result.private_variables, result.body),
                     z3.And(x < 5, cost == x+4))


@pytest.mark.parametrize('kind', ['Bool', 'Real', 'BitVec'])
def test_scalar_value_sorts(kind):
    sort = {'Bool': z3.BoolSort(), 'Real': z3.RealSort(), 'BitVec': z3.BitVecSort(8)}[kind]
    a = z3.Array('a', z3.IntSort(), sort)
    x, y = z3.Consts('x y', sort)
    body = z3.And(x == a[3], y == a[5], a[3] != a[5])
    # Complete source projection is x != y. Necessity follows for every
    # array; sufficiency has a total array witness for every such x and y.
    # This avoids heuristic quantified Array-to-BV solving returning unknown.
    necessary = z3.Solver()
    necessary.add(body, x == y)
    assert necessary.check() == z3.unsat
    witness = z3.Store(z3.K(z3.IntSort(), x), 5, y)
    sufficient = z3.Solver()
    sufficient.add(x != y, z3.Not(z3.substitute(body, (a, witness))))
    assert sufficient.check() == z3.unsat
    result = scalarize_ground_array_reads(body, [a])
    check_equivalent(close(result.private_variables, result.body), x != y)


def test_unused_private_array_and_no_array_case():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    x, hidden = z3.Ints('x hidden')
    result = check_projection(x == hidden+1, [a, hidden])
    assert not result.cells and result.private_variables == (hidden,)
    direct = scalarize_ground_array_reads(x == hidden, [hidden])
    assert not direct.cells and not direct.eliminated_arrays


@pytest.mark.parametrize('form', ['symbolic', 'equality', 'store', 'argument', 'quantifier'])
def test_unsupported_array_uses_are_not_forgotten(form):
    a, b = [z3.Array(n, z3.IntSort(), z3.IntSort()) for n in ('a', 'b')]
    i = z3.Int('i')
    f = z3.Function('f', a.sort(), z3.BoolSort())
    bodies = {
        'symbolic': a[i] == 0,
        'equality': a == b,
        'store': z3.Select(z3.Store(a, 1, 3), 2) == 0,
        'argument': f(a),
        'quantifier': z3.ForAll(i, a[i] == i),
    }
    with pytest.raises(UnsupportedArrayProjection):
        scalarize_ground_array_reads(bodies[form], [a])


def test_unobserved_ground_read_remains_in_full_constraint():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    x = z3.Int('x')
    body = z3.And(x == a[1], a[2] >= x, a[2] < 4)
    result = check_projection(body, [a])
    assert len(result.cells) == 2
    check_equivalent(close(result.private_variables, result.body), x < 4)


def test_public_array_is_preserved():
    a, public = [z3.Array(n, z3.IntSort(), z3.IntSort()) for n in ('a', 'public')]
    result = check_projection(z3.And(a[1] == public[7], a[1] > 3), [a])
    check_equivalent(close(result.private_variables, result.body), public[7] > 3)


def test_nested_array_sort_and_duplicate_private_are_rejected():
    a = z3.Array('a', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    with pytest.raises(UnsupportedArrayProjection):
        scalarize_ground_array_reads(z3.Select(z3.Select(a, 1), 2) == 3, [a])
    x = z3.Int('x')
    with pytest.raises(UnsupportedArrayProjection):
        scalarize_ground_array_reads(x == 0, [x, x])
