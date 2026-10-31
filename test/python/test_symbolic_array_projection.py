"""Full relation checks for private arrays with symbolic read indices."""
import pytest
import z3
from z3.z3util import get_vars

from tools.semantic_checks.ground_array_projection import UnsupportedArrayProjection
from tools.semantic_checks.symbolic_array_projection import scalarize_symbolic_array_reads


def closed(variables, body):
    return z3.Exists(variables, body) if variables else body


def assert_equivalent(body, private, projected):
    solver = z3.Solver()
    solver.add(z3.Xor(closed(private, body),
                      closed(projected.private_variables, projected.body)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('sort', [z3.IntSort(), z3.BoolSort(), z3.RealSort(), z3.BitVecSort(8)])
def test_symbolic_read_aliasing_preserves_each_scalar_sort(sort):
    array = z3.Array('a', z3.IntSort(), sort)
    i, j = z3.Ints('i j')
    x, y = z3.Consts('x y', sort)
    body = z3.And(z3.Select(array, i) == x, z3.Select(array, j) == y)
    projected = scalarize_symbolic_array_reads(body, [array])
    assert len(projected.consistency_conditions) == 1
    # Z3 can return unknown for the quantified Bool-array equivalence. Prove
    # both directions through a constructive total-array witness instead:
    # any original array implies consistency, and consistency supplies an
    # array satisfying both reads. The projected formula must equal it too.
    consistent = z3.Implies(i == j, x == y)
    witness = z3.Store(z3.K(z3.IntSort(), x), j, y)
    obligations = [
        z3.And(body, z3.Not(consistent)),
        z3.And(consistent, z3.Not(z3.substitute(body, (array, witness)))),
        z3.Xor(consistent, closed(projected.private_variables, projected.body)),
    ]
    for obligation in obligations:
        solver = z3.Solver()
        solver.add(obligation)
        assert solver.check() == z3.unsat


def test_congruence_is_required_for_equal_indices():
    array = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, j = z3.Ints('i j')
    body = z3.And(i == j, array[i] != array[j])
    projected = scalarize_symbolic_array_reads(body, [array])
    solver = z3.Solver()
    solver.add(projected.body)
    assert solver.check() == z3.unsat
    # Dropping the generated consistency obligation admits a false witness.
    solver = z3.Solver()
    solver.add(projected.body.arg(0))
    assert solver.check() == z3.sat


def test_nested_reads_rewrite_indices_and_all_congruence_dependencies():
    a, b = [z3.Array(n, z3.IntSort(), z3.IntSort()) for n in ['a', 'b']]
    i, x, y = z3.Ints('i x y')
    body = z3.And(a[i] == x, b[a[i]] == y, b[x] != y)
    projected = scalarize_symbolic_array_reads(body, [a, b])
    solver = z3.Solver()
    solver.add(projected.body)
    assert solver.check() == z3.unsat
    assert_equivalent(body, [a, b], projected)


def test_self_indexed_read_uses_the_same_total_array():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i = z3.Int('i')
    body = z3.And(a[i] == i, a[a[i]] != i)
    projected = scalarize_symbolic_array_reads(body, [a])
    assert_equivalent(body, [a], projected)
    solver = z3.Solver()
    solver.add(projected.body)
    assert solver.check() == z3.unsat


def test_ground_duplicates_share_cells_without_quadratic_conditions():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    body = z3.And(*[a[i] == i for i in range(64)], a[1 + z3.IntVal(1)] == 2)
    projected = scalarize_symbolic_array_reads(body, [a])
    assert len(projected.cells) == 64
    assert not projected.consistency_conditions
    assert_equivalent(body, [a], projected)


def test_symbolic_and_ground_reads_share_values_at_any_integer_index():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, value = z3.Ints('i value')
    body = z3.And(a[-100] == 2, a[10000] == 4, a[i] == value)
    projected = scalarize_symbolic_array_reads(body, [a])
    assert len(projected.consistency_conditions) == 2
    assert_equivalent(body, [a], projected)
    solver = z3.Solver()
    solver.add(projected.body, i == 50000, value == -7)
    assert solver.check() == z3.sat


def test_negation_and_signed_cost_are_preserved_inside_complete_body():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, j, cost = z3.Ints('i j cost')
    body = z3.And(z3.Not(a[i] == a[j]), cost == -3*a[i] + 2*a[j])
    projected = scalarize_symbolic_array_reads(body, [a])
    # Quantified array XOR is incomplete in Z3 and can return unknown depending
    # on earlier context allocations. Prove both existential directions by
    # explicit witnesses instead, preserving the entire signed-cost body.
    reads = [(value, z3.Select(array, index))
             for array, index, value in projected.cells]
    from_original = z3.substitute(projected.body, *reads)
    total_array = z3.K(z3.IntSort(), 0)
    for array, index, value in projected.cells:
        assert array.eq(a)
        total_array = z3.Store(total_array, index, value)
    from_projected = z3.substitute(body, (a, total_array))
    for obligation in (z3.And(body, z3.Not(from_original)),
                       z3.And(projected.body, z3.Not(from_projected))):
        solver = z3.Solver()
        solver.add(obligation)
        assert solver.check() == z3.unsat
    # A reversed cost sign must fail the same forward implication.
    solver = z3.Solver()
    solver.add(body, z3.Not(z3.substitute(from_original, (cost, -cost))))
    assert solver.check() == z3.sat


def test_public_arrays_and_private_scalar_indices_remain_in_scope():
    a, b = [z3.Array(n, z3.IntSort(), z3.IntSort()) for n in ['a', 'b']]
    i = z3.Int('i')
    body = z3.And(a[i] == b[i], i == 3)
    projected = scalarize_symbolic_array_reads(body, [a, i])
    assert projected.private_variables[0].eq(i)
    assert any(b.eq(variable) for variable in get_vars(projected.body))
    assert_equivalent(body, [a, i], projected)


@pytest.mark.parametrize('kind', ['equality', 'store', 'function', 'quantifier', 'nested-sort'])
def test_unsupported_whole_array_or_quantified_uses_are_rejected(kind):
    a, b = [z3.Array(n, z3.IntSort(), z3.IntSort()) for n in ['a', 'b']]
    i = z3.Int('i')
    if kind == 'equality':
        body = a == b
    elif kind == 'store':
        body = z3.Select(z3.Store(a, 1, 2), i) == 3
    elif kind == 'function':
        body = z3.Function('f', a.sort(), z3.BoolSort())(a)
    elif kind == 'quantifier':
        body = z3.ForAll([i], a[i] == 3)
    else:
        a = z3.Array('nested', z3.IntSort(), b.sort())
        body = a[0][i] == 3
    with pytest.raises(UnsupportedArrayProjection):
        scalarize_symbolic_array_reads(body, [a])
