"""Complete-relation and construction-size controls for bounded read projection."""
import pytest
import z3

from tools.semantic_checks.ground_array_projection import UnsupportedArrayProjection
from tools.semantic_checks.symbolic_array_projection import scalarize_symbolic_array_reads


def closed(result):
    return (z3.Exists(result.private_variables, result.body)
            if result.private_variables else result.body)


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('offset', [-5, 0, 10**40])
@pytest.mark.parametrize('sort', [z3.IntSort(), z3.RealSort(), z3.BoolSort(), z3.BitVecSort(8)])
def test_complete_carrier_needs_no_pair_obligations(offset, sort):
    array = z3.Array('complete_carrier', z3.IntSort(), sort)
    i, j = z3.Ints('complete_i complete_j')
    a, b, x, y = z3.Consts('complete_a complete_b complete_x complete_y', sort)
    body = z3.And(array[offset] == a, array[offset + 1] == b,
                  offset <= i, i < offset + 2, offset <= j, j < offset + 2,
                  x == array[i], y == array[j])
    result = scalarize_symbolic_array_reads(body, [array])
    assert len(result.bounded_read_definitions) == 2
    assert not result.consistency_conditions
    expected = z3.And(offset <= i, i < offset + 2, offset <= j, j < offset + 2,
                      x == z3.If(i == offset, a, b), y == z3.If(j == offset, a, b))
    equivalent(closed(result), expected)


def test_distinct_bounds_overlap_and_signed_cost_remains_exact():
    array = z3.Array('overlap_array', z3.IntSort(), z3.IntSort())
    i, j, cost = z3.Ints('overlap_i overlap_j overlap_cost')
    body = z3.And(array[0] == 3, array[1] == 7, array[2] == 13,
                  i >= 0, i <= 1, j >= 1, j <= 2,
                  cost == -array[i] + 2*array[j])
    result = scalarize_symbolic_array_reads(body, [array])
    assert not result.consistency_conditions
    expected = z3.And(i >= 0, i <= 1, j >= 1, j <= 2,
                      cost == -z3.If(i == 0, 3, 7) + 2*z3.If(j == 1, 7, 13))
    equivalent(closed(result), expected)
    solver = z3.Solver()
    solver.add(closed(result), i == j, cost != 7)
    assert solver.check() == z3.unsat


def test_unbounded_read_still_aliases_every_bounded_lookup():
    array = z3.Array('mixed_array', z3.IntSort(), z3.IntSort())
    i, j, x, y = z3.Ints('mixed_i mixed_j mixed_x mixed_y')
    body = z3.And(array[0] == 11, array[1] == 17, i >= 0, i <= 1,
                  x == array[i], y == array[j])
    result = scalarize_symbolic_array_reads(body, [array])
    assert len(result.bounded_read_definitions) == 1
    assert len(result.consistency_conditions) == 2
    expected = z3.And(i >= 0, i <= 1, x == z3.If(i == 0, 11, 17),
                      z3.Implies(j == 0, y == 11), z3.Implies(j == 1, y == 17))
    equivalent(closed(result), expected)
    for index, value, answer in [(1, 99, z3.unsat), (2, 99, z3.sat), (-1, 99, z3.sat)]:
        solver = z3.Solver()
        solver.add(closed(result), i == 1, j == index, y == value)
        assert solver.check() == answer


def test_nested_bounded_definition_rewrites_residual_congruence_indices():
    a, b = [z3.Array(name, z3.IntSort(), z3.IntSort()) for name in ['nested_a', 'nested_b']]
    i, x, y = z3.Ints('nested_i nested_x nested_y')
    body = z3.And(a[0] == 4, a[1] == 9, i >= 0, i <= 1,
                  b[a[i]] == x, b[4] == y)
    result = scalarize_symbolic_array_reads(body, [a, b])
    assert len(result.bounded_read_definitions) == 1
    assert len(result.consistency_conditions) == 1
    equivalent(closed(result), z3.And(i >= 0, i <= 1, z3.Implies(i == 0, x == y)))


@pytest.mark.parametrize('aliased', [False, True])
def test_read_after_aliasing_writes_preserves_last_write(aliased):
    a = z3.Array('write_array', z3.IntSort(), z3.IntSort())
    i, j, k, value, cost = z3.Ints('write_i write_j write_k write_value write_cost')
    bounds = z3.And(i >= 0, i <= 1, j >= 0, j <= 1, k >= 0, k <= 1,
                    j == k if aliased else j != k)
    original = z3.And(a[0] == 5, a[1] == 19, bounds,
                      cost == -z3.Select(z3.Store(z3.Store(a, j, 31), k, value), i))
    prepared = z3.And(a[0] == 5, a[1] == 19, bounds,
                      cost == -z3.If(i == k, value, z3.If(i == j, 31, a[i])))
    # Read-over-write preparation is an independently checked equivalence,
    # not an assumption about distinct write indices.
    equivalent(original, prepared)
    result = scalarize_symbolic_array_reads(prepared, [a])
    expected = z3.And(bounds, cost == -z3.If(i == k, value,
                      z3.If(i == j, 31, z3.If(i == 0, 5, 19))))
    equivalent(closed(result), expected)
    with pytest.raises(UnsupportedArrayProjection):
        scalarize_symbolic_array_reads(original, [a])


@pytest.mark.parametrize('kind', ['hole', 'conditional-upper', 'different-index', 'different-array'])
def test_incomplete_or_unrelated_carrier_does_not_bound_a_read(kind):
    a, b = [z3.Array(name, z3.IntSort(), z3.IntSort()) for name in ['gap_a', 'gap_b']]
    i, j, cost = z3.Ints('gap_i gap_j gap_cost')
    gate = z3.Bool('gap_gate')
    atoms = [a[0] == 11, a[2] == 17, cost == a[i]]
    if kind != 'hole':
        atoms.append((b if kind == 'different-array' else a)[1] == 13)
    if kind == 'conditional-upper':
        atoms.extend([i >= 0, z3.Implies(gate, i <= 2)])
    elif kind == 'different-index':
        atoms.extend([j >= 0, j <= 2])
    else:
        atoms.extend([i >= 0, i <= 2])
    result = scalarize_symbolic_array_reads(z3.And(*atoms), [a, b])
    assert not result.bounded_read_definitions
    solver = z3.Solver()
    solver.add(closed(result), i == (3 if kind in ('conditional-upper', 'different-index') else 1),
               cost == 999, z3.Not(gate))
    assert solver.check() == z3.sat


def test_contradictory_bounds_are_retained():
    a = z3.Array('empty_carrier', z3.IntSort(), z3.IntSort())
    i = z3.Int('empty_i')
    result = scalarize_symbolic_array_reads(z3.And(a[0] == 5, i > 0, i < 0, a[i] == 9), [a])
    assert not result.bounded_read_definitions
    equivalent(closed(result), z3.BoolVal(False))


@pytest.mark.parametrize('residual_reads', [0, 2])
def test_carrier_is_substituted_before_quadratic_pairs_are_constructed(monkeypatch, residual_reads):
    a = z3.Array('scale_array', z3.IntSort(), z3.IntSort())
    ground_count, bounded_count = 128, 96
    indices = [z3.Int('scale_i_' + str(n)) for n in range(bounded_count)]
    free_indices = [z3.Int('scale_free_' + str(n)) for n in range(residual_reads)]
    atoms = [a[n] == n + 1 for n in range(ground_count)]
    atoms.extend(z3.And(i >= 0, i < ground_count, a[i] > 0) for i in indices)
    atoms.extend(a[i] > 0 for i in free_indices)
    body = z3.And(*atoms)
    calls = []
    original = z3.Implies

    def counted(*args, **kwargs):
        calls.append(1)
        return original(*args, **kwargs)

    monkeypatch.setattr(z3, 'Implies', counted)
    result = scalarize_symbolic_array_reads(body, [a])
    expected_pairs = residual_reads*ground_count + residual_reads*(residual_reads - 1)//2
    assert len(calls) == expected_pairs
    assert len(result.consistency_conditions) == expected_pairs
    assert len(result.bounded_read_definitions) == bounded_count
    assert len(result.private_variables) == ground_count + residual_reads
    # Check a satisfying full assignment; no elapsed-time threshold is used.
    solver = z3.Solver()
    solver.add(result.body, *[i == n % ground_count for n, i in enumerate(indices)],
               *[i == ground_count + n for n, i in enumerate(free_indices)])
    assert solver.check() == z3.sat
