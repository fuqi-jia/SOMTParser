"""Exact finite images of bounded integer subscripts, including sparse strides."""
import pytest
import z3

from tools.semantic_checks.symbolic_array_projection import scalarize_symbolic_array_reads


def closed(result):
    return z3.Exists(result.private_variables, result.body) if result.private_variables else result.body


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('scale', [-96, -1, 1, 96])
@pytest.mark.parametrize('offset', [-7, 0, 10**60])
def test_sparse_affine_image_uses_only_reachable_existing_cells(scale, offset):
    a = z3.Array('affine_a', z3.IntSort(), z3.IntSort())
    i, x, y, t, cost = z3.Ints('affine_i affine_x affine_y affine_t affine_cost')
    values = [x, y, t]
    body = z3.And(*[a[scale*(n - 1) + offset] == value for n, value in enumerate(values)],
                  i >= -1, i <= 1, cost == -a[scale*i + offset])
    result = scalarize_symbolic_array_reads(body, [a])
    assert len(result.bounded_read_definitions) == 1
    assert not result.consistency_conditions
    expected = z3.And(i >= -1, i <= 1, cost == -z3.If(i == -1, x, z3.If(i == 0, y, t)))
    equivalent(closed(result), expected)
    solver = z3.Solver()
    solver.add(closed(result), i == 0, cost != -y)
    assert solver.check() == z3.unsat


def test_composed_affine_expression_and_cancelled_terms():
    a = z3.Array('composed_a', z3.IntSort(), z3.IntSort())
    i, j, cost = z3.Ints('composed_i composed_j composed_cost')
    index = 4*(i - 2) + 2*i + j - j + 3
    body = z3.And(a[1] == 11, a[7] == 17, a[13] == 23,
                  i >= 1, i <= 3, cost == a[index])
    result = scalarize_symbolic_array_reads(body, [a])
    assert len(result.bounded_read_definitions) == 1
    equivalent(closed(result), z3.And(i >= 1, i <= 3,
                 cost == z3.If(i == 1, 11, z3.If(i == 2, 17, 23))))


def test_explicit_bound_on_flattened_index_tightens_affine_carrier():
    a = z3.Array('tight_a', z3.IntSort(), z3.IntSort())
    i, value = z3.Ints('tight_i tight_value')
    index = 10*i + 3
    body = z3.And(i >= -10, i <= 10, index >= 12, index <= 32,
                  a[13] == 5, a[23] == 7, value == a[index])
    result = scalarize_symbolic_array_reads(body, [a])
    assert len(result.bounded_read_definitions) == 1
    equivalent(closed(result), z3.And(i >= 1, i <= 2, value == z3.If(i == 1, 5, 7)))


def test_missing_reachable_cell_retains_unconstrained_value():
    a = z3.Array('missing_a', z3.IntSort(), z3.IntSort())
    i, cost = z3.Ints('missing_i missing_cost')
    body = z3.And(i >= 1, i <= 3, a[101] == 5, a[301] == 7,
                  cost == a[100*i + 1])
    result = scalarize_symbolic_array_reads(body, [a])
    assert not result.bounded_read_definitions
    solver = z3.Solver()
    solver.add(closed(result), i == 2, cost == 999)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('kind', ['no-upper', 'conditional', 'another-variable', 'nonlinear', 'two-variables'])
def test_insufficient_bounds_never_create_an_affine_domain(kind):
    a = z3.Array('unbounded_a', z3.IntSort(), z3.IntSort())
    i, j, value = z3.Ints('unbounded_i unbounded_j unbounded_value')
    gate = z3.Bool('unbounded_gate')
    index = i*i if kind == 'nonlinear' else 10*i+j if kind == 'two-variables' else 10*i
    atoms = [a[10] == 1, a[20] == 2, value == a[index]]
    if kind == 'another-variable':
        atoms.extend([j >= 1, j <= 2])
    else:
        atoms.append(i >= 1)
        if kind == 'conditional':
            atoms.append(z3.Implies(gate, i <= 2))
        elif kind != 'no-upper':
            atoms.append(i <= 2)
    if kind == 'two-variables':
        atoms.extend([j >= 1, j <= 2])
    result = scalarize_symbolic_array_reads(z3.And(*atoms), [a])
    assert not result.bounded_read_definitions
    solver = z3.Solver()
    solver.add(closed(result), i == (1 if kind in ('nonlinear', 'two-variables') else 3),
               j == 1, z3.Not(gate), value == 999)
    assert solver.check() == z3.sat


def test_multivariate_index_can_still_use_explicit_complete_index_bounds():
    a = z3.Array('multivariate_a', z3.IntSort(), z3.IntSort())
    i, j, cost = z3.Ints('multivariate_i multivariate_j multivariate_cost')
    index = 3*i + 7*j
    body = z3.And(index >= 1, index <= 2, a[1] == 11, a[2] == 17, cost == a[index])
    result = scalarize_symbolic_array_reads(body, [a])
    assert len(result.bounded_read_definitions) == 1
    equivalent(closed(result), z3.And(index >= 1, index <= 2, cost == z3.If(index == 1, 11, 17)))


def test_two_affine_subscripts_alias_under_different_offsets():
    a = z3.Array('alias_a', z3.IntSort(), z3.IntSort())
    i, j, x, y = z3.Ints('alias_i alias_j alias_x alias_y')
    body = z3.And(a[2] == 5, a[4] == 7, a[6] == 9,
                  i >= 1, i <= 2, j >= 0, j <= 1,
                  x == a[2*i], y == a[2*j + 4])
    result = scalarize_symbolic_array_reads(body, [a])
    assert len(result.bounded_read_definitions) == 2
    assert not result.consistency_conditions
    equivalent(closed(result), z3.And(i >= 1, i <= 2, j >= 0, j <= 1,
                 x == z3.If(i == 1, 5, 7), y == z3.If(j == 0, 7, 9)))
    solver = z3.Solver()
    solver.add(closed(result), i == j + 2, x != y)
    assert solver.check() == z3.unsat


def test_nested_read_supplies_bounded_affine_index():
    a, b = [z3.Array(name, z3.IntSort(), z3.IntSort()) for name in ['nested_affine_a', 'nested_affine_b']]
    i, cost = z3.Ints('nested_affine_i nested_affine_cost')
    body = z3.And(i >= 0, i <= 1, a[0] == 1, a[1] == 2,
                  a[i] >= 1, a[i] <= 2, b[13] == 11, b[23] == 17,
                  cost == b[10*a[i] + 3])
    result = scalarize_symbolic_array_reads(body, [a, b])
    assert len(result.bounded_read_definitions) == 2
    equivalent(closed(result), z3.And(i >= 0, i <= 1, cost == z3.If(i == 0, 11, 17)))


def test_row_major_scale_does_not_enumerate_unreachable_gap_cells(monkeypatch):
    a = z3.Array('row_major_a', z3.IntSort(), z3.IntSort())
    width, height = 96, 12
    indices = [z3.Int('row_major_i_' + str(n)) for n in range(width)]
    atoms = [a[k] == k + 1 for k in range(width*height)]
    atoms.extend(z3.And(i >= 1, i <= height, a[width*(i - 1) + k] > 0)
                 for k, i in enumerate(indices))
    body = z3.And(*atoms)
    calls = []
    original_if = z3.If

    def counted(*args, **kwargs):
        calls.append(1)
        return original_if(*args, **kwargs)

    monkeypatch.setattr(z3, 'If', counted)
    result = scalarize_symbolic_array_reads(body, [a])
    assert len(result.bounded_read_definitions) == width
    assert not result.consistency_conditions
    assert len(calls) == width*(height - 1)
    assert len(result.private_variables) == width*height
    solver = z3.Solver()
    solver.add(result.body, *[i == 1 + n % height for n, i in enumerate(indices)])
    assert solver.check() == z3.sat
