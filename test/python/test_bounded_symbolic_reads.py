import pytest
import z3

from tools.semantic_checks.symbolic_array_projection import scalarize_symbolic_array_reads
from tools.semantic_checks.source_oracles.fzn_json_source import element_relation, read_source


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def project(result):
    return z3.Exists(result.private_variables, result.body) if result.private_variables else result.body


@pytest.mark.parametrize('offset,size', [(-7, 0), (-7, 1), (-7, 4), (1, 3), (10**80, 4)])
@pytest.mark.parametrize('sort', [z3.IntSort(), z3.BoolSort(), z3.RealSort()])
def test_element_entire_relation_equals_literal_disjunction(offset, size, sort):
    index = z3.Int('element_index')
    values = [z3.Const('element_value_' + str(i), sort) for i in range(size)]
    result = z3.Const('element_result', sort)
    actual = element_relation(index, offset, values, result)
    expected = z3.Or(*[z3.And(index == offset + i, result == value)
                       for i, value in enumerate(values)])
    equivalent(actual, expected)


def test_source_element_result_is_eliminated_without_losing_cost_or_guard():
    source = read_source(dict(version='1.0', variables={
        'i': {'type': 'int'}, 'r': {'type': 'int'}, 'a': {'type': 'int'}, 'b': {'type': 'int'}},
        arrays={}, output=[], solve={'method': 'maximize', 'objective': 'r'},
        constraints=[{'id': 'gecode_int_element', 'args': ['i', -3, ['a', 'b'], 'r']}]))
    i, a, b, cost = z3.Ints('observed_i observed_a observed_b observed_cost')
    actual = source.projected([(i, source.variables['i']), (a, source.variables['a']),
                               (b, source.variables['b'])], signed_cost=cost)
    equivalent(actual, z3.And(i >= -3, i <= -2, cost == -z3.If(i == -3, a, b)))


@pytest.mark.parametrize('offset', [-3, 0, 7])
def test_complete_ground_coverage_eliminates_dynamic_cell_with_signed_cost(offset):
    array = z3.Array('bounded_array', z3.IntSort(), z3.IntSort())
    index, a, b, cost = z3.Ints('bounded_index bounded_a bounded_b bounded_cost')
    body = z3.And(array[offset] == a, array[offset + 1] == b,
                  index >= offset, index < offset + 2, cost == -array[index])
    result = scalarize_symbolic_array_reads(body, [array])
    assert len(result.bounded_read_definitions) == 1
    assert len(result.private_variables) == 2
    expected = z3.And(index >= offset, index < offset + 2,
                      cost == -z3.If(index == offset, a, b))
    equivalent(project(result), expected)
    wrong = z3.Solver()
    wrong.add(z3.Xor(project(result), z3.And(index >= offset, index < offset + 2,
                                            cost == -z3.If(index == offset, a, b) + 1)))
    assert wrong.check() == z3.sat


@pytest.mark.parametrize('missing', ['upper', 'lower', 'cell', 'conditional-bound'])
def test_missing_coverage_never_introduces_an_index_restriction(missing):
    array = z3.Array('incomplete_array', z3.IntSort(), z3.IntSort())
    index, cost = z3.Ints('incomplete_index incomplete_cost')
    gate = z3.Bool('incomplete_gate')
    atoms = [array[0] == 11, cost == array[index]]
    if missing != 'cell':
        atoms.append(array[1] == 17)
    if missing != 'lower':
        atoms.append(index >= 0)
    if missing == 'conditional-bound':
        atoms.append(z3.Implies(gate, index <= 1))
    elif missing != 'upper':
        atoms.append(index <= 1)
    result = scalarize_symbolic_array_reads(z3.And(*atoms), [array])
    assert not result.bounded_read_definitions
    witness = 1 if missing == 'cell' else -1 if missing == 'lower' else 2
    solver = z3.Solver()
    solver.add(project(result), index == witness, cost == 1234, z3.Not(gate))
    assert solver.check() == z3.sat


def test_nested_symbolic_indices_preserve_all_dependency_definitions():
    array = z3.Array('nested_reads', z3.IntSort(), z3.IntSort())
    i, a, b, cost = z3.Ints('nested_i nested_a nested_b nested_cost')
    inner = array[i]
    body = z3.And(array[0] == a, array[1] == b, i >= 0, i <= 1,
                  inner >= 0, inner <= 1, cost == array[inner])
    result = scalarize_symbolic_array_reads(body, [array])
    assert len(result.bounded_read_definitions) == 2
    first = z3.If(i == 0, a, b)
    expected = z3.And(i >= 0, i <= 1, first >= 0, first <= 1,
                      cost == z3.If(first == 0, a, b))
    equivalent(project(result), expected)


def test_bounds_and_ground_cells_do_not_cross_between_arrays():
    a = z3.Array('separate_a', z3.IntSort(), z3.IntSort())
    b = z3.Array('separate_b', z3.IntSort(), z3.IntSort())
    i, j, cost = z3.Ints('separate_i separate_j separate_cost')
    body = z3.And(a[0] == 5, a[1] == 7, b[0] == 19,
                  i >= 0, i <= 1, j >= 0, j <= 1, cost == a[i] + b[j])
    result = scalarize_symbolic_array_reads(body, [a, b])
    assert len(result.bounded_read_definitions) == 1
    expected = z3.And(i >= 0, i <= 1, j >= 0, j <= 1,
                      z3.Implies(j == 0, cost == z3.If(i == 0, 5, 7) + 19))
    equivalent(project(result), expected)


def test_contradictory_and_extra_constraints_are_retained():
    a = z3.Array('contradictory_a', z3.IntSort(), z3.BoolSort())
    i = z3.Int('contradictory_i')
    body = z3.And(a[-1], z3.Not(a[0]), i >= -1, i <= 0,
                  a[i], z3.Not(a[i]))
    result = scalarize_symbolic_array_reads(body, [a])
    assert len(result.bounded_read_definitions) == 1
    equivalent(project(result), z3.BoolVal(False))
