"""Full formula equivalence for finite defined-array witness projection."""
import pytest
import z3
from tools.semantic_checks.existential_definitions import (
    _defined_array_witness, eliminate_existential_definitions)


def prove(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def prove_array_projection(array, body, result, cells):
    # A complete equivalence proof using an explicit reverse array witness;
    # nested quantified array equality is otherwise unknown to Z3.
    forward = z3.Solver()
    forward.add(body, z3.Not(result))
    assert forward.check() == z3.unsat
    empty = z3.K(z3.IntSort(), False)
    witness = z3.K(z3.IntSort(), empty)
    for index, value in cells:
        witness = z3.Store(witness, index, value)
    reverse = z3.Solver()
    reverse.add(result, z3.Not(z3.substitute(body, (array, witness))))
    assert reverse.check() == z3.unsat


def test_nested_set_values_and_bounded_symbolic_read():
    array = z3.Array('sets', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    first, second = z3.Consts('first second', z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    index, member = z3.Ints('index member')
    body = z3.And(array[0] == first, array[1] == second,
                  index >= 0, index <= 1, z3.Select(array[index], member))
    result = eliminate_existential_definitions(z3.Exists([array], body))
    expected = z3.And(index >= 0, index <= 1,
                      z3.Select(z3.If(index == 0, first, second), member))
    assert result.direct_definitions == 1
    prove(result.formula, expected)
    prove_array_projection(array, body, result.formula, [(0, first), (1, second)])


@pytest.mark.parametrize('scale,offset', [(1, 0), (2, -3), (-2, 7)])
def test_affine_original_bounds_cover_only_defined_cells(scale, offset):
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    index, x, y, z = z3.Ints('index x y z')
    keys = [scale * i + offset for i in range(3)]
    body = z3.And(*(array[k] == v for k, v in zip(keys, (x, y, z))),
                  index >= 0, index <= 2, array[scale * index + offset] > 9)
    result = eliminate_existential_definitions(z3.Exists([array], body))
    assert result.direct_definitions == 1
    prove(z3.Exists([array], body), result.formula)


@pytest.mark.parametrize('bad_kind', ['undefined-ground', 'unbounded-index', 'incomplete-range', 'whole-array', 'quantified-index', 'self-index'])
def test_incomplete_array_definitions_retain_witness(bad_kind):
    array, other = z3.Consts('array other', z3.ArraySort(z3.IntSort(), z3.IntSort()))
    index, value = z3.Ints('index value')
    extra = {
        'undefined-ground': array[1] == 3,
        'unbounded-index': array[index] == 3,
        'incomplete-range': z3.And(index >= 0, index <= 2, array[index] == 3),
        'whole-array': array != other,
        'quantified-index': z3.ForAll([index], array[index] >= 0),
        'self-index': array[array[0]] == 3,
    }[bad_kind]
    # A non-defining use leaves the undefined ground cell genuinely free.
    if bad_kind == 'undefined-ground':
        extra = array[1] > 3
    body = z3.And(array[0] == value, extra)
    assert _defined_array_witness(body, {array.get_id(): array}) is None
    result = eliminate_existential_definitions(z3.Exists([array], body))
    prove(z3.Exists([array], body), result.formula)


def test_incomplete_range_is_not_filled_with_a_default_value():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    body = z3.And(array[0] == 0, array[2] == 1, array[1] > 8)
    assert _defined_array_witness(body, {array.get_id(): array}) is None
    solver = z3.Solver()
    solver.add(z3.Exists([array], body))
    assert solver.check() == z3.sat


def test_conflicting_duplicate_cells_remain_unsatisfiable():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    body = z3.And(array[0] == 2, array[0] == 3)
    result = eliminate_existential_definitions(z3.Exists([array], body))
    assert result.direct_definitions == 1
    prove(result.formula, z3.BoolVal(False))


def test_self_definition_cannot_supply_an_array_cell():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    body = z3.And(array[0] == array[1], array[1] > 0)
    assert _defined_array_witness(body, {array.get_id(): array}) is None


def test_nested_set_universal_condition_preserves_scope():
    array = z3.Array('array', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    public = z3.Array('public', z3.IntSort(), z3.BoolSort())
    index = z3.Int('index')
    body = z3.And(array[0] == public, z3.ForAll([index], z3.Implies(array[0][index], index >= 0)))
    result = eliminate_existential_definitions(z3.Exists([array], body))
    expected = z3.ForAll([index], z3.Implies(public[index], index >= 0))
    assert result.direct_definitions == 1
    prove(result.formula, expected)


def test_shadowed_binder_with_same_name_is_not_an_observed_cell():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    shadow = z3.Array('array', z3.IntSort(), z3.IntSort())
    value = z3.Int('value')
    body = z3.And(array[0] == value, z3.ForAll([shadow], shadow[0] == 0))
    result = eliminate_existential_definitions(z3.Exists([array], body))
    assert result.direct_definitions == 1
    prove(result.formula, z3.BoolVal(False))


def test_store_read_of_defined_nested_cells_retains_overrides():
    array = z3.Array('array', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    public = z3.Array('public', z3.IntSort(), z3.BoolSort())
    index, member = z3.Ints('index member')
    empty = z3.K(z3.IntSort(), False)
    body = z3.And(array[0] == public, array[1] == empty, index >= 0, index <= 1,
                  z3.Select(z3.Select(z3.Store(array, 1, public), index), member))
    result = eliminate_existential_definitions(z3.Exists([array], body))
    assert result.direct_definitions == 1
    prove(result.formula, z3.And(index >= 0, index <= 1, public[member]))
    prove_array_projection(array, body, result.formula, [(0, public), (1, empty)])


def test_bound_store_read_does_not_escape_quantifier():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    index, value = z3.Ints('index value')
    body = z3.And(array[0] == value,
                  z3.ForAll([index], z3.Select(z3.Store(array, 1, 7), index) >= index))
    assert _defined_array_witness(body, {array.get_id(): array}) is None


def test_two_private_arrays_cannot_remove_a_definition_cycle():
    a, b = z3.Consts('a b', z3.ArraySort(z3.IntSort(), z3.IntSort()))
    body = z3.And(a[0] == b[0], b[0] == a[0] + 1)
    result = eliminate_existential_definitions(z3.Exists([a, b], body))
    prove(result.formula, z3.BoolVal(False))


def test_conditional_cell_equality_is_not_a_definition():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    guard = z3.Bool('guard')
    body = z3.And(z3.Implies(guard, a[0] == 0), a[0] > 7)
    assert _defined_array_witness(body, {a.get_id(): a}) is None


def test_public_array_is_never_selected_without_private_authorization():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    x = z3.Int('x')
    body = z3.And(a[0] == x, a[1] > 0)
    assert _defined_array_witness(body, {x.get_id(): x}) is None
