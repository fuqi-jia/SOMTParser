import pytest
import z3
from tools.semantic_checks.ground_bool_arrays import simplify_ground_bool_arrays


def arr(default, entries=()):
    result = z3.K(z3.IntSort(), z3.BoolVal(default))
    for index, value in entries:
        result = z3.Store(result, index, value)
    return result


def checked(term, expected):
    reduced = simplify_ground_bool_arrays(term)
    assert z3.is_true(reduced) if expected else z3.is_false(reduced)
    solver = z3.Solver(); solver.add(term != reduced)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('default', [False, True])
def test_overwrites_remove_and_restore_exceptions(default):
    checked(arr(default, [(4, not default), (4, default), (-2, not default)]) ==
            arr(default, [(-2, not default)]), True)


def test_same_explicit_support_different_defaults_is_not_equal():
    checked(arr(False, [(0, True)]) == arr(True, [(0, True)]), False)


def test_outside_old_sample_support_is_not_ignored():
    checked(arr(False, [(0, True)]) == arr(False, [(0, True), (10**20, True)]), False)


@pytest.mark.parametrize('operator', ['and', 'or', 'xor', 'implies'])
def test_map_uses_all_input_supports_and_defaults(operator):
    p, q = z3.Bools('p q')
    function = {'and': z3.And(p, q), 'or': z3.Or(p, q),
                'xor': z3.Xor(p, q), 'implies': z3.Implies(p, q)}[operator].decl()
    a, b = arr(True, [(2, False)]), arr(False, [(-3, True), (5, True)])
    mapped = z3.Map(function, a, b)
    values = lambda index: z3.is_true(z3.simplify(function(z3.Select(a, index), z3.Select(b, index))))
    default = z3.is_true(z3.simplify(function(z3.BoolVal(True), z3.BoolVal(False))))
    expected = arr(default, [(i, values(i)) for i in [-3, 2, 5]])
    checked(mapped == expected, True)
    checked(z3.Select(mapped, 100000) == default, True)


def test_nested_maps_handle_true_default_and_false_exceptions():
    p, q = z3.Bools('p q')
    negated = z3.Map(z3.Not(p).decl(), arr(False, [(1, True), (9, True)]))
    result = z3.Map(z3.And(p, q).decl(), negated, arr(True, [(3, False)]))
    checked(result == arr(True, [(1, False), (3, False), (9, False)]), True)


def test_unknown_map_function_is_not_evaluated():
    function = z3.Function('unknown', z3.BoolSort(), z3.BoolSort())
    term = z3.Map(function, arr(False)) == arr(False)
    result = simplify_ground_bool_arrays(term)
    assert not z3.is_true(result) and not z3.is_false(result)
    solver = z3.Solver(); solver.add(term != result)
    assert solver.check() == z3.unsat


def test_symbolic_store_and_unknown_array_are_not_ground():
    i, j = z3.Ints('i j'); a = z3.Array('a', z3.IntSort(), z3.BoolSort())
    for term in [z3.Store(arr(False), i, True) == z3.Store(arr(False), j, True), a == arr(True)]:
        result = simplify_ground_bool_arrays(term)
        assert not z3.is_true(result) and not z3.is_false(result)
        solver = z3.Solver(); solver.add(term != result)
        assert solver.check() == z3.unsat


def test_ite_distinct_and_select_keep_complete_extensional_values():
    a = z3.If(z3.BoolVal(True), arr(True, [(7, False)]), arr(False))
    checked(z3.Distinct(a, arr(True)), True)
    checked(z3.Select(a, 7), False)
    checked(z3.Select(a, 8), True)


def test_quantified_body_is_not_treated_as_ground():
    i = z3.Int('i'); term = z3.ForAll([i], z3.Store(arr(False), i, True) == arr(False))
    assert simplify_ground_bool_arrays(term).eq(term)


def test_deep_store_chain_uses_last_write_without_python_recursion():
    value = arr(False)
    for index in range(1800):
        value = z3.Store(value, 4, index % 2 == 0)
    checked(value == arr(False), True)
