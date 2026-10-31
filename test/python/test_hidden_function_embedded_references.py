"""Semantic closure of function-valued parameters, independent of model labels."""
import pytest
import z3

from tools.semantic_checks.hidden_functions import encode_hidden_functions
from tools.semantic_checks.projection import existential_projection


def as_array(function):
    return z3.ArrayRef(z3.Z3_mk_as_array(function.ctx_ref(), function.ast), function.ctx)


def unsatisfiable(formula):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(formula)
    assert solver.check() == z3.unsat


def test_function_only_in_as_array_is_closed():
    function = z3.Function('as_array_only', z3.IntSort(), z3.IntSort())
    x = z3.Int('as_array_visible')
    body, witnesses = encode_hidden_functions(x == z3.Select(as_array(function), 3))
    assert len(witnesses) == 1
    instantiated = z3.substitute(body, (witnesses[0], z3.K(z3.IntSort(), 17)))
    unsatisfiable(z3.Xor(instantiated, x == 17))
    unsatisfiable(z3.Not(existential_projection(x == z3.Select(as_array(function), 3), [x])))


def test_single_domain_as_array_is_the_shared_witness_without_an_artificial_lambda():
    function = z3.Function('unary_as_array_witness', z3.IntSort(), z3.BoolSort())
    original = as_array(function)
    encoded, witnesses = encode_hidden_functions(original)
    assert len(witnesses) == 1
    assert encoded.eq(witnesses[0]) and encoded.sort().eq(original.sort())
    assert not z3.is_quantifier(encoded)
    output = z3.Bool('unary_as_array_output')
    projected = existential_projection(output == z3.Select(original, 0), [output])
    unsatisfiable(z3.Not(projected))


def test_single_domain_array_valued_function_keeps_the_nested_range():
    result_sort = z3.ArraySort(z3.BoolSort(), z3.IntSort())
    function = z3.Function('array_valued_unary', z3.IntSort(), result_sort)
    original = as_array(function)
    encoded, witnesses = encode_hidden_functions(original)
    assert len(witnesses) == 1
    assert encoded.eq(witnesses[0]) and encoded.sort().eq(original.sort())
    assert encoded.sort().range().eq(result_sort)
    disagreement, witnesses = encode_hidden_functions(
        z3.Select(z3.Select(original, 7), True) != z3.Select(function(7), True))
    assert len(witnesses) == 1
    unsatisfiable(disagreement)


def test_application_as_array_and_map_share_one_interpretation():
    function = z3.Function('three_forms', z3.IntSort(), z3.IntSort())
    mapped = z3.Map(function, z3.K(z3.BoolSort(), 3))
    encoded, witnesses = encode_hidden_functions(z3.Or(
        function(3) != z3.Select(as_array(function), 3),
        function(3) != z3.Select(mapped, True)))
    assert len(witnesses) == 1
    unsatisfiable(encoded)


def test_as_array_multi_domain_is_not_confused_with_nested_arrays():
    function = z3.Function('multi_as_array', z3.IntSort(), z3.BoolSort(), z3.IntSort())
    array = as_array(function)
    closed_array, arrays = encode_hidden_functions(array)
    assert closed_array.is_lambda() and closed_array.num_vars() == 2
    assert closed_array.sort().eq(array.sort())
    assert not arrays[0].sort().eq(array.sort())
    encoded, witnesses = encode_hidden_functions(z3.Or(
        z3.Select(array, 7, True) != function(7, True),
        z3.Select(array, 2, False) != function(2, False)))
    assert len(witnesses) == 1
    unsatisfiable(encoded)


def test_map_multi_domain_indices_and_mixed_argument_positions():
    function = z3.Function('mixed_map', z3.BoolSort(), z3.IntSort(), z3.IntSort())
    left = z3.Array('mixed_map_left', z3.IntSort(), z3.BoolSort(), z3.BoolSort())
    right = z3.Array('mixed_map_right', z3.IntSort(), z3.BoolSort(), z3.IntSort())
    mapped = z3.Map(function, left, right)
    body = z3.Select(mapped, 5, False) != function(
        z3.Select(left, 5, False), z3.Select(right, 5, False))
    encoded, witnesses = encode_hidden_functions(body)
    assert len(witnesses) == 1
    unsatisfiable(encoded)


def test_map_under_array_and_index_binders_avoids_capture():
    function = z3.Function('bound_map', z3.IntSort(), z3.IntSort())
    array = z3.Array('bound_array', z3.BoolSort(), z3.IntSort())
    index = z3.Bool('bound_index')
    identity = z3.ForAll([array], z3.ForAll([index],
        z3.Select(z3.Map(function, array), index) == function(z3.Select(array, index))))
    encoded, witnesses = encode_hidden_functions(identity)
    assert len(witnesses) == 1
    unsatisfiable(z3.Not(encoded))


def test_nested_map_declaration_parameter_is_closed_recursively():
    function = z3.Function('nested_map_private', z3.IntSort(), z3.IntSort())
    inner = z3.Array('nested_map_inner', z3.IntSort(), z3.IntSort())
    map_declaration = z3.Map(function, inner).decl()
    outer = z3.Array('nested_map_outer', z3.BoolSort(), inner.sort())
    mapped = z3.Map(map_declaration, outer)
    encoded, witnesses = encode_hidden_functions(
        z3.Select(z3.Select(mapped, True), 4) != function(z3.Select(z3.Select(outer, True), 4)))
    assert len(witnesses) == 1
    unsatisfiable(encoded)


def test_nested_lambdas_and_function_valued_array_are_closed():
    function = z3.Function('inside_lambda', z3.IntSort(), z3.BoolSort(), z3.IntSort())
    i = z3.Int('lambda_i')
    b = z3.Bool('lambda_b')
    array = z3.Lambda([i], z3.Lambda([b], function(i, b)))
    encoded, witnesses = encode_hidden_functions(
        z3.Select(z3.Select(array, 5), True) != function(5, True))
    assert len(witnesses) == 1
    unsatisfiable(encoded)


def test_quantifier_patterns_and_names_are_rewritten_together():
    function = z3.Function('pattern_private', z3.IntSort(), z3.IntSort())
    x = z3.Int('original_bound_name')
    original = z3.ForAll([x], function(x) == x, patterns=[function(x)], weight=7, qid='q-name', skid='s-name')
    encoded, witnesses = encode_hidden_functions(original)
    assert len(witnesses) == 1
    assert encoded.var_name(0) == 'original_bound_name'
    assert encoded.weight() == 7 and encoded.qid() == 'q-name' and encoded.skolem_id() == 's-name'
    assert encoded.num_patterns() == 1
    assert encoded.pattern(0).arg(0).decl().kind() == z3.Z3_OP_SELECT
    assert encoded.pattern(0).arg(0).arg(0).eq(witnesses[0])
    instantiated = z3.substitute_vars(encoded.body(), z3.IntVal(11))
    unsatisfiable(z3.And(instantiated, z3.Select(witnesses[0], 11) != 11))


def test_function_only_in_no_pattern_annotation_does_not_leak():
    function = z3.Function('no_pattern_private', z3.IntSort(), z3.IntSort())
    x = z3.Int('no_pattern_bound')
    original = z3.ForAll([x], x == x, no_patterns=[function(x)])
    encoded, witnesses = encode_hidden_functions(original)
    assert len(witnesses) == 1
    assert encoded.num_no_patterns() == 1
    assert encoded.no_pattern(0).decl().kind() == z3.Z3_OP_SELECT
    unsatisfiable(z3.Not(encoded))


def test_unsupported_transitive_closure_is_reported_before_projection():
    relation = z3.Function('private_reachability', z3.IntSort(), z3.IntSort(), z3.BoolSort())
    with pytest.raises(ValueError, match='embedded private functions'):
        encode_hidden_functions(z3.TransitiveClosure(relation)(0, 1))


def test_interpreted_map_and_datatype_parameters_remain_interpreted():
    datatype = z3.Datatype('EmbeddedProjectionBox')
    datatype.declare('box', ('value', z3.IntSort()))
    datatype = datatype.create()
    function = z3.Function('separate_private', z3.IntSort(), z3.IntSort())
    array = z3.Array('interpreted_map_array', z3.IntSort(), z3.IntSort())
    plus = (z3.Int('plus_a') + z3.Int('plus_b')).decl()
    body = z3.And(function(0) == 1, z3.Select(z3.Map(plus, array, array), 3) != 2 * array[3],
                  datatype.is_box(datatype.box(1)))
    encoded, witnesses = encode_hidden_functions(body)
    assert len(witnesses) == 1
    unsatisfiable(encoded)


def test_independent_as_array_models_get_independent_witnesses():
    function = z3.Function('shared_textual_function', z3.IntSort(), z3.BoolSort())
    output = z3.Bool('as_array_output')
    left = existential_projection(output == z3.Select(as_array(function), 0), [output])
    right = existential_projection(output != z3.Select(as_array(function), 0), [output])
    unsatisfiable(z3.Xor(left, right))


def test_recursive_definition_hidden_dependencies_are_not_silently_retained():
    private = z3.Function('recursive_private_dependency', z3.IntSort(), z3.IntSort())
    defined = z3.RecFunction('definition_with_private_body', z3.IntSort(), z3.IntSort())
    argument = z3.Int('recursive_argument')
    z3.RecAddDefinition(defined, [argument], private(argument))
    with pytest.raises(ValueError, match='explicit expansion of recursive function definitions'):
        encode_hidden_functions(defined(0) == 1)


def test_sequence_map_array_function_argument_is_closed():
    function = z3.Function('sequence_map_private', z3.IntSort(), z3.IntSort())
    source = z3.Concat(z3.Unit(z3.IntVal(2)), z3.Unit(z3.IntVal(7)))
    expected = z3.Concat(z3.Unit(function(2)), z3.Unit(function(7)))
    encoded, witnesses = encode_hidden_functions(z3.SeqMap(as_array(function), source) != expected)
    assert len(witnesses) == 1
    unsatisfiable(encoded)


def test_sequence_fold_multi_domain_function_argument_is_closed():
    function = z3.Function('sequence_fold_private', z3.IntSort(), z3.IntSort(), z3.IntSort())
    source = z3.Concat(z3.Unit(z3.IntVal(2)), z3.Unit(z3.IntVal(7)))
    expected = function(function(0, 2), 7)
    encoded, witnesses = encode_hidden_functions(z3.SeqFoldLeft(as_array(function), z3.IntVal(0), source) != expected)
    assert len(witnesses) == 1
    unsatisfiable(encoded)
