"""Official model constructs retain values, indices and partiality."""
import pytest
import somtparser as sp
import z3


def assert_relation(source, expected, data=()):
    result = sp.translate(source=source + ' solve satisfy;', language='minizinc', data=list(data))
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('value,index,expected', [
    ('[3,7,]', 2, 7),
    ('array1d(-2..-1,[3,7,])', -1, 7),
    ('[i*i | i in 2..4]', 3, 16),
    ('[3] ++ [7,]', 2, 7),
])
def test_inferred_parameter_initializer_keeps_values_and_indices(value, index, expected):
    assert_relation(f'array[int] of int: a :: output = {value}; var int: x; '
                    f'constraint x = a[{index}];', z3.Int('x') == expected)


@pytest.mark.parametrize('value,index,expected', [
    ('[3,7,]', 1, 3),
    ('array1d(-2..-1,[3,7,])', -2, 3),
    ('array1d(S,[3,7,])', 5, 7),
])
def test_inferred_parameter_data_keeps_explicit_or_deferred_indices(tmp_path, value, index, expected):
    path = tmp_path/'case.dzn'
    path.write_text('a = ' + value + ';')
    assert_relation('set of int: S = 4..5; array[int] of int: a :: output; '
                    f'var int: x; constraint x = a[{index}];', z3.Int('x') == expected, [str(path)])


def test_named_parameter_array_keeps_nonstandard_origin():
    assert_relation('array[-2..-1] of int: a = array1d(-2..-1, [8,9]); array[int] of int: b = a; '
                    'var int: x; constraint x = b[-1];', z3.Int('x') == 9)


@pytest.mark.parametrize('sort,value,condition', [
    ('bool', '[true,false,]', 'a[1] /\\ not a[2]'),
    ('string', '["alpha","beta",]', 'a[2] = "beta"'),
    ('set of int', '[{i,i+1} | i in 1..3]', '4 in a[3]'),
    ('int', '[]', 'sum(a) = 0'),
    ('set of int', '[{i} | i in 1..0]', 'card(index_set(a)) = 0'),
])
def test_inferred_parameter_element_types_and_empty_values(sort, value, condition):
    assert_relation(f'array[int] of {sort}: a = {value}; var int: x; '
                    f'constraint {condition}; constraint x = 1;', z3.Int('x') == 1)


def test_trailing_commas_preserve_matrix_rows_in_data_and_expression(tmp_path):
    path = tmp_path/'case.dzn'
    path.write_text('a = [|1,2,|3,4,|];')
    assert_relation('array[1..2,1..2] of int: a; '
                    'array[1..2,1..2] of var int: b = [|5,6,|7,8,|]; '
                    'constraint b[2,1] = a[1,2]+5;',
                    z3.And(*[z3.Select(z3.Array('b', z3.IntSort(), z3.IntSort()),i)==v
                             for i,v in enumerate([5,6,7,8])]), [str(path)])


@pytest.mark.parametrize('expression,expected', [
    ('5+4^3', 69), ('2^3^2', 64), ('-2^2', -4), ('(-2)^2', 4),
    ('2*3^2', 18), ('pow(3,4)', 81), ('0^0', 1),
    ('1^9223372036854775807', 1), ('+2^3', 8),
])
def test_fixed_power_precedence_and_large_exponent(expression, expected):
    assert_relation(f'int: n = {expression}; var int: x; constraint x = n;', z3.Int('x') == expected)


def test_decision_base_powers_and_real_reciprocal_are_exact():
    x = z3.Int('x')
    assert_relation('var -4..4: x; constraint x^3 = -8;', z3.And(x >= -4,x <= 4,x*x*x == -8))
    assert_relation('var float: r; constraint r = 2.0 /\\ r^(-3) = 0.125;', z3.Real('r') == 2)


def test_zero_power_does_not_erase_undefined_base_under_negation():
    x = z3.Int('x')
    assert_relation('var int: x; constraint not ((1 div x)^0 = 1);', x == 0)


@pytest.mark.parametrize('source', [
    'array[int] of int: a = [true];',
    'array[int] of int: a = [|1,2|3,4|];',
    'array[int] of int: a;',
    'array[int] of int: a = [1,,2];',
    'array[1..2,1..2] of int: a = [|1,2,|3,|];',
    'int: n = 2^63;',
    'int: n = 2^(-1);',
])
def test_inference_and_power_keep_invalid_inputs_diagnosed(source):
    assert not sp.translate(source=source+' solve satisfy;',language='minizinc').ok
