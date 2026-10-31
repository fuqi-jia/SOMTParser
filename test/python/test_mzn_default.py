"""MiniZinc default captures partial values without global domain constraints."""
import pytest
import z3
import somtparser as sp


def formula(source):
    result = sp.translate(source=source + 'solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def same(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('negated', [False, True])
def test_multidimensional_decision_lookup_checks_each_source_axis(negated):
    expression = '(a[row,col] default 99) = r'
    if negated:
        expression = f'not ({expression})'
    actual = formula('array[4..5,-1..0] of var int: a;'
                     'var int: row;var int: col;var int: r;'
                     f'constraint {expression};')
    row, col, r = z3.Ints('row col r')
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    inside = z3.And(row >= 4, row <= 5, col >= -1, col <= 0)
    expected = z3.If(inside, a[(row-4)*2+col+1], 99) == r
    same(actual, z3.Not(expected) if negated else expected)


@pytest.mark.parametrize('negated', [False, True])
def test_undefined_fallback_is_required_only_when_selected(negated):
    expression = '(a[i] default a[j]) = r'
    if negated:
        expression = f'not ({expression})'
    actual = formula('array[1..2] of var int:a;var int:i;var int:j;var int:r;'
                     f'constraint {expression};')
    i, j, r = z3.Ints('i j r')
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    first, second = z3.And(i >= 1, i <= 2), z3.And(j >= 1, j <= 2)
    expected = z3.And(z3.Or(first, second), z3.If(first, a[i], a[j]) == r)
    same(actual, z3.Not(expected) if negated else expected)


@pytest.mark.parametrize('expression,expected', [
    ('a[i] default 3 + 4', lambda a, i: z3.If(z3.And(i >= 1, i <= 2), a[i], 3) + 4),
    ('2 * a[i] default 3', lambda a, i: 2 * z3.If(z3.And(i >= 1, i <= 2), a[i], 3)),
    ('a[i] default 3 ^ 2', lambda a, i: z3.If(z3.And(i >= 1, i <= 2), a[i], 3) ** 2),
    ('-a[i] default 3', lambda a, i: -z3.If(z3.And(i >= 1, i <= 2), a[i], 3)),
    ('a[i+1] default 3 ^ 2', lambda a, i: z3.If(z3.And(i+1 >= 1, i+1 <= 2), a[i+1], 3) ** 2),
    ('a[i] default 3 ^ 0', lambda a, i: z3.IntVal(1)),
    ('(a[i] default 3 + 1) ^ 2', lambda a, i: (z3.If(z3.And(i >= 1, i <= 2), a[i], 3) + 1) ** 2),
])
def test_default_precedes_arithmetic_and_unary_sign(expression, expected):
    actual = formula('array[1..2] of var int:a;var int:i;var int:r;'
                     f'constraint r = {expression};')
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, r = z3.Ints('i r')
    same(actual, r == expected(a, i))


def test_nonoptional_boolean_partiality_is_false_before_default():
    actual = formula('array[1..2] of var bool:a;var int:i;'
                     'constraint not a[i] default true;')
    a = z3.Array('a', z3.IntSort(), z3.BoolSort())
    i = z3.Int('i')
    same(actual, z3.Not(z3.And(i >= 1, i <= 2, a[i])))


@pytest.mark.parametrize('fallback,expected', [('+17', 17), ('-17', -17)])
def test_signed_fallback_operand(fallback, expected):
    same(formula('array[1..2] of int:a=[3,5];var int:r;'
                 f'constraint r=a[0] default {fallback};'), z3.Int('r') == expected)


@pytest.mark.parametrize('decision', [False, True])
@pytest.mark.parametrize('expression', ['a[0] default 17', '(a[0] + 4) default 17',
                                      'a[0] default a[3] default 17'])
def test_constant_invalid_index_is_captured_before_reporting_an_error(decision, expression):
    array = ('array[1..2] of var int:a;' if decision
             else 'array[1..2] of int:a=[3,5];')
    same(formula(array + f'var int:r;constraint r={expression};'), z3.Int('r') == 17)


@pytest.mark.parametrize('kind,initial,fallback,expected', [('int', '[3,5]', '17', True),
                                                         ('bool', '[false,true]', 'true', False),
                                                         ('string', '["a","b"]', '"fallback"', True)])
def test_fixed_parameter_table_default_preserves_element_type(kind, initial, fallback, expected):
    source = f'array[1..2] of {kind}:a={initial};constraint (a[0] default {fallback})={fallback};'
    same(formula(source), z3.BoolVal(expected))


def test_boolean_default_coercion_occurs_after_relational_closure():
    actual = formula('array[1..2] of var bool:a;var int:i;var int:r;'
                     'constraint r=a[i] default 7;')
    a = z3.Array('a', z3.IntSort(), z3.BoolSort())
    i, r = z3.Ints('i r')
    same(actual, r == z3.If(z3.And(i >= 1, i <= 2, a[i]), 1, 0))


@pytest.mark.parametrize('decision', [False, True])
def test_unused_invalid_fallback_has_no_domain_obligation(decision):
    array = ('array[1..2] of var int:a;' if decision
             else 'array[1..2] of int:a=[3,5];')
    same(formula(array + 'constraint (11 default a[0]) = 11;'), z3.BoolVal(True))


def test_parameter_table_with_dynamic_index_and_fixed_invalid_coordinate():
    source = ('array[4..5,-1..0] of int:a=array2d(4..5,-1..0,[2,3,5,7]);var int:i;'
              'var int:r;constraint r=a[i,1] default 19;')
    same(formula(source), z3.Int('r') == 19)


def test_empty_parameter_table_has_no_fictitious_cell():
    same(formula('array[1..0] of int:a=[];var int:i;'
                 'var int:r;constraint r=a[i] default 19;'), z3.Int('r') == 19)


def test_parameter_offset_does_not_overflow_before_bounds_check():
    source = ('array[-9223372036854775807..-9223372036854775806] of int:a=array1d(-9223372036854775807..-9223372036854775806,[2,3]);'
              'var int:r;constraint r=a[9223372036854775807] default 19;')
    same(formula(source), z3.Int('r') == 19)


def test_real_division_and_mixed_numeric_default_keep_exact_values():
    d, r = z3.Int('d'), z3.Real('r')
    actual = formula('var int:d;var float:r;constraint r=(1.0/d) default 2.5;')
    same(actual, r == z3.If(d != 0, z3.RealVal(1)/z3.ToReal(d), z3.RealVal('5/2')))
    same(formula('var int:d;var float:r;constraint r=d default 2.5;'),
         r == z3.ToReal(d))


def test_default_inside_a_generator_matches_explicit_boundary_handling():
    actual = formula('array[1..3] of var int:a;var int:r;'
                     'constraint r=sum(i in 1..3)(a[i-1] default 0);')
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    same(actual, z3.Int('r') == a[1] + a[2])


@pytest.mark.parametrize('body', ['a[0]=1', 'a[0]+1=2', 'a[0]+(1 default 2)=3'])
def test_constant_index_errors_outside_default_are_still_reported(body):
    result = sp.translate(source=f'array[1..2] of int:a=[2,3];constraint {body};solve satisfy;',
                          language='minizinc')
    assert not result.ok
    assert any('outside' in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize('body', ['a[true] default 2 = 2', 'a[0] default "bad" = 2',
                                 '1 default missing = 1'])
def test_default_does_not_suppress_type_or_name_errors(body):
    result = sp.translate(source=f'array[1..2] of int:a=[2,3];constraint {body};solve satisfy;',
                          language='minizinc')
    assert not result.ok


def test_invalid_second_axis_type_is_not_hidden_by_invalid_first_axis():
    result = sp.translate(source='array[1..2,1..2] of var int:a;'
                          'constraint (a[0,true] default 2)=2;solve satisfy;', language='minizinc')
    assert not result.ok
    assert any('sort Int' in d.message for d in result.diagnostic_items)
