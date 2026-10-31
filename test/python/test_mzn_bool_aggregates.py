"""MiniZinc Bool-to-Int coercion in numeric folds, including partial terms."""
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


@pytest.mark.parametrize('fn', ['sum', 'product'])
@pytest.mark.parametrize('syntax', ['named', 'literal', 'generator', 'comprehension'])
@pytest.mark.parametrize('size', [0, 1, 3])
def test_bool_folds_keep_numeric_result_and_empty_identity(fn, syntax, size):
    argument = {
        'named': '(b)',
        'literal': '([' + ','.join(f'b[{i}]' for i in range(1, size + 1)) + '])',
        'generator': f'(i in 1..{size})(b[i])',
        'comprehension': f'([b[i] | i in 1..{size}])',
    }[syntax]
    actual = formula(f'array[1..{size}] of var bool: b; var int: r;'
                     f'constraint r = {fn}{argument};')
    b = z3.Array('b', z3.IntSort(), z3.BoolSort())
    r = z3.Int('r')
    terms = [z3.If(b[i], 1, 0) for i in range(1, size + 1)]
    expected = z3.Sum(*terms) if fn == 'sum' else 1
    if fn == 'product':
        for term in terms:
            expected *= term
    same(actual, r == expected)


@pytest.mark.parametrize('fn,expected', [('sum', 2), ('product', 0)])
def test_fixed_bool_array_and_multidimensional_alias(fn, expected):
    actual = formula(f'array[4..6] of bool: b = array1d(4..6, [true, false, true]);'
                     f'array[2..2,4..6] of bool: a = array2d(2..2,4..6,b);'
                     f'var int: r; constraint r = {fn}(a);')
    same(actual, z3.Int('r') == expected)


@pytest.mark.parametrize('fn', ['sum', 'product'])
@pytest.mark.parametrize('syntax', ['generator', 'comprehension'])
def test_decision_filter_coerces_before_choosing_numeric_identity(fn, syntax):
    argument = ('(i in 1..3 where keep[i])(b[i])' if syntax == 'generator'
                else '([b[i] | i in 1..3 where keep[i]])')
    actual = formula('array[1..3] of var bool: b;array[1..3] of var bool: keep;'
                     f'var int:r;constraint r={fn}{argument};')
    b = z3.Array('b', z3.IntSort(), z3.BoolSort())
    keep = z3.Array('keep', z3.IntSort(), z3.BoolSort())
    terms = [z3.If(keep[i], z3.If(b[i], 1, 0), 0 if fn == 'sum' else 1)
             for i in range(1, 4)]
    expected = z3.Sum(*terms) if fn == 'sum' else terms[0] * terms[1] * terms[2]
    same(actual, z3.Int('r') == expected)


@pytest.mark.parametrize('fn', ['sum', 'product'])
@pytest.mark.parametrize('negated', [False, True])
def test_partial_bool_under_filter_matches_explicit_bool2int(fn, negated):
    # The selection guard must control definedness as well as the 0/1 value.
    # Compare the shorthand with MiniZinc's existing explicit coercion path.
    prefix = 'var bool: keep;var 0..1:z;'
    body = '1 div z = 1'
    relation = f'{fn}(i in 1..1 where keep)({body})=1'
    explicit = f'{fn}(i in 1..1 where keep)(bool2int({body}))=1'
    if negated:
        relation, explicit = f'not ({relation})', f'not ({explicit})'
    same(formula(prefix + 'constraint ' + relation + ';'),
         formula(prefix + 'constraint ' + explicit + ';'))


@pytest.mark.parametrize('fn', ['sum', 'product'])
@pytest.mark.parametrize('element,values', [('string', '["x"]'), ('set of int', '[{1}]')])
@pytest.mark.parametrize('empty', [False, True])
def test_nonnumeric_named_arrays_remain_type_errors_even_when_empty(fn, element, values, empty):
    size = 0 if empty else 1
    source = (f'array[1..{size}] of {element}: a = {"[]" if empty else values};'
              f'constraint {fn}(a)=0;solve satisfy;')
    result = sp.translate(source=source, language='minizinc')
    assert not result.ok
    assert any('no matching signature' in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize('fn', ['forall', 'exists', 'count'])
def test_boolean_folds_do_not_coerce_int_to_bool(fn):
    result = sp.translate(source=f'array[1..0] of int:a=[];constraint {fn}(a)=true;solve satisfy;',
                          language='minizinc')
    assert not result.ok
