"""MiniZinc string-array concatenation preserves values and partiality."""
from pathlib import Path

import pytest
import somtparser as sp
import z3


def translate(source):
    return sp.translate(source=source + '\nsolve satisfy;', language='minizinc')


def solver(source):
    result = translate(source)
    assert result.ok, [d.message for d in result.diagnostic_items]
    s = z3.Solver()
    s.set(timeout=5000)
    s.add(z3.parse_smt2_string(result.to_smt2()))
    return s


@pytest.mark.parametrize('expression,expected', [
    ('concat([])', ''),
    ('concat(["a", "", "b"])', 'ab'),
    ('concat(["#" | i in 1..3])', '###'),
    ('concat(["#" | i in 1..0])', ''),
    ('concat(["汉", "字", "🙂"])', '汉字🙂'),
    ('concat([concat(["a", "b"]), "c"])', 'abc'),
])
def test_concat_exact_parameter_value(expression, expected):
    prefix = f'string: block = {expression};'
    assert solver(prefix + f'constraint block = "{expected}";').check() == z3.sat
    assert solver(prefix + f'constraint block != "{expected}";').check() == z3.unsat


def test_concat_preserves_nonzero_indices_and_enum_order():
    assert solver('array[-2..0] of string: a = array1d(-2..0, ["b","a","b"]); '
                  'constraint concat(a) = "bab";').check() == z3.sat
    assert solver('enum E = {first,second}; array[E] of string: a = ["x","y"]; '
                  'constraint concat(a) = "xy";').check() == z3.sat


@pytest.mark.parametrize('negated', [False, True])
def test_concat_preserves_dynamic_string_cell_and_undefined_index(negated):
    relation = 'concat([a[i], "!"]) = "a!"'
    if negated:
        relation = f'not ({relation})'
    prefix = 'array[1..2] of string: a = ["a","b"]; var 0..2:i;'
    s = solver(prefix + 'constraint ' + relation + ';')
    for index, equal in [(0, False), (1, True), (2, False)]:
        s.push()
        s.add(z3.Int('i') == index)
        assert s.check() == (z3.sat if equal != negated else z3.unsat)
        s.pop()


@pytest.mark.parametrize('expression', ['a[2]', 'concat([a[2]])'])
def test_concat_parameter_extraction_does_not_erase_undefinedness(expression):
    result = translate('array[1..1] of string:a=["a"]; '
                       f'string:block={expression}; constraint block="";')
    assert not result.ok


@pytest.mark.parametrize('declaration,expression', [
    ('', 'concat([1])'),
    ('array[1..0] of int: a=[];', 'concat(a)'),
    ('', 'concat([|"a","b"|])'),
])
def test_concat_rejects_nonstring_or_multidimensional_array(declaration, expression):
    assert not translate(declaration + 'constraint ' + expression + '="";').ok


def test_user_string_function_named_concat_keeps_its_body():
    source = ('function string: concat(array[int] of string: s)="own"; '
              'constraint concat(["different"])="own";')
    assert solver(source).check() == z3.sat


@pytest.mark.parametrize('relative,expected', [
    ('ok/concat_strings.mzn', True),
    ('reject/concat_integer_array.mzn', False),
])
def test_concat_fixtures(relative, expected):
    root = Path(__file__).resolve().parents[2]
    result = sp.translate(path=str(root / 'languages/minizinc/instances' / relative),
                          language='minizinc')
    assert result.ok == expected, [d.message for d in result.diagnostic_items]
