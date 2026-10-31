"""Numeric extrema preserve generator binding, selection and definedness."""
import itertools

import pytest
import z3
import somtparser as sp


def formula(source):
    result = sp.translate(source=source + 'solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def test_carpet_nested_parameter_extrema_and_shadowed_set_name():
    actual = formula('''
      set of int: i = 8..9;
      array[4..6] of int: lengths = array1d(4..6,[7,2,5]);
      array[4..6] of int: widths = array1d(4..6,[1,4,3]);
      int: least = min(i in 4..6)(min(lengths[i],widths[i]));
      int: largest_extent = max(i in 4..6)(max(lengths[i],widths[i]));
      constraint least=1 /\\ largest_extent=7 /\\ min(i)=8;
      constraint min(i,j in 1..3 where i<j)(j-i)=1;
    ''')
    solver = z3.Solver(); solver.add(actual)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('fn', ['min', 'max'])
@pytest.mark.parametrize('syntax', ['generator', 'comprehension'])
@pytest.mark.parametrize('negated', [False, True])
def test_decision_filter_matches_all_selection_subsets(fn, syntax, negated):
    head = 'if i=1 then x elseif i=2 then y else z endif'
    where = 'if i=1 then a elseif i=2 then b else c endif'
    expr = (f'{fn}(i in 1..3 where {where})({head})' if syntax == 'generator'
            else f'{fn}([{head} | i in 1..3 where {where}])')
    condition = f'{expr}=r'
    if negated: condition = f'not ({condition})'
    actual = formula('var -1..1:x;var -1..1:y;var -1..1:z;var -1..1:r;'
                     'var bool:a;var bool:b;var bool:c;constraint '+condition+';')
    values = z3.Ints('x y z'); r = z3.Int('r'); guards = z3.Bools('a b c')
    alternatives = []
    for mask in itertools.product([False, True], repeat=3):
        kept = [v for v,keep in zip(values,mask) if keep]
        if not kept: continue
        value = kept[0]
        for v in kept[1:]:
            value = z3.If(value <= v if fn == 'min' else value >= v, value, v)
        alternatives.append(z3.And(*[g == keep for g,keep in zip(guards,mask)], r == value))
    expected = z3.Or(*alternatives)
    if negated: expected = z3.Not(expected)
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(*[z3.And(v>=-1,v<=1) for v in [*values,r]], z3.Xor(actual,expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('fn', ['min', 'max'])
@pytest.mark.parametrize('negated', [False, True])
def test_only_selected_values_need_be_defined(fn, negated):
    condition = f'{fn}(i in 1..2 where i=2 \\/ a)(if i=1 then 1 div z else 5 endif)=5'
    if negated: condition = f'not ({condition})'
    actual = formula('var bool:a;var 0..0:z;constraint '+condition+';')
    expected = z3.Bool('a') if negated else z3.Not(z3.Bool('a'))
    solver = z3.Solver(); solver.add(z3.Int('z')==0,z3.Xor(actual,expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('syntax', ['min(i in 1..n)(i)', 'min([i | i in 1..n])'])
def test_decision_bound_preserves_empty_selection(syntax):
    actual = formula('var 0..3:n;constraint '+syntax+'=1;')
    n = z3.Int('n')
    solver = z3.Solver(); solver.add(n>=0,n<=3,z3.Xor(actual,n>=1))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('expression', ['min(i in 1..2)(true)',
    'max([true | i in 1..0])', 'min(i in 1..0)(i)', 'max(i in 1..2 where false)(i)'])
def test_wrong_element_types_and_statically_empty_extrema_are_diagnosed(expression):
    result = sp.translate(source='constraint '+expression+'=0;solve satisfy;',language='minizinc')
    assert not result.ok


@pytest.mark.parametrize('negated', [False, True])
@pytest.mark.parametrize('predicate', [False, True])
def test_scalar_row_binding_shadows_outer_set_and_restores_slice(negated, predicate):
    source = """
      set of int: i = 8..9;
      array[4..5,8..9] of int: a = array2d(4..5,8..9,[1,2,3,4]);
    """
    if predicate:
        source += 'predicate row(int:i,int:v)=sum(a[i,..])=v;'
        condition = 'row(4,3) /\\ row(5,7)'
    else:
        condition = 'sum(i in 4..5)(sum(a[i,..]))=10'
    # After the scalar scope exits, i denotes the original set again.
    condition = '('+condition+') /\\ sum(a[4,i])=3'
    if negated:
        condition = 'not ('+condition+')'
    actual = formula(source+'constraint '+condition+';')
    solver = z3.Solver(); solver.add(actual)
    assert solver.check() == (z3.unsat if negated else z3.sat)
