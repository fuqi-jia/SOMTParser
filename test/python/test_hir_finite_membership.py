"""Shared lowering of finite-set membership, without a guessed universe."""
import itertools
import shutil
import subprocess

import pytest
import z3
import somtparser as sp
from somtparser.hir import HirBuilder


def op(name, *args):
    return {'op': name, 'args': list(args)}


def lit(value, sort='Int'):
    return {'literal': value, 'sort': sort}


def finite(*elements, sort='Int'):
    empty = lit('set.empty', {'Set': sort})
    return op('set.insert', *elements, empty) if elements else empty


@pytest.mark.parametrize('kind', ['union', 'intersection', 'difference', 'conditional'])
@pytest.mark.parametrize('negated', [False, True])
def test_symbolic_finite_set_algebra_against_python_membership(kind, negated):
    x,y,z = ({'var': name} for name in ['x','y','z'])
    left, right = finite(y,lit(1),y), finite(z,lit(-1))
    if kind == 'conditional':
        expr = op('ite',op('lt',y,z),left,right)
    else:
        expr = op({'union':'set.union','intersection':'set.inter','difference':'set.minus'}[kind],left,right)
    member = op('set.member',x,expr)
    builder = HirBuilder()
    for name in ['x','y','z']: builder.declare(name,'Int')
    builder.constrain(op('not',member) if negated else member)
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    assert 'set.member' not in script and '(Set ' not in script
    assert 'finite-set-membership' in result.report.to_json()
    actual = z3.And(*z3.parse_smt2_string(script))
    variables = z3.Ints('x y z'); accepted=[]
    for xv,yv,zv in itertools.product(range(-2,3), repeat=3):
        a,b = {yv,1},{zv,-1}
        values = {'union': a|b, 'intersection': a&b, 'difference': a-b,
                  'conditional': a if yv<zv else b}[kind]
        if (xv in values) != negated:
            accepted.append(z3.And(*[v==n for v,n in zip(variables,[xv,yv,zv])]))
    solver=z3.Solver();solver.set(timeout=10000)
    solver.add(*[z3.And(v>=-2,v<=2) for v in variables],z3.Xor(actual,z3.Or(*accepted)))
    assert solver.check()==z3.unsat


def test_empty_boolean_and_real_finite_membership():
    builder=HirBuilder()
    builder.constrain(op('not',op('set.member',lit(0),finite())))
    builder.constrain(op('set.member',lit(True,'Bool'),finite(lit(True,'Bool'),sort='Bool')))
    builder.constrain(op('set.member',lit(3),op('set.singleton',lit(3))))
    builder.constrain(op('set.member',lit('1/2','Real'),finite(lit('0.5','Real'),sort='Real')))
    result=builder.translate();assert result.ok
    solver=z3.Solver();solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check()==z3.sat


def test_unknown_sets_and_complements_retain_their_native_theory():
    builder=HirBuilder();builder.declare('s',{'Set':'Int'});builder.declare('x','Int')
    builder.constrain(op('set.member',{'var':'x'},op('set.insert',lit(1),{'var':'s'})))
    result=builder.translate();assert result.ok
    assert 'set.member' in result.to_smt2()
    assert 'finite-set-membership' not in result.report.to_json()
    builder=HirBuilder()
    builder.constrain(op('set.member',lit(1),op('set.complement',finite(lit(2)))))
    result=builder.translate();assert result.ok
    assert 'set.complement' in result.to_smt2()


@pytest.mark.parametrize('negative', [False,True])
def test_minizinc_set_literal_operand_definedness_is_not_erased(negative):
    expr='x in {1,1 div z}'
    if negative:expr='not ('+expr+')'
    result=sp.translate(source='var 1..1:x;var 0..0:z;constraint '+expr+';solve satisfy;',language='minizinc')
    assert result.ok,[d.message for d in result.diagnostic_items]
    solver=z3.Solver();solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check()==(z3.sat if negative else z3.unsat)


@pytest.mark.parametrize('set_expr,members', [
    ('{1} union (2..3)', [1, 2, 3]),
    ('{1,3} diff {3}', [1]),
    ('{1} union A', [1, 2, 3]),
    ('A union B', [2, 3, 4]),
])
@pytest.mark.parametrize('negative', [False, True])
def test_minizinc_literal_and_named_set_algebra_membership(set_expr, members, negative):
    predicate = 'x in ' + set_expr
    if negative:
        predicate = 'not (' + predicate + ')'
    result = sp.translate(
        source='set of int:A=2..3;set of int:B={4};var -1..5:x;constraint '
               + predicate + ';solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    x = z3.Int('x')
    expected = z3.Or(*[x == value for value in members])
    if negative:
        expected = z3.Not(expected)
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(x >= -1, x <= 5, z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('element, values, expected', [
    (1, '{0}', 'sat'), (2, '{0}', 'unsat'),
    (1, '{2}', 'sat'), (2, '{2}', 'sat'),
])
def test_minizinc_literal_union_with_decision_set_keeps_symbolic_operand(element, values, expected):
    result = sp.translate(source='var 1..2:x;var set of int:s;'
                          'constraint x in {1} union s;'
                          f'constraint x={element};constraint s={values};solve satisfy;',
                          language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    assert 'set.member' in script
    executable = shutil.which('cvc5')
    if executable is None:
        pytest.skip('cvc5 is required to check symbolic set membership')
    # Both set.member(x, union({1}, s)) and x=1 OR set.member(x, s)
    # preserve the symbolic operand. Check meaning rather than printed shape.
    solved = subprocess.run([executable, '--lang=smt2', '--tlimit=5000'],
                            input=script, text=True, capture_output=True, timeout=10)
    assert solved.returncode == 0, solved.stdout + solved.stderr
    assert solved.stdout.strip() == expected, solved.stdout + solved.stderr


@pytest.mark.parametrize('language', ['minizinc', 'minizinc-union', 'xcsp3'])
@pytest.mark.parametrize('negative', [False, True])
def test_frontend_finite_membership_keeps_exact_values_and_polarity(language, negative):
    if language.startswith('minizinc'):
        predicate='x in {c | c in 1..3 where c != 2}'
        if language=='minizinc-union':predicate+=' union {-2}'
        if negative: predicate='not ('+predicate+')'
        source='var -3..3:x; constraint '+predicate+'; solve satisfy;'
        members=[-2,1,3] if language=='minizinc-union' else [1,3]
    else:
        predicate='in(x,set(-1,1,3))'
        if negative: predicate='not('+predicate+')'
        source=('<instance format="XCSP3" type="CSP"><variables>'
                '<var id="x"> -3..3 </var></variables><constraints>'
                '<intension>'+predicate+'</intension></constraints></instance>')
        members=[-1,1,3]
    result=sp.translate(source=source,language=language.split('-')[0])
    assert result.ok,[d.message for d in result.diagnostic_items]
    actual=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    x=z3.Int('x');expected=z3.Or(*[x==v for v in members])
    if negative:expected=z3.Not(expected)
    solver=z3.Solver();solver.set(timeout=10000)
    solver.add(x>=-3,x<=3,z3.Xor(actual,expected))
    assert solver.check()==z3.unsat
