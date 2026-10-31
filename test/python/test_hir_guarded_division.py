"""A local nonzero proof must never become a global domain or cross a binder."""
import pytest
import z3
from somtparser import HirBuilder
from somtparser._nl_model import ModelError


def lit(x, sort='Int'):
    return {'literal': x, 'sort': sort}


def var(x):
    return {'var': x}


def op(name, *args):
    return {'op': name, 'args': list(args)}


def formula(expression):
    b=HirBuilder();b.declare('x','Int');b.declare('d','Int')
    b.constrain(expression);result=b.translate()
    assert result.ok,[d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def same(left,right):
    solver=z3.Solver();solver.set(timeout=10000);solver.add(z3.Xor(left,right))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('guard,expected', [
    (op('ne',var('d'),lit(0)),lambda d:d!=0),
    (op('not',op('eq',var('d'),lit(0))),lambda d:d!=0),
    (op('gt',var('d'),lit(0)),lambda d:d>0),
    (op('ge',var('d'),lit(2)),lambda d:d>=2),
    (op('lt',var('d'),lit(0)),lambda d:d<0),
    (op('le',var('d'),lit(-1)),lambda d:d<=-1),
    (op('lt',lit(0),var('d')),lambda d:0<d),
    (op('eq',lit(-2),var('d')),lambda d:-2==d),
])
def test_guarded_integer_remainder_retains_zero_and_both_signs(guard,expected):
    expression=op('implies',guard,op('eq',op('mod_euclid',var('x'),var('d')),lit(1)))
    x,d=z3.Ints('x d');same(formula(expression),z3.Implies(expected(d),x%d==1))


@pytest.mark.parametrize('operator', ['div','div_euclid','mod_euclid','div_trunc','mod_trunc','div_floor','mod_floor'])
def test_division_conventions_in_a_guarded_ite(operator):
    from fractions import Fraction
    sort='Real' if operator=='div' else 'Int'
    zero=lit('0','Real') if sort=='Real' else lit(0)
    expr=op('ite',op('eq',var('d'),lit(0)),zero,op(operator,var('x'),var('d')))
    b=HirBuilder();b.declare('x','Int');b.declare('d','Int');b.declare('q',sort)
    b.constrain(op('eq',var('q'),expr));result=b.translate();assert result.ok
    target=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    x,d=z3.Ints('x d');q=z3.Real('q') if sort=='Real' else z3.Int('q')
    expected=[]
    # Independent exact arithmetic across both signs and the zero branch.
    for a in range(-8,9):
        for divisor in range(-3,4):
            value=0
            if divisor:
                ratio=Fraction(a,divisor)
                trunc=int(ratio)
                floor=a//divisor
                remainder=a%abs(divisor)
                euclid=(a-remainder)//divisor
                value={'div':ratio,'div_euclid':euclid,'mod_euclid':remainder,
                       'div_trunc':trunc,'mod_trunc':a-divisor*trunc,
                       'div_floor':floor,'mod_floor':a-divisor*floor}[operator]
            exact=z3.RealVal(str(value)) if sort=='Real' else z3.IntVal(value)
            expected.append(z3.And(x==a,d==divisor,q==exact))
    solver=z3.Solver();solver.set(timeout=10000)
    solver.add(x>=-8,x<=8,d>=-3,d<=3,z3.Xor(target,z3.Or(*expected)))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('outer', ['and','or'])
def test_zero_guard_sibling_is_order_independent_and_survives_negation(outer):
    guard=op('ne' if outer=='and' else 'eq',var('d'),lit(0))
    relation=op('eq',op('mod_euclid',var('x'),var('d')),lit(0))
    x,d=z3.Ints('x d')
    expected=z3.And(d!=0,x%d==0) if outer=='and' else z3.Or(d==0,x%d==0)
    for args in [(guard,relation),(relation,guard)]:
        same(formula(op('not',op(outer,*args))),z3.Not(expected))


def test_guard_facts_do_not_cross_native_quantifier_shadowing():
    relation=op('eq',op('mod_euclid',var('x'),var('d')),lit(0))
    shadow={'quantifier':'forall','binders':[{'name':'d','sort':'Int'}],'body':relation}
    with pytest.raises(ModelError,match='nonzero'):
        formula(op('implies',op('ne',var('d'),lit(0)),shadow))
    inner=op('implies',op('gt',var('d'),lit(2)),relation)
    shadow=dict(shadow,body=inner)
    x,d,t=z3.Ints('x d t')
    same(formula(op('implies',op('ne',var('d'),lit(0)),shadow)),
         z3.Implies(d!=0,z3.ForAll([t],z3.Implies(t>2,x%t==0))))


def test_guard_facts_do_not_cross_finite_fold_shadowing():
    folded={'fold':'forall','var':'d','range':[0,2],
            'body':op('eq',op('mod_euclid',var('x'),var('d')),lit(0))}
    with pytest.raises(ModelError,match='nonzero'):
        formula(op('implies',op('ne',var('d'),lit(0)),folded))


@pytest.mark.parametrize('guard', [
    op('ge',var('d'),lit(0)),op('le',var('d'),lit(0)),
    op('ne',var('d'),lit(2)),op('eq',var('d'),lit(0)),
    op('or',op('ne',var('d'),lit(0)),op('eq',var('x'),lit(1))),
])
def test_zero_possible_guards_remain_rejected(guard):
    with pytest.raises(ModelError,match='nonzero'):
        formula(op('implies',guard,op('eq',op('mod_euclid',var('x'),var('d')),lit(0))))


def test_facts_do_not_escape_one_call_or_ite_branch():
    b=HirBuilder();b.declare('d','Int')
    b.expr(op('implies',op('ne',var('d'),lit(0)),op('eq',op('mod_euclid',lit(5),var('d')),lit(0))))
    with pytest.raises(ModelError,match='nonzero'):
        b.expr(op('mod_euclid',lit(5),var('d')))
    with pytest.raises(ModelError,match='nonzero'):
        b.expr(op('ite',op('eq',var('d'),lit(0)),op('mod_euclid',lit(5),var('d')),lit(0)))
