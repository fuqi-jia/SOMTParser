"""An occurrence count is an Int expression, including in objectives."""
import pytest
import z3
import somtparser as sp
from somtparser import _somtparser as native


@pytest.mark.parametrize('negated',[False,True])
@pytest.mark.parametrize('boolean',[False,True])
def test_function_count_matches_independent_indicators(negated,boolean):
    typ='bool' if boolean else 'int'; sought='false' if boolean else '-2'
    relation=f'count(a,{sought})=c'
    source=f'array[-1..1] of var {typ}:a;var int:c;constraint '
    result=sp.translate(source=source+('not ('+relation+')' if negated else relation)+';solve satisfy;',language='minizinc')
    assert result.ok,[d.message for d in result.diagnostic_items]
    assert 'count-value-indicators' in result.report.to_json()
    a=z3.Array('a',z3.IntSort(),z3.BoolSort() if boolean else z3.IntSort())
    expected=z3.Int('c')==z3.Sum(*[z3.If(a[i]==(False if boolean else -2),1,0) for i in range(-1,2)])
    actual=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver=z3.Solver();solver.add(z3.Xor(actual,z3.Not(expected) if negated else expected))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('expression,value',[
    ('count([],4)',0),('count([1,2,1],1)',2),
    ('count(["red","blue","red"],"red")',2),
    ('count(row(array2d(-1..0,4..5,[1,2,1,1]),0),1)',2),
])
def test_empty_duplicate_string_and_row_counts(expression,value):
    result=sp.translate(source=f'constraint {expression}={value};solve satisfy;',language='minizinc')
    assert result.ok,[d.message for d in result.diagnostic_items]
    solver=z3.Solver();solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check()==z3.sat


def test_count_preserves_operand_partiality_under_negation():
    result=sp.translate(source='constraint not (count([1 div 0],1)=0);solve satisfy;',language='minizinc')
    assert result.ok
    solver=z3.Solver();solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check()==z3.sat


def test_boolean_count_objective_reaches_independent_optimizer():
    result=sp.translate(source='array[0..2] of var bool:a;constraint not a[0];'
                        'solve minimize 3*count(a,false);',language='minizinc')
    assert result.ok,[d.message for d in result.diagnostic_items]
    script=result.to_smt2(sp.OmtDialect.Z3);assert '(minimize' in script
    solver=z3.Optimize();solver.from_string(script);assert solver.check()==z3.sat
    a=z3.Array('a',z3.IntSort(),z3.BoolSort())
    cost=3*z3.Sum(*[z3.If(a[i],0,1) for i in range(3)])
    assert solver.model().eval(cost).as_long()==3


@pytest.mark.parametrize('values',[[-1,0],[2,0,1],[1,True,1]])
def test_native_count_value_checks_arity_and_equality_sorts(values):
    def literal(value):
        sort=native.HirSort.boolean() if type(value) is bool else native.HirSort.integer()
        return native._hir_literal(sort,str(value).lower())
    count=native._hir_global('count_value',[literal(v) for v in values])
    model=native.HirModel();model.constrain(native._hir_op('eq',[count,literal(0)]))
    assert not model.translate().ok
