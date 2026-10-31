"""Shared scheduling lowering compared with an independent integer-time grid."""
import pytest
import z3
import somtparser as sp
from somtparser import _somtparser as native
from somtparser.hir import build_hir
from somtparser.hir_cp import expand_cp_model


def lit(value):
    return {'literal': value, 'sort': 'Int'}


def model(expression, names=()):
    return dict(schema='somt-hir-model-v1', language='hir', decision='satisfiability',
                declarations=[dict(name=name, sort='Int') for name in names],
                functions=[], constraints=[dict(expr=expression, span=[0, 1])],
                objectives=[], objective_order='single', goal=None, assumptions=[], unresolved=[])


def formula(source):
    result = sp.translate(source=source+' solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result, z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))


@pytest.mark.parametrize('negated', [False, True])
def test_variable_scheduling_matches_every_bounded_assignment(negated):
    names=['s0','s1','d0','d1','r0','r1','b']
    values={name:z3.Int(name) for name in names}
    expr={'cp':'cumulative', 'starts':[{'var':x} for x in names[:2]],
          'durations':[{'var':x} for x in names[2:4]],
          'demands':[{'var':x} for x in names[4:6]], 'capacity':{'var':'b'}}
    if negated:expr={'op':'not','args':[expr]}
    source=model(expr,names)
    result=build_hir(source,'x').translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert 'cumulative-start-events' in result.report.to_json()
    actual=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected=z3.And(values['b']>=0, *[values[n]>=0 for n in names[2:6]], *[
        z3.Sum(*[z3.If(z3.And(values[f's{i}']<=t,t<values[f's{i}']+values[f'd{i}']),
                       values[f'r{i}'],0) for i in range(2)])<=values['b']
        for t in range(-2,6)])
    solver=z3.Solver();solver.set(timeout=10000)
    for n,v in values.items():
        solver.add(v>=(-2 if n.startswith('s') else -1),v<=(2 if n.startswith('s') else 3))
    solver.add(z3.Xor(actual,z3.Not(expected) if negated else expected))
    assert solver.check()==z3.unsat
    # The public expansion API remains equivalent to direct native globals.
    expanded=build_hir(expand_cp_model(source),'x').translate()
    assert expanded.ok
    solver=z3.Solver();solver.set(timeout=10000)
    solver.add(z3.Xor(actual,z3.And(*z3.parse_smt2_string(expanded.to_smt2()))))
    assert solver.check()==z3.unsat


def test_start_time_has_no_artificial_horizon():
    expr={'cp':'cumulative','starts':[lit(-10**30),lit(-10**30+1)],
          'durations':[2,2],'demands':[1,1],'capacity':lit(1)}
    result=build_hir(model(expr),'x').translate();assert result.ok
    solver=z3.Solver();solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('call', [
    'cumulative([x,y],[2,1],[1,1],1)',
    'cumulative(row(array2d(-1..0,4..5,[x,y,0,0]),-1),array1d(4..5,[2,1]),array1d(4..5,[1,1]),1)',
    'cumulative(col(array2d(4..5,-1..0,[x,0,y,0]),-1),array1d(4..5,[2,1]),array1d(4..5,[1,1]),1)',
])
@pytest.mark.parametrize('negated', [False, True])
def test_minizinc_indexed_vectors_and_matrix_slices(call,negated):
    x,y=z3.Ints('x y')
    result,actual=formula('var int:x;var int:y;constraint '+('not '+call if negated else call)+';')
    assert 'cumulative-start-events' in result.report.to_json()
    expected=z3.Or(x+2<=y,y+1<=x)
    solver=z3.Solver();solver.add(z3.Xor(actual,z3.Not(expected) if negated else expected))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('call,expected', [
    ('cumulative([],[],[],-1)',True),
    ('cumulative([0],[0],[9],0)',True),
    ('cumulative([0,1],[1,1],[1,1],1)',True),
    ('not cumulative([1 div 0],[1],[1],1)',True),
])
def test_empty_zero_duration_touching_and_partiality(call,expected):
    _,actual=formula('constraint '+call+';')
    solver=z3.Solver();solver.add(actual)
    assert solver.check()==(z3.sat if expected else z3.unsat)


@pytest.mark.parametrize('call', [
    'cumulative([0],[1,1],[1],1)',
    'cumulative(array1d(2..2,[0]),[1],[1],1)',
    'cumulative([true],[1],[1],1)',
    'cumulative([0],[1],[1],true)',
    'cumulative(row([0],1),[1],[1],1)',
])
def test_malformed_scheduling_is_rejected(call):
    result=sp.translate(source='constraint '+call+';solve satisfy;',language='minizinc')
    assert not result.ok


@pytest.mark.parametrize('args', [[1,2],[1,2,3],[True],[1,0,1,False]])
def test_native_global_checks_shape_and_types(args):
    def value(x):
        sort=native.HirSort.boolean() if type(x) is bool else native.HirSort.integer()
        return native._hir_literal(sort,str(x).lower())
    raw=native.HirModel();raw.constrain(native._hir_global('cumulative',[value(x) for x in args]))
    assert not raw.translate().ok
