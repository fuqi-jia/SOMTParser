"""Defined HIR helpers must not conceal planning state dependencies."""
import pytest
import z3
from somtparser import _somtparser as n


def fixture():
    model=n.HirModel()
    real,boolean=n.HirSort.real(),n.HirSort.boolean()
    def cell(name):
        return n.HirNumericStateCell(model.declare(name,real),model.declare(name+'d',boolean))
    before,after=cell('x'),cell('nx')
    enabled=model.declare('enabled',boolean)
    return model,before,after,enabled


def helper(model,name,body):
    model.declare_function(name,[],body.sort,auxiliary=True)
    model.define_function(name,[],body)
    return n._hir_apply(name,body.sort,[])


def body(model):
    translated=model.translate()
    assert translated.ok,[d.message for d in translated.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(translated.to_smt2()))


@pytest.mark.parametrize('place',['rhs_value','rhs_defined','guard'])
@pytest.mark.parametrize('selected',[True,False])
def test_transitive_helper_cannot_hide_future_state(place,selected):
    model,before,after,enabled=fixture()
    leaf=after.value if place=='rhs_value' else after.defined
    inner=helper(model,'inner',leaf)
    outer=helper(model,'outer',inner)
    rhs=n.planning_numeric_constant('1')
    guard=n._hir_literal(n.HirSort.boolean(),'true' if selected else 'false')
    if place=='rhs_value':rhs=n.HirNumericValue(outer,rhs.defined,[])
    if place=='rhs_defined':rhs=n.HirNumericValue(rhs.value,outer,[])
    if place=='guard':guard=n._hir_op('and',[guard,outer])
    snapshot=model.translate().to_smt2()
    with pytest.raises(ValueError,match='old state only'):
        n.planning_numeric_transition(model,[before],[after],[
            n.HirNumericUpdate(0,n.NumericUpdateKind.ASSIGN,rhs,guard,'A')])
    assert model.translate().to_smt2()==snapshot


@pytest.mark.parametrize('where',['value','defined'])
def test_old_state_read_metadata_covers_defined_function_bodies(where):
    model,before,after,enabled=fixture()
    constant=n.planning_numeric_constant('3')
    term=helper(model,'read_old',before.value if where=='value' else before.defined)
    rhs=n.HirNumericValue(term if where=='value' else constant.value,
                          term if where=='defined' else constant.defined,[])
    with pytest.raises(ValueError,match='read metadata'):
        n.planning_numeric_transition(model,[before],[after],[
            n.HirNumericUpdate(0,n.NumericUpdateKind.ASSIGN,rhs,enabled,'A')])


def test_valid_defined_helper_preserves_complete_old_state_relation():
    model,before,after,enabled=fixture()
    value=helper(model,'old_value',before.value)
    defined=helper(model,'old_defined',before.defined)
    # An unrelated helper can mention a successor. It is never read by this
    # transition and must not be rejected merely for existing in the context.
    helper(model,'unused_future',after.value)
    one=n.planning_numeric_constant('1')
    old=n.HirNumericValue(value,defined,[0])
    rhs=n.planning_numeric_arithmetic('+',[old,one])
    snapshot=model.translate().to_smt2()
    rows=n.planning_numeric_transition(model,[before],[after],[
        n.HirNumericUpdate(0,n.NumericUpdateKind.ASSIGN,rhs,enabled,'A')])
    assert model.translate().to_smt2()==snapshot
    for row in rows:model.constrain(row)
    x,nx=z3.Reals('x nx');xd,nxd,a=z3.Bools('xd nxd enabled')
    expected=z3.And(z3.Implies(z3.Not(xd),x==0),z3.Implies(a,xd),
        nxd==xd,nx==z3.If(xd,z3.If(a,x+1,x),0))
    solver=z3.Solver();solver.add(z3.Xor(body(model),expected))
    assert solver.check()==z3.unsat


def test_bound_formal_and_old_actual_argument_keep_separate_scope():
    model,before,after,enabled=fixture()
    real=n.HirSort.real()
    formal=n._hir_ident('formal',real,True)
    model.declare_function('identity',[real],real,auxiliary=True)
    model.define_function('identity',[('formal',real)],formal)
    call=n._hir_apply('identity',real,[before.value])
    rhs=n.HirNumericValue(call,before.defined,[0])
    rows=n.planning_numeric_transition(model,[before],[after],[
        n.HirNumericUpdate(0,n.NumericUpdateKind.ASSIGN,rhs,enabled,'A')])
    for row in rows:model.constrain(row)
    x,nx=z3.Reals('x nx');xd,nxd,a=z3.Bools('xd nxd enabled')
    expected=z3.And(z3.Implies(z3.Not(xd),x==0),z3.Implies(a,xd),nxd==xd,nx==x)
    solver=z3.Solver();solver.add(z3.Xor(body(model),expected))
    assert solver.check()==z3.unsat
