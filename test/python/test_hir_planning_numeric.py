"""Public planning numeric API versus independent complete Real relations."""
import pytest
from somtparser import _somtparser as n
import z3


def fixture():
    model=n.HirModel()
    real,boolean=n.HirSort.real(),n.HirSort.boolean()
    def cell(name):
        return n.HirNumericStateCell(model.declare(name,real),model.declare(name+'d',boolean))
    before=[cell('x'),cell('y')]
    after=[cell('nx'),cell('ny')]
    return model,before,after,model.declare('a',boolean),model.declare('b',boolean)


def relation(model):
    result=model.translate()
    assert result.ok,[d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def attach(model,before,after,updates):
    original=model.translate().to_smt2()
    constraints=n.planning_numeric_transition(model,before,after,updates)
    assert model.translate().to_smt2()==original
    for expression in constraints:
        model.constrain(expression)
    return relation(model)


def exact(actual,expected):
    solver=z3.Solver()
    solver.add(z3.Xor(actual,expected))
    assert solver.check()==z3.unsat


def symbols():
    x,y,nx,ny=z3.Reals('x y nx ny')
    xd,yd,nxd,nyd,a,b=z3.Bools('xd yd nxd nyd a b')
    canonical=z3.And(z3.Implies(z3.Not(xd),x==0),z3.Implies(z3.Not(yd),y==0))
    return x,y,nx,ny,xd,yd,nxd,nyd,a,b,canonical


def test_simultaneous_swap_and_read_metadata():
    model,before,after,a,b=fixture()
    xread=n.planning_numeric_read(before[0],0)
    yread=n.planning_numeric_read(before[1],1)
    assert xread.reads==[0] and yread.reads==[1]
    combined=n.planning_numeric_arithmetic('+',[yread,xread,yread])
    assert combined.reads==[0,1]
    actual=attach(model,before,after,[
        n.HirNumericUpdate(0,n.NumericUpdateKind.ASSIGN,yread,a,'swap'),
        n.HirNumericUpdate(1,n.NumericUpdateKind.ASSIGN,xread,a,'swap')])
    x,y,nx,ny,xd,yd,nxd,nyd,az,bz,canon=symbols()
    exact(actual,z3.And(canon,z3.Implies(az,z3.And(xd,yd)),
        nxd==z3.Or(xd,az),nyd==z3.Or(yd,az),
        nx==z3.If(z3.Or(xd,az),z3.If(az,y,x),0),
        ny==z3.If(z3.Or(yd,az),z3.If(az,x,y),0)))
    # A sequential x:=y; y:=x interpretation disagrees on a real witness.
    mutant=z3.Solver();mutant.add(actual,az,x==2,y==3,xd,yd,ny!=3)
    assert mutant.check()==z3.sat


def test_guarded_division_and_assignment_initialization():
    model,before,after,a,b=fixture()
    quotient=n.planning_numeric_arithmetic('/',[
        n.planning_numeric_constant('10'),n.planning_numeric_read(before[1],1)])
    actual=attach(model,before,after,[n.HirNumericUpdate(0,n.NumericUpdateKind.ASSIGN,quotient,a,'divide')])
    x,y,nx,ny,xd,yd,nxd,nyd,az,bz,canon=symbols()
    exact(actual,z3.And(canon,z3.Implies(az,z3.And(yd,y!=0)),
        nxd==z3.Or(xd,az),nx==z3.If(z3.Or(xd,az),z3.If(az,10/y,x),0),
        nyd==yd,ny==y))
    inactive=z3.Solver();inactive.add(actual,z3.Not(az),y==0,yd,z3.Not(xd))
    assert inactive.check()==z3.sat
    active=z3.Solver();active.add(actual,az,y==0,yd)
    assert active.check()==z3.unsat


def test_exact_signed_additive_weights_require_defined_accumulator():
    model,before,after,a,b=fixture()
    actual=attach(model,before,after,[
        n.HirNumericUpdate(0,n.NumericUpdateKind.INCREASE,n.planning_numeric_constant('-3/2'),a,'A'),
        n.HirNumericUpdate(0,n.NumericUpdateKind.DECREASE,n.planning_numeric_constant('2/3'),b,'B')])
    x,y,nx,ny,xd,yd,nxd,nyd,az,bz,canon=symbols()
    exact(actual,z3.And(canon,z3.Implies(z3.Or(az,bz),xd),nxd==xd,nyd==yd,ny==y,
        nx==z3.If(xd,x-z3.If(az,z3.RealVal('3/2'),0)-z3.If(bz,z3.RealVal('2/3'),0),0)))


@pytest.mark.parametrize('same_owner',[True,False])
def test_scaling_same_action_or_endpoint_interference(same_owner):
    model,before,after,a,b=fixture()
    actual=attach(model,before,after,[
        n.HirNumericUpdate(0,n.NumericUpdateKind.SCALE_UP,n.planning_numeric_constant('2'),a,'A'),
        n.HirNumericUpdate(0,n.NumericUpdateKind.SCALE_DOWN,n.planning_numeric_constant('3'),b,'A' if same_owner else 'B')])
    x,y,nx,ny,xd,yd,nxd,nyd,az,bz,canon=symbols()
    exact(actual,z3.And(canon,z3.Implies(z3.Or(az,bz),xd),nxd==xd,nyd==yd,ny==y,
        nx==z3.If(xd,x*z3.If(az,2,1)/z3.If(bz,3,1),0),
        z3.BoolVal(True) if same_owner else z3.Not(z3.And(az,bz))))


def test_undefined_boolean_context_cannot_recover_truth():
    model,before,after,a,b=fixture()
    comparison=n.planning_numeric_compare('>',n.planning_numeric_read(before[0],0),n.planning_numeric_constant('0'))
    true=n.planning_numeric_predicate(n._hir_literal(n.HirSort.boolean(),'true'))
    neg=n.planning_numeric_logical('not',[comparison])
    disjunction=n.planning_numeric_logical('or',[true,comparison])
    model.constrain(n._hir_op('eq',[a,n.planning_numeric_satisfied(neg)]))
    model.constrain(n._hir_op('eq',[b,n.planning_numeric_satisfied(disjunction)]))
    actual=attach(model,before,after,[])
    x,y,nx,ny,xd,yd,nxd,nyd,az,bz,canon=symbols()
    exact(actual,z3.And(canon,nx==x,ny==y,nxd==xd,nyd==yd,
                        az==z3.And(xd,x<=0),bz==xd))


@pytest.mark.parametrize('bad',['future','wrong_read_metadata','bad_guard','missing_owner','target_outside'])
def test_invalid_transition_is_atomic(bad):
    model,before,after,a,b=fixture()
    value=n.planning_numeric_constant('2')
    target,guard,owner=0,a,'A'
    if bad=='future':value=n.HirNumericValue(after[0].value,after[0].defined,[0])
    if bad=='wrong_read_metadata':value=n.HirNumericValue(before[0].value,before[0].defined,[])
    if bad=='bad_guard':guard=n._hir_literal(n.HirSort.integer(),'1')
    if bad=='missing_owner':owner=''
    if bad=='target_outside':target=2
    original=model.translate().to_smt2()
    with pytest.raises(ValueError):
        n.planning_numeric_transition(model,before,after,[n.HirNumericUpdate(target,n.NumericUpdateKind.ASSIGN,value,guard,owner)])
    assert model.translate().to_smt2()==original


@pytest.mark.parametrize('bad',['NaN','1/0','infinity','0/0','-7/000','-1/000','+1/00','000/000'])
def test_non_real_literals_are_refused(bad):
    with pytest.raises(ValueError):n.planning_numeric_constant(bad)


def test_int_weight_does_not_become_real_implicitly():
    with pytest.raises(ValueError):
        n.HirNumericValue(n._hir_literal(n.HirSort.integer(),'1'),n._hir_literal(n.HirSort.boolean(),'true'),[])


@pytest.mark.parametrize('value', ['0/0003', '+1/0002', '-7/0002',
    '1/100000000000000000000000000000000000007'])
def test_exact_rational_literals_keep_nonzero_unbounded_denominators(value):
    model = n.HirModel()
    actual = model.declare('amount', n.HirSort.real())
    literal = n.planning_numeric_constant(value)
    model.constrain(n._hir_op('eq', [actual, literal.value]))
    exact(relation(model), z3.Real('amount') == z3.RealVal(value))

@pytest.mark.parametrize('text',['0/7','0/0007','-3/2','+1/0002',
                               '1/100000000000000000000000000000000000000'])
def test_exact_rational_constants_preserve_their_value(text):
    model=n.HirModel()
    x=model.declare('x',n.HirSort.real())
    constant=n.planning_numeric_constant(text)
    assert constant.reads==[]
    model.constrain(constant.defined)
    model.constrain(n._hir_op('eq',[x,constant.value]))
    exact(relation(model),z3.Real('x')==z3.RealVal(text))


