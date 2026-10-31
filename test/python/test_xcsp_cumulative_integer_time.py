"""Complete XCSP cumulative relation and signed-cost regressions.

The official formula quantifies every Int time. The official Java checker also
starts at min(origins), and rangeClosed includes maxEnd, where the load is zero.
"""
import pytest
import z3
import somtparser as sp


def document(variables, body, objective=''):
    return '<instance format="XCSP3" type="'+('COP' if objective else 'CSP')+'"><variables>'+variables+'</variables><constraints>'+body+'</constraints>'+objective+'</instance>'


def translate(text):
    result=sp.translate(source=text,language='xcsp3',dialect=sp.OmtDialect.Z3)
    assert result.ok
    target=z3.Optimize();target.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    return target


def equivalent(left,right):
    solver=z3.Solver();solver.add(z3.Xor(left,right));assert solver.check()==z3.unsat


@pytest.mark.parametrize('starts,lengths,heights,allowed',[
    ((-3,-3),(2,2),(1,1),False),
    ((-1,0),(2,1),(1,1),False),
    ((-3,-1),(2,2),(1,1),True),
    ((-3,-3),(0,2),(7,1),True),
])
def test_negative_and_cross_zero_complete_fixed_relation(starts,lengths,heights,allowed):
    variables=''.join('<var id="s'+str(i)+'">'+str(s)+'</var>' for i,s in enumerate(starts))
    body='<cumulative><origins>s0 s1</origins><lengths>'+' '.join(map(str,lengths))+'</lengths><heights>'+' '.join(map(str,heights))+'</heights><condition>(le,1)</condition></cumulative>'
    target=translate(document(variables,body));s0,s1=z3.Ints('s0 s1')
    expected=z3.And(s0==starts[0],s1==starts[1],z3.BoolVal(allowed))
    equivalent(z3.And(*target.assertions()),expected)


@pytest.mark.parametrize('operator',['eq','ge','gt','ne'])
def test_maximum_end_zero_load_is_checked_not_half_open_horizon(operator):
    bound=0 if operator in ['gt','ne'] else 1
    text=document('<var id="s0">-3</var><var id="s1">-2</var>',
        '<cumulative><origins>s0 s1</origins><lengths>1 1</lengths><heights>1 1</heights><condition>('+operator+','+str(bound)+')</condition></cumulative>')
    target=translate(text)
    # Both tasks fill [-3,-1), but the official checker also tests t=-1.
    equivalent(z3.And(*target.assertions()),z3.BoolVal(False))


def test_all_zero_lengths_have_zero_load_with_negative_origins():
    target=translate(document('<array id="s" size="[2]">-2..0</array>',
        '<cumulative><origins>s[]</origins><lengths>0 0</lengths><heights>7 11</heights><condition>(eq,0)</condition></cumulative>'))
    s=[z3.Int(f's[{i}]') for i in range(2)]
    equivalent(z3.And(*target.assertions()),z3.And(*[z3.And(x>=-2,x<=0) for x in s]))


@pytest.mark.parametrize('direction',['minimize','maximize'])
def test_complete_variable_lengths_ends_gap_and_signed_cost(direction):
    declarations='<array id="s" size="[2]">-2..2</array><array id="l" size="[2]">0..2</array><array id="e" size="[2]">-2..4</array>'
    body='<cumulative><origins>s[]</origins><lengths>l[]</lengths><ends>e[]</ends><heights>1 1</heights><condition>(le,1)</condition></cumulative><intension>ne(s[0],1)</intension>'
    target=translate(document(declarations,body,'<objectives><'+direction+'>sub(e[0],7)</'+direction+'></objectives>'))
    s=[z3.Int(f's[{i}]') for i in range(2)];l=[z3.Int(f'l[{i}]') for i in range(2)];e=[z3.Int(f'e[{i}]') for i in range(2)]
    domains=z3.And(*[z3.And(x>=-2,x<=2) for x in s],*[z3.And(x>=0,x<=2) for x in l],*[z3.And(x>=-2,x<=4) for x in e])
    # All nonzero load lies in [-2,4); these seven integer points plus the
    # zero outside load are a complete independent consequence of the domains.
    loads=[z3.Sum(*[z3.If(z3.And(a<=t,t<a+d),1,0) for a,d in zip(s,l)])<=1 for t in range(-3,5)]
    expected=z3.And(domains,*loads,*[a+d==b for a,d,b in zip(s,l,e)],s[0]!=1)
    equivalent(z3.And(*target.assertions()),expected)
    signed=(e[0]-7) if direction=='minimize' else (7-e[0]);cost=z3.Int('observed_signed_cost')
    assert len(target.objectives())==1
    equivalent(z3.And(*target.assertions(),cost==target.objectives()[0]),z3.And(expected,cost==signed))
    solver=z3.Solver();solver.add(domains,target.objectives()[0]!=signed);assert solver.check()==z3.unsat
    solver=z3.Solver();solver.add(expected,target.objectives()[0]!=-signed);assert solver.check()==z3.sat


def test_negative_height_cancellation_and_gaps_keep_entire_relation():
    target=translate(document('<array id="s" size="[2]">-2..1</array>',
        '<cumulative><origins>s[]</origins><lengths>2 1</lengths><heights>-1 1</heights><condition>(le,0)</condition></cumulative>'))
    a,b=z3.Ints('s[0] s[1]')
    # The positive task must be contained in the negative-height task.
    expected=z3.And(a>=-2,a<=1,b>=-2,b<=1,a<=b,b+1<=a+2)
    equivalent(z3.And(*target.assertions()),expected)
