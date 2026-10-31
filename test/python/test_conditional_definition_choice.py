"""Prefer exact independent definitions while preserving every original constraint."""
import itertools
import pytest
import z3
from tools.semantic_checks import existential_definitions as module


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def unequal(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.sat


def example(aggregate_first, total_first, reverse):
    a,b,c,d,e,f = z3.Bools('a b c d e f')
    w,v,total,x,y = z3.Ints('w v total x y')
    scalar = [z3.Or(w+x == 7,z3.Not(a),z3.Not(b)), z3.Or(w == 0,z3.And(a,b)),
              z3.Or(v-x == 2,z3.Not(c),z3.Not(d)), z3.Or(v == 0,z3.And(c,d))]
    term = total-w-v if total_first else -w-v+total
    aggregate = [z3.Or(term == 5,z3.Not(e),z3.Not(f)),z3.Or(term == 0,z3.And(e,f))]
    clauses = aggregate+scalar if aggregate_first else scalar+aggregate
    if reverse:
        clauses.reverse()
    value = z3.If(z3.And(a,b),7-x,0)+z3.If(z3.And(c,d),2+x,0)+z3.If(z3.And(e,f),5,0)
    return [w,v,total], clauses, (total,x,y), value


@pytest.mark.parametrize('aggregate_first,total_first,reverse', list(itertools.product([False,True],repeat=3)))
def test_aggregate_and_scalar_equation_order_has_no_residual_witness(aggregate_first,total_first,reverse):
    variables,clauses,(total,x,y),value = example(aggregate_first,total_first,reverse)
    original = z3.Exists(variables,z3.And(*clauses,total>=0,y>=total))
    actual = module.eliminate_existential_definitions(original)
    assert actual.conditional_definitions == 3
    assert not z3.is_quantifier(actual.formula)
    equivalent(original,actual.formula)
    equivalent(actual.formula,z3.And(value>=0,y>=value))


@pytest.mark.parametrize('reverse',[False,True])
def test_same_guard_branch_prefers_fewer_witnesses(reverse):
    g=z3.Bool('g');w,v,x,y=z3.Ints('w v x y')
    clauses=[z3.Implies(g,w==v+x),z3.Implies(g,w==x),z3.Implies(z3.Not(g),w==0),
             z3.Implies(g,v==y),z3.Implies(z3.Not(g),v==0)]
    if reverse:clauses.reverse()
    variables={w.get_id():w,v.get_id():v}
    found=module._conditional(clauses,variables,all_definitions=True,
                              dependencies=module._WitnessDependencyIndex(variables))
    assert module._mentions(found[w.get_id()],variables)==set()
    original=z3.Exists([w,v],z3.And(*clauses))
    actual=module.eliminate_existential_definitions(original)
    assert not z3.is_quantifier(actual.formula)
    equivalent(original,actual.formula)
    equivalent(actual.formula,z3.Or(z3.Not(g),y==0))
    unequal(actual.formula,z3.BoolVal(True))


@pytest.mark.parametrize('reverse',[False,True])
def test_different_guards_prefer_independent_complete_definition(reverse):
    a,b=z3.Bools('a b');w,v,x,y=z3.Ints('w v x y')
    clauses=[z3.Implies(a,w==v+1),z3.Implies(z3.Not(a),w==v-1),
             z3.Implies(b,w==x),z3.Implies(z3.Not(b),w==y)]
    if reverse:clauses.reverse()
    variables={w.get_id():w,v.get_id():v}
    found=module._conditional(clauses,variables,all_definitions=True,
                              dependencies=module._WitnessDependencyIndex(variables))
    assert module._mentions(found[w.get_id()],variables)==set()
    actual=module.eliminate_existential_definitions(z3.Exists([w,v],z3.And(*clauses,v>=0)))
    expected=z3.Exists([v],z3.And(*[z3.substitute(c,(w,z3.If(b,x,y)))for c in clauses],v>=0))
    equivalent(actual.formula,expected)


@pytest.mark.parametrize('cycle_offset',[0,1])
def test_actual_dependency_cycle_is_not_assumed_solvable(cycle_offset):
    g=z3.Bool('g');w,v,y=z3.Ints('w v y')
    clauses=[z3.Implies(g,w==v+1),z3.Implies(z3.Not(g),w==v-1),
             z3.Implies(g,v==w+cycle_offset),z3.Implies(z3.Not(g),v==w-1),y>=w]
    variables={w.get_id():w,v.get_id():v}
    found=module._conditional(clauses,variables,all_definitions=True)
    assert module._resolve_definition_batch(found,variables)==()
    original=z3.Exists([w,v],z3.And(*clauses))
    actual=module.eliminate_existential_definitions(original)
    equivalent(original,actual.formula)
    solver=z3.Solver();solver.add(actual.formula)
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('sign',[-1,1])
def test_original_domains_and_ordered_cost_coordinates_remain(sign):
    variables,clauses,(total,x,y),value=example(True,False,False)
    c0,c1=z3.Ints('c0 c1')
    # Observation bounds and costs cannot become definitions of private variables.
    cost0=sign*z3.If(total>=0,total,-total)
    cost1=z3.If(total>=3,-2*total,-total)
    constraints=[total>=1,total<=9,y>=total,c0==cost0,c1==cost1]
    original=z3.Exists(variables,z3.And(*clauses,*constraints))
    actual=module.eliminate_existential_definitions(original)
    assert not z3.is_quantifier(actual.formula)
    projected0=sign*z3.If(value>=0,value,-value)
    projected1=z3.If(value>=3,-2*value,-value)
    correct=z3.And(value>=1,value<=9,y>=value,c0==projected0,c1==projected1)
    equivalent(original,actual.formula);equivalent(actual.formula,correct)
    unequal(actual.formula,z3.And(y>=value,c0==projected0,c1==projected1))
    unequal(actual.formula,z3.And(value>=1,value<=9,y>=value,c1==projected0,c0==projected1))


@pytest.mark.parametrize('mode',['missing','self-guard','same-polarity'])
def test_dependency_preference_cannot_invent_a_complete_guard_cover(mode):
    g=z3.Bool('g');w,v,y=z3.Ints('w v y')
    clauses=[z3.Implies(g,w==v+1),z3.Implies(g,w==2)]
    if mode=='self-guard':clauses=[z3.Implies(w>0,w==v+1),z3.Implies(w>0,w==2)]
    elif mode=='same-polarity':clauses.append(z3.Implies(g,w==3))
    original=z3.Exists([w,v],z3.And(*clauses,w>=0,y>=w))
    actual=module.eliminate_existential_definitions(original)
    assert actual.formula.eq(original)
    assert actual.conditional_definitions==actual.direct_definitions==0


def test_equal_dependency_ties_keep_first_candidate_without_erasing_conflict():
    g=z3.Bool('g');w,x,y=z3.Ints('w x y')
    clauses=[z3.Implies(g,w==x),z3.Implies(g,w==y),z3.Implies(z3.Not(g),w==0)]
    found=module._conditional(clauses,{w.get_id():w},all_definitions=True)
    equivalent(found[w.get_id()]==z3.If(g,x,0),z3.BoolVal(True))
    original=z3.Exists([w],z3.And(*clauses))
    actual=module.eliminate_existential_definitions(original)
    equivalent(original,actual.formula)
    equivalent(actual.formula,z3.Or(z3.Not(g),x==y))
