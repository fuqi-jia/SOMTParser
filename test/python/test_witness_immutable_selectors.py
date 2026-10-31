"""Immutable witness selectors avoid quadratic validation without trusting mutation."""
import gc
import weakref
from types import MappingProxyType
import pytest
import z3
from tools.semantic_checks import existential_definitions as module


class CountingOrdinals(dict):
    def __init__(self, values):
        super().__init__(values)
        self.membership_calls = 0

    def __contains__(self, key):
        self.membership_calls += 1
        return super().__contains__(key)


def counted_index(variables):
    result = module._WitnessDependencyIndex(variables)
    result.ordinals = CountingOrdinals(result.ordinals)
    return result


def equivalent(left, right):
    solver = z3.Solver(); solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_repeated_frozen_full_selector_is_validated_once():
    values = [z3.Int(f'selector_{i}') for i in range(600)]
    variables = {value.get_id():value for value in values}
    index = counted_index(variables); selected = frozenset(variables)
    for _ in range(200):
        assert index.mentions(values[0]+values[-1],selected)=={values[0].get_id(),values[-1].get_id()}
    assert index.ordinals.membership_calls < 2*len(values)


@pytest.mark.parametrize('kind',['dict','set','proxy'])
def test_mutable_same_length_unknown_replacement_is_revalidated(kind):
    x,y=z3.Ints('mutable_x mutable_y');index=counted_index({x.get_id():x})
    underlying={x.get_id():True}if kind in ('dict','proxy')else{x.get_id()}
    selected=MappingProxyType(underlying)if kind=='proxy'else underlying
    assert index.mentions(x,selected)=={x.get_id()}
    if isinstance(underlying,dict):underlying.clear();underlying[y.get_id()]=True
    else:underlying.clear();underlying.add(y.get_id())
    assert len(selected)==1
    with pytest.raises(ValueError,match='unindexed'):index.mentions(x,selected)


@pytest.mark.parametrize('kind',['dict','set','proxy'])
def test_mutable_same_length_valid_replacement_changes_query(kind):
    x,y=z3.Ints('replace_x replace_y');index=counted_index({x.get_id():x,y.get_id():y})
    underlying={x.get_id():True}if kind in ('dict','proxy')else{x.get_id()}
    selected=MappingProxyType(underlying)if kind=='proxy'else underlying
    assert index.mentions(x+y,selected)=={x.get_id()}
    if isinstance(underlying,dict):underlying.clear();underlying[y.get_id()]=True
    else:underlying.clear();underlying.add(y.get_id())
    assert index.mentions(x+y,selected)=={y.get_id()}


def test_invalid_frozen_selector_is_never_cached_as_valid():
    x,y=z3.Ints('invalid_x invalid_y');index=counted_index({x.get_id():x});selected=frozenset([y.get_id()])
    for _ in range(3):
        with pytest.raises(ValueError,match='unindexed'):index.mentions(x,selected)


def test_frozen_selector_strong_reference_prevents_identity_reuse():
    x=z3.Int('retained_x');index=counted_index({x.get_id():x})
    selected=frozenset([x.get_id()]);reference=weakref.ref(selected)
    assert index.mentions(x,selected)=={x.get_id()}
    del selected;gc.collect();assert reference()is not None
    del index;gc.collect();assert reference()is None


def test_frozen_cache_never_suppresses_context_check():
    a,b=z3.Context(),z3.Context();x=z3.Int('context_x',ctx=a);y=z3.Int('context_x',ctx=b)
    index=counted_index({x.get_id():x});selected=frozenset([x.get_id()])
    assert index.mentions(x,selected)=={x.get_id()}
    with pytest.raises(ValueError,match='different Z3 context'):index.mentions(y,selected)


def test_frozenset_subclass_with_mutable_iteration_is_not_cached():
    x,y=z3.Ints('subclass_x subclass_y');index=counted_index({x.get_id():x})
    active=[x.get_id()]
    class ChangingFrozen(frozenset):
        def __iter__(self):return iter(active)
    selected=ChangingFrozen([x.get_id()]);assert index.mentions(x,selected)=={x.get_id()}
    active[:]=[y.get_id()]
    with pytest.raises(ValueError,match='unindexed'):index.mentions(x,selected)


def test_cached_selector_handles_rebuilt_and_nested_quantified_expressions():
    x,y,bound=z3.Ints('rebuilt_x rebuilt_y bound');index=counted_index({x.get_id():x,y.get_id():y});selected=frozenset([x.get_id(),y.get_id()])
    first=z3.ForAll([bound],x+bound>=0)
    assert index.mentions(first,selected)=={x.get_id()}
    second=z3.substitute(first,(x,y+1))
    assert index.mentions(second,selected)=={y.get_id()}
    assert index.mentions(z3.And(first,second),selected)==set(selected)


@pytest.mark.parametrize('kind',['dict','set','frozen'])
def test_selector_forms_match_legacy_dag_occurrences(kind):
    values=[z3.Int(f'legacy_{i}')for i in range(80)];variables={x.get_id():x for x in values};index=counted_index(variables)
    selected=set(list(variables)[::3])
    selected=dict.fromkeys(selected)if kind=='dict'else frozenset(selected)if kind=='frozen'else selected
    expr=z3.Sum(*[z3.If(x>=0,x,-x)for x in values])
    assert index.mentions(expr,selected)==module._mentions(expr,selected)


@pytest.mark.parametrize('dense',[False,True])
def test_sparse_and_dense_occurrences_use_same_validated_selector(dense):
    values=[z3.Int(f'dense_{i}')for i in range(256)];variables={x.get_id():x for x in values};index=counted_index(variables)
    chosen=values if dense else[values[0],values[-1]];expr=z3.Sum(*chosen);selected=frozenset(variables)
    assert index.mentions(expr,selected)=={x.get_id()for x in chosen}
    assert index.mentions(expr,frozenset([values[-1].get_id()]))=={values[-1].get_id()}


def test_definition_batch_does_not_revalidate_all_selected_variables_per_definition():
    values=[z3.Int(f'resolve_{i}')for i in range(400)];public=z3.Int('resolve_public')
    variables={x.get_id():x for x in values};index=counted_index(variables)
    definitions={x.get_id():public+i for i,x in enumerate(values)}
    actual=module._resolve_definition_batch(definitions,variables,index)
    assert len(actual)==len(values)
    assert index.ordinals.membership_calls < 10*len(values)
    for key,value in actual:equivalent(value==definitions[key],z3.BoolVal(True))


def test_linear_direct_batch_reuses_one_full_selector_across_equations():
    values=[z3.Int(f'direct_{i}')for i in range(250)];public=z3.Int('direct_public');g=z3.Bool('direct_guard')
    variables={x.get_id():x for x in values};index=counted_index(variables)
    term=z3.If(g,public,1);clauses=[x+term==i for i,x in enumerate(values)]
    actual=module._direct_batch(clauses,variables,index)
    assert len(actual)==len(values)
    assert index.ordinals.membership_calls < 30*len(values)
    equivalent(z3.And(*[z3.substitute(c,*[(variables[k],v)for k,v in actual])for c in clauses]),z3.BoolVal(True))


def test_conditional_batch_reuses_one_full_selector_across_equations():
    values=[z3.Int(f'conditional_{i}')for i in range(250)];public=z3.Int('conditional_public');g,h=z3.Bools('conditional_guard branch_guard')
    variables={x.get_id():x for x in values};index=counted_index(variables);term=z3.If(h,public,1)
    clauses=[z3.Implies(g,x+term==i)for i,x in enumerate(values)]+[z3.Implies(z3.Not(g),x==0)for x in values]
    actual=module._conditional(clauses,variables,all_definitions=True,dependencies=index)
    assert set(actual)==set(variables)
    assert index.ordinals.membership_calls < 30*len(values)
    equivalent(z3.And(*[z3.substitute(c,*[(variables[k],v)for k,v in actual.items()])for c in clauses]),z3.BoolVal(True))


@pytest.mark.parametrize('sign',[-1,1])
def test_complete_projection_retains_domains_conflicts_and_ordered_costs(sign):
    w,v,public,c0,c1=z3.Ints('final_w final_v final_public final_c0 final_c1');g=z3.Bool('final_g')
    original=z3.Exists([w,v],z3.And(z3.Implies(g,w+public==5),z3.Implies(z3.Not(g),w==0),v==w+1,w>=1,w<=4,c0==sign*v,c1==-2*w))
    actual=module.eliminate_existential_definitions(original)
    value=z3.If(g,5-public,0)
    correct=z3.And(value>=1,value<=4,c0==sign*(value+1),c1==-2*value)
    equivalent(original,actual.formula);equivalent(actual.formula,correct)
    solver=z3.Solver();solver.add(z3.Xor(actual.formula,z3.And(value>=1,value<=4,c1==sign*(value+1),c0==-2*value)))
    assert solver.check()==z3.sat
