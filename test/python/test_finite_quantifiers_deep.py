"""Deep source DAGs must not depend on the Python recursion limit."""
import pytest
import z3
from tools.semantic_checks.finite_quantifiers import expand_finite_int_quantifiers


def deep_context(body, depth=1600):
    gate, fallback = z3.Bools('deep_gate deep_fallback')
    for _ in range(depth):
        body = z3.If(gate, body, fallback)
    return body


def equivalent(left, right):
    solver=z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(left,right))
    assert solver.check()==z3.unsat


def test_deep_unexpanded_dag_is_preserved_exactly():
    original=deep_context(z3.Bool('leaf'))
    result=expand_finite_int_quantifiers(original)
    assert result.formula.eq(original)
    assert result.stats.expanded_quantifiers==0
    assert not result.stats.budget_exhausted


@pytest.mark.parametrize('polarity',['forall','exists'])
def test_deep_context_preserves_finite_binder_semantics(polarity):
    x, value=z3.Ints('deep_bound public_value')
    guard=z3.And(x>=-1,x<=1)
    body=x==value
    bound=(z3.ForAll([x],z3.Implies(guard,body)) if polarity=='forall'
           else z3.Exists([x],z3.And(guard,body)))
    original=deep_context(bound)
    result=expand_finite_int_quantifiers(original)
    assert result.stats.expanded_quantifiers==1
    assert result.stats.expanded_instances==3
    expected=(z3.And(*[value==i for i in range(-1,2)]) if polarity=='forall'
              else z3.Or(*[value==i for i in range(-1,2)]))
    equivalent(result.formula,deep_context(expected))


def test_deep_instantiated_body_is_rewritten_without_losing_a_guard():
    x, value=z3.Ints('deep_body_bound deep_body_value')
    enabled=z3.Bool('deep_enabled')
    body=deep_context(x==value)
    formula=z3.ForAll([x],z3.Implies(z3.And(x>=0,x<=0,enabled),body))
    result=expand_finite_int_quantifiers(formula)
    assert result.stats.expanded_quantifiers==1
    equivalent(result.formula,z3.Implies(enabled,deep_context(value==0)))


def test_deep_conjunctive_guard_uses_every_original_restriction():
    x, value=z3.Ints('deep_guard_bound deep_guard_value')
    enabled=z3.Bool('deep_guard_enabled')
    guard=z3.And(x>=0,x<=1)
    for _ in range(1600):
        guard=z3.And(enabled,guard)
    formula=z3.ForAll([x],z3.Implies(guard,value>x))
    result=expand_finite_int_quantifiers(formula)
    assert result.stats.expanded_quantifiers==1
    equivalent(result.formula,z3.Implies(enabled,value>1))


def test_deep_nested_finite_binders_use_explicit_frames():
    depth=1100
    x=z3.Int('nested_frame_bound')
    leaf=z3.Bool('nested_frame_leaf')
    formula=leaf
    for _ in range(depth):
        formula=z3.ForAll([x],z3.Implies(z3.And(x>=0,x<=0),formula))
    result=expand_finite_int_quantifiers(formula,max_ast_nodes=20000000)
    assert not result.stats.budget_exhausted
    assert result.stats.expanded_quantifiers==depth
    assert result.stats.expanded_instances==depth
    assert z3.simplify(result.formula).eq(leaf)


def test_budget_abort_discards_every_pending_deep_frame():
    x=z3.Int('deep_budget_bound')
    inner=z3.ForAll([x],z3.Implies(z3.And(x>=0,x<3),x>=0))
    formula=deep_context(inner)
    result=expand_finite_int_quantifiers(formula,max_enumerated_tuples=2)
    assert result.stats.budget_exhausted
    assert result.formula.eq(formula)
    assert result.stats.expanded_quantifiers==0


def test_shared_deep_dag_expands_one_binder_once():
    x=z3.Int('deep_shared_bound')
    array=z3.Array('deep_shared_array',z3.IntSort(),z3.IntSort())
    bound=z3.ForAll([x],z3.Implies(z3.And(x>=0,x<2),array[x]>0))
    shared=deep_context(bound)
    formula=z3.Or(shared,shared)
    result=expand_finite_int_quantifiers(formula)
    assert result.stats.expanded_quantifiers==1
    assert result.stats.expanded_instances==2
    equivalent(result.formula,deep_context(z3.And(array[0]>0,array[1]>0)))


def test_unsupported_binder_inside_deep_context_stays_whole():
    x=z3.Int('deep_unbounded')
    quantified=z3.ForAll([x],x>=0)
    formula=deep_context(quantified)
    result=expand_finite_int_quantifiers(formula)
    assert result.formula.eq(formula)
    assert result.stats.skipped_quantifiers==1
    assert not result.stats.budget_exhausted
