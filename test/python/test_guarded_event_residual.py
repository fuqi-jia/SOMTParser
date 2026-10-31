import pytest
import z3

from tools.semantic_checks.guarded_event_residual import prepare_guarded_event_residual


def answer(formula):
    solver = z3.Solver()
    solver.add(formula)
    return solver.check()


@pytest.mark.parametrize('bound', [
    lambda x: x >= 0, lambda x: 0 <= x, lambda x: x > -1,
    lambda x: -1 < x, lambda x: z3.Not(x <= -1),
    lambda x: z3.Not(-1 >= x), lambda x: z3.Not(x < 0),
    lambda x: z3.Not(0 > x),
])
def test_retained_integer_bounds_and_full_query(bound):
    x, y = z3.Ints('x y')
    event = x + y <= 7
    query = z3.And(bound(x), y >= 0,
                   z3.Xor(z3.And(z3.Or(event, x + y <= -1), x >= 0), event))
    proof = prepare_guarded_event_residual(query)
    assert proof is not None
    assert answer(proof.formula) == z3.unsat
    assert answer(query) == z3.unsat
    assert proof.audit['source_conjuncts'] == 2
    assert proof.audit['residual_source_indices'] == [1]


@pytest.mark.parametrize('context,guard', [
    (lambda x,p: p, lambda x: x <= -1),
    (lambda x,p: z3.Or(p, x >= 0), lambda x: x <= -1),
    (lambda x,p: z3.Implies(p, x >= 0), lambda x: x <= -1),
    (lambda x,p: z3.Not(x >= 0), lambda x: x <= -1),
    (lambda x,p: x >= -2, lambda x: x <= -1),
    (lambda x,p: x >= 0, lambda x: x <= 0),
    (lambda x,p: x >= 0, lambda x: -x <= -1),
])
def test_missing_conditional_changed_or_negative_coefficient_bound(context, guard):
    x = z3.Int('x'); p = z3.Bool('p')
    query = z3.And(context(x,p), z3.Xor(z3.Or(p,guard(x)),p))
    assert prepare_guarded_event_residual(query) is None


@pytest.mark.parametrize('sort', ['real', 'bv'])
def test_no_integer_rounding_for_other_sorts(sort):
    x = z3.Real('x') if sort == 'real' else z3.BitVec('x', 8)
    p = z3.Bool('p')
    query = z3.And(x > -1, z3.Xor(z3.Or(p, x <= 0),p))
    assert prepare_guarded_event_residual(query) is None


def test_numeral_parse_and_repeated_coordinate_multiplicity():
    q = z3.parse_smt2_string('''(declare-const x Int)(declare-const p Bool)
    (assert (and (>= x 2) (xor (or p (<= (+ x x (- 1)) 2)) p)))''')[0]
    result = prepare_guarded_event_residual(q)
    assert result is not None
    assert result.audit['removed_guards'][0]['lower_bound'] == 3
    assert answer(q) == answer(result.formula) == z3.unsat


@pytest.mark.parametrize('target', [
    lambda x,y: x+y <= 8,
    lambda x,y: z3.And(x+y <= 7, y == 1),
    lambda x,y: x-y <= 7,
])
def test_changed_target_and_objective_are_not_matched(target):
    x,y = z3.Ints('x y')
    q=z3.And(x>=0,y>=0,z3.Xor(z3.Or(x+y<=7,x+y<=-1),target(x,y)))
    assert prepare_guarded_event_residual(q) is None


def test_complete_addition_commutativity_and_baseline_retention():
    x,y=z3.Ints('x y')
    event=x+y<=7; baseline=x<=2
    q=z3.And(x>=0,y>=0,z3.Xor(z3.And(z3.Or(event,x<=-1),baseline),y+x<=7))
    r=prepare_guarded_event_residual(q)
    assert r is not None and r.audit['residual_source_indices']==[1]
    assert answer(r.formula)==z3.sat
    assert answer(q)==z3.sat


def test_target_events_may_prove_baseline_but_never_become_shared_facts():
    x=z3.Int('x');event=x==0;baseline=x<=0
    q=z3.And(x>=0,z3.Xor(z3.And(z3.Or(event,x<=-1),baseline),event))
    strong=prepare_guarded_event_residual(q)
    complete=prepare_guarded_event_residual(q,retain_target_events=True)
    assert answer(strong.formula)==z3.sat
    assert answer(complete.formula)==z3.unsat
    assert answer(q)==z3.unsat
    assert not strong.audit['target_event_premise']
    assert complete.audit['target_event_premise']


def test_no_source_branch_bound_borrowing():
    x=z3.Int('x');p=z3.Bool('p')
    q=z3.And(z3.BoolVal(True),z3.Xor(z3.And(x>=0,z3.Or(p,x<=-1)),p))
    assert prepare_guarded_event_residual(q) is None


def test_multiple_residuals_and_all_events_covered():
    x,y=z3.Ints('x y');a=x<=5;b=y<=8
    left=z3.And(z3.Or(a,x<=-1),x>=0,z3.Or(b,y<=-1),y>=0)
    q=z3.And(x>=0,y>=0,z3.Xor(left,z3.And(b,a)))
    r=prepare_guarded_event_residual(q)
    assert r is not None and r.audit['residual_source_indices']==[1,3]
    assert [g['source_index']for g in r.audit['removed_guards']]==[0,2]
    assert answer(q)==answer(r.formula)==z3.unsat


def test_unmatched_event_cannot_be_dropped():
    x=z3.Int('x');a,b=z3.Bools('a b')
    q=z3.And(x>=0,z3.Xor(z3.And(z3.Or(a,x<=-1),z3.Or(b,x<=-1)),a))
    assert prepare_guarded_event_residual(q) is None


def test_positive_bound_in_nested_shared_and_is_unconditional():
    x=z3.Int('x');p=z3.Bool('p')
    q=z3.And(z3.And(x>=0,x<=3),z3.Xor(z3.Or(p,x<=-1),p))
    r=prepare_guarded_event_residual(q)
    assert r is not None and answer(r.formula)==z3.unsat


def test_custom_context():
    c=z3.Context();x=z3.Int('x',ctx=c);p=z3.Bool('p',ctx=c)
    q=z3.And(x>=0,z3.Xor(z3.Or(p,x<=-1),p))
    r=prepare_guarded_event_residual(q)
    s=z3.Solver(ctx=c);s.add(r.formula);assert s.check()==z3.unsat
