"""Method substitutions over relations that no source effect can add to."""
from itertools import product

import pytest
import somtparser as sp
import z3


def encode(tmp_path, body, initial='', tasks='(t)', horizon=1, depth=1,
           network=':subtasks', goal='(and)'):
    domain = ('''(define (domain d) (:requirements :adl :hierarchy :htn-method-pre-eff)
      (:types obj) (:constants a b - obj)
      (:predicates (edge ?x ?y - obj) (ready ?x - obj) (p) (done)) ''' + body + ')')
    problem = tmp_path / 'problem.hddl'
    problem.write_text(f'(define (problem p) (:domain d) (:htn {network} {tasks}) '
                       f'(:init {initial}) (:goal {goal}))')
    result = sp.translate(source=domain, data=[str(problem)], language='hddl', profile='bmc',
                          options={'plan_horizon': str(horizon), 'decomposition_depth': str(depth)})
    return result


def solve(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


@pytest.mark.parametrize('delete_relation', [False, True])
@pytest.mark.parametrize('condition_site', ['method', 'primitive'])
def test_sparse_method_join_before_quadratic_local_grounding(tmp_path, delete_relation, condition_site):
    # 350**2 substitutions exceed the old grounding guard. Only 350 sparse
    # edges can ever satisfy the method condition, even if edges are deleted.
    n = 350
    objects = ' '.join(f'c{i}' for i in range(n))
    condition = ':precondition (edge ?x ?y)'
    domain = (f'''(define (domain d) (:requirements :adl :hierarchy :method-preconditions)
      (:constants {objects}) (:predicates (edge ?x ?y) (done)) (:task t)
      (:method choose :parameters (?x ?y) :task (t)
        {condition if condition_site == 'method' else ''} :subtasks (act ?x ?y))
      (:action act :parameters (?x ?y)
        {condition if condition_site == 'primitive' else ''} :effect (done))'''
      + ('(:action drop :parameters (?x ?y) :effect (not (edge ?x ?y)))' if delete_relation else '') + ')')
    problem = tmp_path / 'problem.hddl'
    edges = ' '.join(f'(edge c{i} c{(i+1)%n})' for i in range(n))
    problem.write_text(f'(define (problem p) (:domain d) (:htn :subtasks (t)) '
                       f'(:init {edges}) (:goal (done)))')
    result = sp.translate(source=domain, data=[str(problem)], language='hddl', profile='bmc',
                          options={'plan_horizon': '1', 'decomposition_depth': '1'})
    assert solve(result) == z3.sat


@pytest.mark.parametrize('initial', ['', '(edge a b)'])
@pytest.mark.parametrize('delete_first', [False, True])
def test_initial_candidate_is_still_checked_at_method_execution(tmp_path, initial, delete_first):
    body = ('''(:task t :parameters (?x ?y - obj))
      (:method choose :parameters (?x ?y - obj) :task (t ?x ?y)
        :precondition (edge ?x ?y) :effect (done))
      (:action drop :effect (not (edge a b)))''')
    result = encode(tmp_path, body, initial,
                    tasks='(and (drop) (t a b))' if delete_first else '(t a b)',
                    network=':ordered-subtasks', horizon=int(delete_first), goal='(done)')
    assert solve(result) == (z3.sat if initial and not delete_first else z3.unsat)


@pytest.mark.parametrize('producer', ['action', 'method', 'quantified-conditional'])
def test_positive_effects_prevent_initial_state_pruning(tmp_path, producer):
    effect = ('(forall (?x - obj) (when (ready ?x) (edge ?x ?x)))'
              if producer == 'quantified-conditional' else '(edge a a)')
    before = ('(:task before) (:method establish :task (before) :effect ' + effect + ')'
              if producer == 'method' else '(:action before :effect ' + effect + ')')
    body = (before + '''(:task t) (:method choose :parameters (?x ?y - obj)
      :task (t) :precondition (edge ?x ?y) :effect (done))''')
    result = encode(tmp_path, body, '(ready a)', tasks='(and (before) (t))',
                    network=':ordered-subtasks', horizon=0 if producer == 'method' else 1,
                    goal='(done)')
    assert solve(result) == z3.sat


@pytest.mark.parametrize('condition', ['(or (edge ?x ?y) (p))',
                                      '(not (edge ?x ?y))',
                                      '(imply (edge ?x ?y) (p))',
                                      '(forall (?x - obj) (or (edge ?x ?y) (p)))'])
def test_nonmandatory_atoms_are_not_joined(tmp_path, condition):
    body = ('(:task t) (:method choose :parameters (?x ?y - obj) :task (t) '
            f':precondition {condition} :effect (done))')
    result = encode(tmp_path, body, '(p)', horizon=0, goal='(done)')
    assert solve(result) == z3.sat


def test_pruned_method_still_reports_bad_source_formula(tmp_path):
    body = ('(:task t) (:method invalid :parameters (?x - obj) :task (t) '
            ':precondition (unknown ?x) :effect (done))')
    result = encode(tmp_path, body, horizon=0)
    assert not result.ok
    assert any('undeclared' in d.message or 'unknown' in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize('left,right', list(product('ab', repeat=2)))
@pytest.mark.parametrize('condition_site', ['method', 'primitive'])
def test_head_binding_and_repeated_join_variables(tmp_path, left, right, condition_site):
    body = ('''(:task t :parameters (?x ?y - obj))
      (:method choose :parameters (?x ?y - obj) :task (t ?x ?y)
        :precondition (and (edge ?x ?x) (edge ?x ?y)) :effect (done))'''
      if condition_site == 'method' else '''(:task t :parameters (?x ?y - obj))
      (:method choose :parameters (?x ?y - obj) :task (t ?x ?y) :subtasks (act ?y ?x))
      (:action act :parameters (?u ?v - obj)
        :precondition (and (edge ?v ?v) (edge ?v ?u)) :effect (done))''')
    initial = '(edge a a) (edge a b)'
    result = encode(tmp_path, body, initial, tasks=f'(t {left} {right})',
                    horizon=int(condition_site == 'primitive'), goal='(done)')
    assert solve(result) == (z3.sat if left == 'a' else z3.unsat)


@pytest.mark.parametrize('effect', ['(edge a b)',
                                  '(forall (?x - obj) (when (ready ?x) (edge ?x b)))'])
def test_primitive_join_never_prunes_relations_added_by_a_method(tmp_path, effect):
    body = (f'''(:task establish) (:method before :task (establish) :effect {effect})
      (:task t) (:method wrapper :parameters (?x ?y - obj) :task (t) :subtasks (act ?y ?x))
      (:action act :parameters (?to ?from - obj) :precondition (edge ?from ?to) :effect (done))''')
    result = encode(tmp_path, body, '(ready a)', tasks='(and (establish) (t))',
                    network=':ordered-subtasks', horizon=1, goal='(done)')
    assert solve(result) == z3.sat


def test_primitive_candidate_still_checks_deletion_before_execution(tmp_path):
    body = '''(:task t) (:method wrapper :parameters (?x ?y - obj) :task (t)
      :subtasks (act ?x ?y))
      (:action act :parameters (?x ?y - obj) :precondition (edge ?x ?y) :effect (done))
      (:action drop :effect (not (edge a b)))'''
    result = encode(tmp_path, body, '(edge a b)', tasks='(and (drop) (t))',
                    network=':ordered-subtasks', horizon=2, goal='(done)')
    assert solve(result) == z3.unsat
