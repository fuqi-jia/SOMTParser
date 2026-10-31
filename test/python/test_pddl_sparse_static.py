"""Closed-world static PDDL relations without enumerating implicit false tuples."""
import pytest
import somtparser as sp
import z3


def encode(tmp_path, domain, initial, goal='(done)', horizon=1):
    path = tmp_path / 'problem.pddl'
    path.write_text(f'(define (problem p) (:domain d) (:init {initial}) (:goal {goal}))')
    return sp.translate(source=domain, data=[str(path)], language='pddl', profile='bmc',
                        options={'plan_horizon': str(horizon)})


def solve(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


@pytest.mark.parametrize('initial,expected', [
    ('(edge c0 c1 c2 c3)', z3.sat),
    ('(edge c0 c1 c2 c4)', z3.unsat),
    ('', z3.unsat),
])
def test_large_static_relation(tmp_path, initial, expected):
    constants = ' '.join(f'c{i}' for i in range(512))
    domain = (f'(define (domain d) (:requirements :strips) (:constants {constants}) '
              '(:predicates (edge ?a ?b ?c ?d) (done)) '
              '(:action act :precondition (edge c0 c1 c2 c3) :effect (done)))')
    assert solve(encode(tmp_path, domain, initial)) == expected


@pytest.mark.parametrize('horizon,expected', [(0, z3.unsat), (1, z3.unsat), (2, z3.sat)])
def test_predicate_modified_by_an_action_is_not_static(tmp_path, horizon, expected):
    domain = '''(define (domain d) (:requirements :strips) (:constants c)
      (:predicates (edge ?x) (done)) (:action mark :effect (edge c))
      (:action read :precondition (edge c) :effect (done)))'''
    assert solve(encode(tmp_path, domain, '', horizon=horizon)) == expected


@pytest.mark.parametrize('initial', [
    '(edge a b) (not (edge a b))', '(edge a missing)', '(edge a)', '(undeclared a b)',
])
def test_every_initial_literal_still_checked(tmp_path, initial):
    domain = '''(define (domain d) (:requirements :adl) (:constants a b)
      (:predicates (edge ?x ?y)) (:action act :effect (and)))'''
    result = encode(tmp_path, domain, initial, goal='(and)')
    assert not result.ok


def test_zero_horizon_static_goal_and_injective_keys(tmp_path):
    domain = '''(define (domain d) (:requirements :adl) (:constants a b_c a_b c)
      (:predicates (edge ?x ?y)) (:action act :effect (and)))'''
    goal = '(and (edge a b_c) (not (edge a_b c)))'
    assert solve(encode(tmp_path, domain, '(edge a b_c)', goal, 0)) == z3.sat
    assert solve(encode(tmp_path, domain, '(edge a_b c)', goal, 0)) == z3.unsat


def test_typed_quantifier_in_static_goal(tmp_path):
    domain = '''(define (domain d) (:requirements :adl) (:types item other)
      (:constants a b - item c - other) (:predicates (p ?x - item))
      (:action act :effect (and)))'''
    goal = '(forall (?x - item) (p ?x))'
    assert solve(encode(tmp_path, domain, '(p a) (p b)', goal, 0)) == z3.sat
    assert solve(encode(tmp_path, domain, '(p a)', goal, 0)) == z3.unsat


def test_only_mutated_tuples_of_a_large_dynamic_relation_need_state(tmp_path):
    constants = ' '.join(f'c{i}' for i in range(512))
    domain = (f'(define (domain d) (:requirements :adl) (:constants {constants}) '
              '(:predicates (edge ?a ?b ?c ?d)) '
              '(:action mark :effect (edge c0 c1 c2 c3)))')
    goal = '(and (edge c0 c1 c2 c3) (not (edge c0 c1 c2 c4)) (edge c5 c6 c7 c8))'
    result = encode(tmp_path, domain, '(edge c5 c6 c7 c8)', goal)
    assert solve(result) == z3.sat
    assert result.parser.is_declared_variable('edge_c0_c1_c2_c3@1')
    assert not result.parser.is_declared_variable('edge_c5_c6_c7_c8@1')


@pytest.mark.parametrize('initial,expected', [('', z3.sat), ('(p a)', z3.unsat)])
def test_guarded_quantified_deletes_are_mutable(tmp_path, initial, expected):
    domain = '''(define (domain d) (:requirements :adl) (:types item)
      (:constants a b - item) (:predicates (p ?x - item) (ready ?x - item))
      (:action clear :effect (forall (?x - item) (when (ready ?x) (not (p ?x))))))'''
    goal = '(forall (?x - item) (not (p ?x)))'
    assert solve(encode(tmp_path, domain, '(p b) (ready b) ' + initial, goal)) == expected
