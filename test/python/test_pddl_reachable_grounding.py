"""Bounded action grounding compared with independent source trace execution."""
from itertools import product

import pytest
import somtparser as sp
import z3


def encode(tmp_path, domain, initial='', horizon=1, goal='(and)'):
    path = tmp_path / 'problem.pddl'
    path.write_text(f'(define (problem p) (:domain d) (:init {initial}) (:goal {goal}))')
    result = sp.translate(source=domain, data=[str(path)], language='pddl', profile='bmc',
                          options={'plan_horizon': str(horizon)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return result, solver


@pytest.mark.parametrize('horizon', [1, 2, 3])
@pytest.mark.parametrize('blocked', list(product([False, True], repeat=2)))
def test_all_parametric_traces_and_states(tmp_path, horizon, blocked):
    domain = '''(define (domain d) (:requirements :adl)
      (:types node) (:constants a b - node)
      (:predicates (edge ?x ?y - node) (at ?x - node)
                   (blocked ?x - node) (visited ?x - node))
      (:action step :parameters (?x ?y - node)
        :precondition (and (at ?x) (edge ?x ?y) (not (blocked ?y)))
        :effect (and (not (at ?x)) (at ?y) (visited ?y)))
      (:action open :parameters (?y - node) :effect (not (blocked ?y))))'''
    initial = {'at_a'} | {f'blocked_{x}' for x, b in zip('ab', blocked) if b}
    facts = '(at a) (edge a b) (edge b a) ' + ' '.join(
        f'(blocked {x})' for x, b in zip('ab', blocked) if b)
    result, solver = encode(tmp_path, domain, facts, horizon)
    actions = ['step_a_b', 'step_b_a', 'open_a', 'open_b', 'noop']
    fluents = [f'{p}_{x}' for p in ['at', 'blocked', 'visited'] for x in 'ab']
    for trace in product(actions, repeat=horizon):
        states = [initial]
        padded = False
        for action in trace:
            old = states[-1]
            if padded and action != 'noop':
                break
            new = set(old)
            if action.startswith('step'):
                _, source, target = action.split('_')
                if f'at_{source}' not in old or f'blocked_{target}' in old:
                    break
                new.remove(f'at_{source}')
                new.update([f'at_{target}', f'visited_{target}'])
            elif action.startswith('open'):
                new.discard('blocked_' + action[-1])
            else:
                padded = True
            states.append(new)
        valid = len(states) == horizon + 1
        solver.push()
        for step, action in enumerate(trace):
            name = f'__pddl_noop@{step}' if action == 'noop' else f'do_{action}@{step}'
            exists = result.parser.is_declared_variable(name)
            if valid:
                assert exists, (trace, step)
            solver.add(z3.Bool(name) if exists else z3.BoolVal(False))
        assert solver.check() == (z3.sat if valid else z3.unsat), (blocked, trace)
        if valid:
            # Omitted fluent tuples reconstruct to their initial value. If
            # any actually changing tuple is omitted, this oracle still fails.
            values = [(z3.Bool(f'{f}@{i}') if result.parser.is_declared_variable(f'{f}@{i}')
                       else z3.BoolVal(f in initial)) != (f in state)
                      for i, state in enumerate(states) for f in fluents]
            solver.add(z3.Or(*values))
            assert solver.check() == z3.unsat, (blocked, trace)
        solver.pop()


def test_sparse_joins_avoid_a_trillion_parameter_tuples(tmp_path):
    constants = ' '.join(f'c{i}' for i in range(32))
    parameters = ' '.join(f'?x{i}' for i in range(8))
    links = ' '.join(f'(edge ?x{i} ?x{i+1})' for i in range(7))
    domain = (f'(define (domain d) (:requirements :strips) (:constants {constants}) '
              '(:predicates (edge ?a ?b) (at ?a)) '
              f'(:action move :parameters ({parameters}) '
              f':precondition (and (at ?x0) {links}) '
              ':effect (and (not (at ?x0)) (at ?x7))))')
    facts = '(at c0) ' + ' '.join(f'(edge c{i} c{(i+1)%32})' for i in range(32))
    result, solver = encode(tmp_path, domain, facts, horizon=3, goal='(at c21)')
    assert solver.check() == z3.sat
    # The result must contain the action enabled only after the second move.
    assert result.parser.is_declared_variable('do_move_c14_c15_c16_c17_c18_c19_c20_c21@2')
    _, shorter = encode(tmp_path, domain, facts, horizon=2, goal='(at c21)')
    assert shorter.check() == z3.unsat


def test_binding_sensitive_joins_connect_independent_parameter_groups(tmp_path):
    # A capacity relation is smaller than the edge relation, but joining all
    # unary domains first creates a huge intermediate Cartesian product. Once
    # a cell is bound, its indexed edge relation has just one candidate.
    constants = (' '.join(f'n{i}' for i in range(128)) + ' - node '
                 + ' '.join(f'c{i}' for i in range(128)) + ' - cell '
                 + ' '.join(f'l{i}' for i in range(32)) + ' - level')
    domain = (f'''(define (domain d) (:requirements :typing)
      (:types node cell level) (:constants {constants})
      (:predicates (degree0 ?n - node) (capacity ?c - cell ?v - level)
        (inc ?x ?y - level) (edge ?c1 ?c2 - cell ?n1 ?n2 - node) (done))
      (:action link :parameters (?n1 ?n2 - node ?c1 - cell ?f1 ?t1 - level
                                ?c2 - cell ?f2 ?t2 - level)
        :precondition (and (degree0 ?n1) (degree0 ?n2)
          (edge ?c1 ?c2 ?n1 ?n2) (capacity ?c1 ?f1) (capacity ?c2 ?f2)
          (inc ?t1 ?f1) (inc ?t2 ?f2)) :effect (done)))''')
    facts = ' '.join(f'(degree0 n{i}) (capacity c{i} l{i%32}) '
                     f'(edge c{i} c{(i+1)%128} n{i} n{(i+1)%128})'
                     for i in range(128))
    facts += ' ' + ' '.join(f'(inc l{i} l{i+1})' for i in range(31))
    result, solver = encode(tmp_path, domain, facts, goal='(done)')
    name = 'do_link_n1_n2_c1_l1_l0_c2_l2_l1@0'
    assert result.parser.is_declared_variable(name)
    solver.add(z3.Bool(name))
    assert solver.check() == z3.sat
    assert not result.parser.is_declared_variable('do_link_n127_n0_c127_l31_l30_c0_l0_l31@0')


@pytest.mark.parametrize('condition,expected', [
    ('(or (p b) (= ?x a))', z3.sat),
    ('(imply (= ?x a) (p b))', z3.unsat),
    ('(not (and (= ?x a) (p b)))', z3.sat),
    ('(exists (?x) (p ?x))', z3.sat),
    ('(forall (?x) (p ?x))', z3.unsat),
])
def test_nonconjunctive_conditions_and_shadowing(tmp_path, condition, expected):
    domain = ('(define (domain d) (:requirements :adl) (:constants a b) '
              '(:predicates (edge ?x ?y) (p ?x) (done)) '
              f'(:action act :parameters (?x) :precondition (and (edge ?x ?x) {condition}) '
              ':effect (done)))')
    _, solver = encode(tmp_path, domain, '(edge a a) (edge a b) (p a)', goal='(done)')
    assert solver.check() == expected


def test_quantified_conditional_adds_can_enable_later_actions(tmp_path):
    domain = '''(define (domain d) (:requirements :adl) (:constants a b)
      (:predicates (ready ?x) (p ?x) (done))
      (:action first :parameters (?x) :precondition (ready ?x)
        :effect (forall (?x) (when (ready ?x) (p ?x))))
      (:action second :parameters (?x) :precondition (p ?x) :effect (done)))'''
    result, solver = encode(tmp_path, domain, '(ready a)', horizon=2, goal='(done)')
    assert result.parser.is_declared_variable('do_second_a@1')
    assert result.parser.is_declared_variable('do_second_b@1')
    assert not result.parser.is_declared_variable('do_second_a@0')
    assert not result.parser.is_declared_variable('do_second_b@0')
    assert solver.check() == z3.sat
    solver.add(z3.Bool('do_second_b@1'))
    assert solver.check() == z3.unsat  # relaxed grounding must not erase the guard


def test_action_first_enabled_after_delete_remains_in_later_steps(tmp_path):
    domain = '''(define (domain d) (:requirements :adl)
      (:predicates (p) (q) (r))
      (:action enable :effect (q))
      (:action remove :precondition (q) :effect (not (p)))
      (:action finish :precondition (and (q) (not (p))) :effect (r)))'''
    result, solver = encode(tmp_path, domain, '(p)', horizon=3, goal='(r)')
    assert not result.parser.is_declared_variable('do_remove@0')
    assert not result.parser.is_declared_variable('do_finish@0')
    # Ignoring deletes is only a may-analysis. Presence of mutable p must not
    # discard its negative precondition or incorrectly postpone its candidate.
    assert result.parser.is_declared_variable('do_finish@1')
    solver.add(z3.Bool('do_enable@0'), z3.Bool('do_remove@1'), z3.Bool('do_finish@2'))
    assert solver.check() == z3.sat


def test_pruning_never_hides_an_invalid_unreachable_schema(tmp_path):
    path = tmp_path / 'problem.pddl'
    path.write_text('(define (problem p) (:domain d) (:init) (:goal (and)))')
    domain = '''(define (domain d) (:requirements :strips) (:constants a)
      (:predicates (p ?x))
      (:action act :parameters (?x) :precondition (p ?x) :effect (undeclared ?x)))'''
    result = sp.translate(source=domain, data=[str(path)], language='pddl', profile='bmc',
                          options={'plan_horizon': '1'})
    assert not result.ok
    assert any('undeclared' in d.message for d in result.diagnostic_items)
