"""Compare bounded scheduling with an independent finite trace oracle."""
from itertools import permutations, product

import pytest
import somtparser as sp
import z3


def encode(tmp_path, body, network, horizon, depth=1):
    domain = ('(define (domain d) (:requirements :hierarchy :typing :method-preconditions) '
              '(:predicates (p)) ' + body + ')')
    problem = tmp_path / 'problem.hddl'
    problem.write_text('(define (problem p) (:domain d) (:htn ' + network + ') (:init (p)))')
    result = sp.translate(source=domain, data=[str(problem)], language='hddl', profile='bmc',
                          options={'plan_horizon': str(horizon), 'decomposition_depth': str(depth)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return result, solver


@pytest.mark.parametrize('edges', [[], [(0, 2), (1, 2)], [(0, 1), (1, 2), (2, 3)]])
def test_every_trace_matches_partial_order(tmp_path, edges):
    actions = 'abcd'
    body = ' '.join(f'(:action {a} :effect (and))' for a in actions)
    tasks = ' '.join(f'(s{i} ({a}))' for i, a in enumerate(actions))
    order = ' '.join(f'(< s{i} s{j})' for i, j in edges)
    _, solver = encode(tmp_path, body, f':subtasks (and {tasks}) :ordering (and {order})', 4)
    valid = {tuple(actions[i] for i in order) for order in permutations(range(4))
             if all(order.index(i) < order.index(j) for i, j in edges)}
    # Includes repeated actions and missing occurrences, not only permutations.
    for trace in product(actions, repeat=4):
        solver.push()
        solver.add(*[z3.Bool(f'do_{a}@{step}') for step, a in enumerate(trace)])
        assert solver.check() == (z3.sat if trace in valid else z3.unsat), trace
        solver.pop()


def test_duplicate_labels_are_distinct_occurrences(tmp_path):
    body = '(:action a :effect (and)) (:action b :effect (and))'
    _, solver = encode(tmp_path, body,
                       ':subtasks (and (x (a)) (y (a)) (z (b))) :ordering (< x z)', 3)
    valid = {('a', 'a', 'b'), ('a', 'b', 'a')}
    for trace in product('ab', repeat=3):
        solver.push()
        solver.add(*[z3.Bool(f'do_{a}@{step}') for step, a in enumerate(trace)])
        assert solver.check() == (z3.sat if trace in valid else z3.unsat), trace
        solver.pop()


def test_alternative_lengths_keep_noop_suffix(tmp_path):
    body = ('(:task t) (:method short :task (t) :subtasks (a)) '
            '(:method long :task (t) :subtasks (and (a) (b))) '
            '(:action a :effect (and)) (:action b :effect (and))')
    _, solver = encode(tmp_path, body, ':subtasks (t)', 2)
    for trace, expected in [(('a', 'b'), z3.sat), (('b', 'a'), z3.sat),
                            (('a', 'a'), z3.unsat), (('b', 'b'), z3.unsat)]:
        solver.push()
        solver.add(*[z3.Bool(f'do_{a}@{step}') for step, a in enumerate(trace)])
        assert solver.check() == expected
        solver.pop()
    solver.add(z3.Bool('do_a@0'), z3.Not(z3.Bool('do_a@1')), z3.Not(z3.Bool('do_b@1')))
    assert solver.check() == z3.sat


def test_large_unordered_method_events_do_not_enumerate_factorial(tmp_path):
    # 11! distinct event schedules; source primitive horizon is still zero.
    body = ' '.join(f'(:task t{i}) (:method m{i} :task (t{i}) :precondition (p))'
                    for i in range(11))
    tasks = ' '.join(f'(t{i})' for i in range(11))
    result, solver = encode(tmp_path, body, f':subtasks (and {tasks})', 0)
    assert len(result.to_smt2()) < 1000000
    assert solver.check() == z3.sat
    positions = [d for d in solver.model().decls() if '__hddl_position' in d.name()]
    assert len(positions) == 11
    assert sorted(solver.model()[d].as_long() for d in positions) == list(range(11))


def test_impossible_initial_network_is_pruned_before_cartesian_grounding(tmp_path):
    body = '(:constants a b c) (:action act :parameters (?x) :effect (and))'
    params = ' '.join(f'?x{i}' for i in range(12))
    tasks = ' '.join(f'(act ?x{i})' for i in range(12))
    _, solver = encode(tmp_path, body, f':parameters ({params}) :subtasks (and {tasks})', 1)
    assert solver.check() == z3.unsat


def test_pruned_network_still_checks_source_action_schema(tmp_path):
    body = '(:action act :effect (missing))'
    with pytest.raises(AssertionError, match='undeclared|unknown'):
        encode(tmp_path, body, ':subtasks (and (act) (act))', 1)


def test_shared_schedule_preserves_all_alternative_traces(tmp_path):
    body = ('(:task t) (:method empty :task (t)) '
            '(:method ordered :task (t) :ordered-subtasks (and (a) (b))) '
            '(:method repeated :task (t) :subtasks (and (a) (a))) '
            '(:method longer :task (t) :subtasks (and (x (c)) (y (b)) (z (a))) '
            ':ordering (< x z)) '
            + ' '.join(f'(:action {a} :effect (and))' for a in 'abc'))
    _, solver = encode(tmp_path, body, ':subtasks (t)', 3)
    valid = {('noop',) * 3, ('a', 'b', 'noop'), ('a', 'a', 'noop')}
    valid |= {trace for trace in permutations('abc') if trace.index('c') < trace.index('a')}
    for trace in product(['a', 'b', 'c', 'noop'], repeat=3):
        solver.push()
        solver.add(*[z3.Bool(f'__pddl_noop@{i}' if a == 'noop' else f'do_{a}@{i}')
                     for i, a in enumerate(trace)])
        assert solver.check() == (z3.sat if trace in valid else z3.unsat), trace
        solver.pop()


def test_many_frontiers_share_only_one_schedule_witness(tmp_path):
    # 4,096 unordered frontiers, each with 12 method events. Alternative
    # witnesses are existential: they need at most 12 positions in total.
    body = ' '.join(f'(:task t{i}) (:method a{i} :task (t{i}) :precondition (p)) '
                    f'(:method b{i} :task (t{i}) :precondition (p))' for i in range(12))
    tasks = ' '.join(f'(t{i})' for i in range(12))
    result, solver = encode(tmp_path, body, f':subtasks (and {tasks})', 0)
    assert solver.check() == z3.sat
    positions = [d for d in solver.model().decls() if '__hddl_position' in d.name()]
    assert len(positions) == 12
    assert sorted(solver.model()[d].as_long() for d in positions) == list(range(12))
