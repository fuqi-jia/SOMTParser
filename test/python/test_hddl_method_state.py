"""Method state events: source progression, ordering and primitive-step bounds."""
from pathlib import Path

import pytest
import z3
import somtparser as sp


def translate(tmp_path, body, initial='', tasks='(t)', goal='(and)', horizon=1, depth=1,
              method_requirement=':htn-method-pre-eff'):
    domain = ('(define (domain d) (:requirements :adl :hierarchy ' + method_requirement + ') '
              '(:predicates (p) (q) (r)) ' + body + ')')
    problem = tmp_path / 'problem.hddl'
    problem.write_text('(define (problem prob) (:domain d) (:htn :subtasks '
                       + tasks + ') (:init ' + initial + ') (:goal ' + goal + '))')
    result = sp.translate(source=domain, data=[str(problem)], language='hddl', profile='bmc',
                          options={'plan_horizon': str(horizon), 'decomposition_depth': str(depth)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert [(b.kind, b.value) for b in result.report.fidelity.bounds
            if b.kind == sp.Bound.PLAN_HORIZON] == [(sp.Bound.PLAN_HORIZON, horizon)]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return result, solver


@pytest.mark.parametrize('initial,expected', [('', z3.unsat), ('(p)', z3.sat)])
@pytest.mark.parametrize('requirement', [':htn-method-pre-eff', ':method-preconditions'])
def test_precondition_on_empty_frontier_is_still_checked(tmp_path, initial, expected, requirement):
    _, solver = translate(tmp_path, '(:task t) (:method m :task (t) :precondition (p))',
                          initial=initial, horizon=0, method_requirement=requirement)
    assert solver.check() == expected


def test_method_effect_precedes_every_subtask_without_using_source_horizon(tmp_path):
    body = ('(:task t) (:method m :task (t) :effect (p) '
            ':subtasks (and (a) (b))) '
            '(:action a :precondition (p) :effect (q)) '
            '(:action b :precondition (p) :effect (r))')
    _, solver = translate(tmp_path, body, goal='(and (q) (r))', horizon=2)
    assert solver.check() == z3.sat
    # A late prefix would let both actions use an unestablished precondition.
    assert z3.is_true(solver.model().eval(z3.Bool('do_somt-hddl-method-0@0')))
    _, too_short = translate(tmp_path, body, goal='(and (q) (r))', horizon=1)
    assert too_short.check() == z3.unsat


def test_method_condition_is_evaluated_at_its_event_not_only_in_initial_state(tmp_path):
    body = ('(:task t) (:method m :task (t) :precondition (p) :effect (q)) '
            '(:action establish :effect (p))')
    _, solver = translate(tmp_path, body, tasks='(and (establish) (t))',
                          goal='(q)', horizon=1)
    assert solver.check() == z3.sat
    model = solver.model()
    assert z3.is_true(model.eval(z3.Bool('do_establish@0')))
    assert z3.is_true(model.eval(z3.Bool('do_somt-hddl-method-0@1')))


def test_effect_only_method_cannot_be_replaced_by_noop(tmp_path):
    body = '(:task t) (:method m :task (t) :effect (and (not (p)) (q)))'
    _, solver = translate(tmp_path, body, initial='(p)', goal='(and (not (p)) (q))', horizon=0)
    assert solver.check() == z3.sat
    _, wrong = translate(tmp_path, body, initial='(p)', goal='(p)', horizon=0)
    assert wrong.check() == z3.unsat


def test_prefix_precedence_survives_nested_decomposition(tmp_path):
    body = ('(:task t) (:task u) (:method outer :task (t) :effect (p) :subtasks (u)) '
            '(:method inner :task (u) :precondition (p) :effect (q))')
    _, solver = translate(tmp_path, body, goal='(q)', horizon=0, depth=2)
    assert solver.check() == z3.sat
    _, shallow = translate(tmp_path, body, goal='(q)', horizon=0, depth=1)
    assert shallow.check() == z3.unsat


def test_generated_prefix_name_does_not_capture_source_action(tmp_path):
    body = ('(:task t) (:method m :task (t) :effect (p) :subtasks (somt-hddl-method-0)) '
            '(:action somt-hddl-method-0 :precondition (p) :effect (q))')
    _, solver = translate(tmp_path, body, goal='(q)', horizon=1)
    assert solver.check() == z3.sat
    _, too_short = translate(tmp_path, body, goal='(q)', horizon=0)
    assert too_short.check() == z3.unsat


def test_upstream_method_effect_conditional_guards_use_old_state():
    root = Path(__file__).resolve().parents[2] / 'languages/hddl/instances/upstream'
    result = sp.translate(str(root / 'method-effect.hddl'),
                          data=[str(root / 'method-effect-problem.hddl')],
                          language='hddl', profile='bmc',
                          options={'plan_horizon': '0', 'decomposition_depth': '2',
                                   'lenient_requirements': '1'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
    # Independent simultaneous source progression through its three method
    # events: {p} -> {q} -> {r} -> {r}. No source primitive action exists.
    state = {'p'}
    expected = [set(state)]
    for _ in range(3):
        old = set(state)
        adds = ({'q'} if 'p' in old else set()) | ({'r'} if 'p' not in old and 'q' in old else set())
        deletes = {'p'} if 'p' in old else {'q'}
        state = (old - deletes) | adds
        expected.append(set(state))
    model = solver.model()
    for step, state in enumerate(expected):
        for atom in ('p', 'q', 'r'):
            assert z3.is_true(model.eval(z3.Bool(f'{atom}_c@{step}'))) == (atom in state)


@pytest.mark.parametrize('field', [':precondition', ':effect'])
def test_atomic_method_field_is_not_silently_treated_as_empty(tmp_path, field):
    problem = tmp_path / 'problem.hddl'
    problem.write_text('(define (problem p) (:domain d) (:htn :subtasks (t)) (:init))')
    result = sp.translate(source='(define (domain d) (:requirements :htn-method-pre-eff) '
                          '(:predicates (p)) (:task t) (:method m :task (t) '
                          + field + ' p))', data=[str(problem)], language='hddl', profile='bmc',
                          options={'plan_horizon': '0', 'decomposition_depth': '1'})
    assert not result.ok


def test_unreachable_high_arity_method_does_not_cartesian_ground(tmp_path):
    constants = ' '.join(f'c{i}' for i in range(32))
    body = (f'(:constants {constants}) (:task t) '
            '(:method reached :task (t) :subtasks (a)) '
            '(:task unused :parameters (?a ?b ?c ?d ?e ?f)) '
            '(:method unreachable :parameters (?a ?b ?c ?d ?e ?f) '
            ':task (unused ?a ?b ?c ?d ?e ?f) :subtasks (a)) '
            '(:action a :effect (p))')
    _, solver = translate(tmp_path, body, goal='(p)', horizon=1)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('horizon,depth,expected', [(1, 1, z3.unsat), (1, 2, z3.sat)])
def test_depth_impossible_branch_pruned_before_local_cartesian_grounding(
        tmp_path, horizon, depth, expected):
    constants = ' '.join(f'c{i}' for i in range(32))
    # The first method has 32**6 local bindings, but its two primitives can
    # never fit horizon 1. The second requires one more decomposition level.
    body = (f'(:constants {constants}) (:task t) (:task u) '
            '(:method huge :parameters (?a ?b ?c ?d ?e ?f) '
            ':task (t) :subtasks (and (a) (a))) '
            '(:method nested :task (t) :subtasks (u)) '
            '(:method finish :task (u) :subtasks (a)) '
            '(:action a :effect (p))')
    _, solver = translate(tmp_path, body, goal='(p)', horizon=horizon, depth=depth)
    assert solver.check() == expected


def test_depth_sensitive_grounding_cache_keeps_deeper_alternative(tmp_path):
    body = ('(:task t) (:task u) (:task v) '
            '(:method top :task (t) :ordered-subtasks (and (u) (v))) '
            '(:method middle :task (u) :subtasks (v)) '
            '(:method empty-v :task (v)) '
            '(:method deeper-v :task (v) :subtasks (w)) '
            '(:task w) (:method finish :task (w) :subtasks (a)) '
            '(:action a :effect (p))')
    # v is first visited at depth 1 through u, then at depth 2 directly.
    # Reusing its shallow filtered cache would lose the only goal-achiever.
    _, solver = translate(tmp_path, body, goal='(p)', horizon=1, depth=3)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('tasks,expected', [('(choose c c)', z3.sat),
                                          ('(choose c d)', z3.unsat)])
def test_method_head_repeated_parameter_unifies_consistently(tmp_path, tasks, expected):
    body = ('(:constants c d) (:task choose :parameters (?x ?y)) '
            '(:method equal :parameters (?v) :task (choose ?v ?v) :subtasks (a)) '
            '(:action a :effect (p))')
    _, solver = translate(tmp_path, body, tasks=tasks, goal='(p)', horizon=1)
    assert solver.check() == expected


@pytest.mark.parametrize('tasks,expected', [('(choose c)', z3.sat),
                                          ('(choose d)', z3.unsat)])
def test_reached_task_respects_method_head_constant(tmp_path, tasks, expected):
    body = ('(:constants c d) (:task choose :parameters (?x)) '
            '(:method only-c :task (choose c) :subtasks (a)) '
            '(:action a :effect (p))')
    _, solver = translate(tmp_path, body, tasks=tasks, goal='(p)', horizon=1)
    assert solver.check() == expected


@pytest.mark.parametrize('left,right', [('c', 'c'), ('c', 'd'), ('d', 'c'), ('d', 'd')])
@pytest.mark.parametrize('equal', [False, True])
def test_method_binding_constraints_restrict_substitutions(tmp_path, left, right, equal):
    constraint = '(= ?x ?y)' if equal else '(not (= ?x ?y))'
    body = ('(:constants c d) (:task choose :parameters (?x ?y)) '
            '(:method m :parameters (?x ?y) :task (choose ?x ?y) '
            ':constraints (and ' + constraint + ') :subtasks (a)) '
            '(:action a :effect (p))')
    _, solver = translate(tmp_path, body, tasks=f'(choose {left} {right})', goal='(p)')
    assert solver.check() == (z3.sat if (left == right) == equal else z3.unsat)


@pytest.mark.parametrize('constraint,expected', [
    ('(and (= ?y d) (not (= ?x ?y)))', z3.sat),
    ('(and (= ?y d) (= ?x ?y))', z3.unsat),
])
def test_method_local_binding_filter_precedes_state_event(tmp_path, constraint, expected):
    body = ('(:constants c d) (:task choose :parameters (?x)) '
            '(:method m :parameters (?x ?y) :task (choose ?x) '
            ':constraints ' + constraint + ' :effect (p) :subtasks (and))')
    _, solver = translate(tmp_path, body, tasks='(choose c)', goal='(p)', horizon=0)
    assert solver.check() == expected


@pytest.mark.parametrize('constraint,expected', [('(= ?x c)', z3.sat),
                                                ('(and (= ?x c) (= ?x d))', z3.unsat)])
def test_initial_network_binding_restrictions(tmp_path, constraint, expected):
    problem = tmp_path / 'problem.hddl'
    problem.write_text('(define (problem p) (:domain d) (:htn :parameters (?x) '
                       ':subtasks (a ?x) :constraints ' + constraint + ') (:init))')
    result = sp.translate(source='(define (domain d) (:requirements :hierarchy) '
                          '(:constants c d) (:predicates (p)) '
                          '(:action a :parameters (?v) :effect (p)))',
                          data=[str(problem)], language='hddl', profile='bmc',
                          options={'plan_horizon': '1', 'decomposition_depth': '1'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == expected


@pytest.mark.parametrize('constraint', ['(= ?missing c)', '(= c missing)',
                                       '(= c)', '(not (= c d) (= d c))', '(p)'])
def test_invalid_binding_is_rejected_even_in_unreachable_method(tmp_path, constraint):
    problem = tmp_path / 'problem.hddl'
    problem.write_text('(define (problem p) (:domain d) (:htn :subtasks (and)) (:init))')
    result = sp.translate(source='(define (domain d) (:requirements :hierarchy) '
                          '(:constants c d) (:predicates (p)) (:task t) '
                          '(:method unused :task (t) :constraints ' + constraint + '))',
                          data=[str(problem)], language='hddl', profile='bmc',
                          options={'plan_horizon': '0', 'decomposition_depth': '1'})
    assert not result.ok
