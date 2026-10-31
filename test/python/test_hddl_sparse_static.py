"""Closed static relations stay sparse without weakening source validation."""
import pytest
import somtparser as sp
import z3


def encode(tmp_path, domain, initial, tasks, goal='(and)', horizon=1):
    path = tmp_path / 'problem.hddl'
    path.write_text('(define (problem p) (:domain d) (:htn :ordered-subtasks '
                    + tasks + ') (:init ' + initial + ') (:goal ' + goal + '))')
    result = sp.translate(source=domain, data=[str(path)], language='hddl', profile='bmc',
                          options={'plan_horizon': str(horizon), 'decomposition_depth': '1'})
    return result


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
def test_large_static_relation_does_not_ground_implicit_false_tuples(tmp_path, initial, expected):
    # 512**4 possible tuples; only source literals and evaluated calls need keys.
    constants = ' '.join(f'c{i}' for i in range(512))
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              f'(:types cell) (:constants {constants} - cell) '
              '(:predicates (edge ?a ?b ?c ?d - cell) (done)) '
              '(:action act :precondition (edge c0 c1 c2 c3) :effect (done)) '
              '(:action unreachable :parameters (?a ?b ?c ?d - cell) '
              ':effect (edge ?a ?b ?c ?d)))')
    result = encode(tmp_path, domain, initial, '(act)', '(done)')
    assert solve(result) == expected
    assert result.report.stats.num_vars < 20


@pytest.mark.parametrize('tasks,horizon,expected', [
    ('(and (mark) (read))', 2, z3.sat),
    ('(and (read) (mark))', 2, z3.unsat),
    ('(read)', 1, z3.unsat),
])
def test_reachable_effect_keeps_relation_dynamic(tmp_path, tasks, horizon, expected):
    domain = ('(define (domain d) (:requirements :hierarchy) (:constants c) '
              '(:predicates (edge ?x) (done)) '
              '(:action mark :effect (edge c)) '
              '(:action read :precondition (edge c) :effect (done)))')
    result = encode(tmp_path, domain, '', tasks, '(done)', horizon)
    assert solve(result) == expected


@pytest.mark.parametrize('initial', [
    '(edge c) (not (edge c))',
    '(edge missing)',
    '(edge c c)',
])
def test_sparse_initial_relation_still_validates_every_literal(tmp_path, initial):
    domain = ('(define (domain d) (:requirements :hierarchy) (:constants c) '
              '(:predicates (edge ?x)) (:action act :effect (and)))')
    result = encode(tmp_path, domain, initial, '(act)')
    assert not result.ok
    assert any('initial state both' in d.message or 'unknown PDDL object' in d.message
               or 'expects' in d.message for d in result.diagnostic_items)


def test_sparse_tuple_keys_do_not_alias_concatenated_names(tmp_path):
    domain = ('(define (domain d) (:requirements :hierarchy) (:constants a b_c a_b c) '
              '(:predicates (edge ?x ?y) (done)) '
              '(:action act :precondition (edge a_b c) :effect (done)))')
    assert solve(encode(tmp_path, domain, '(edge a b_c)', '(act)', '(done)')) == z3.unsat
    assert solve(encode(tmp_path, domain, '(edge a_b c)', '(act)', '(done)')) == z3.sat


def test_sparse_static_relation_in_finite_quantifier(tmp_path):
    domain = ('(define (domain d) (:requirements :hierarchy :adl) (:constants a b) '
              '(:predicates (edge ?x)) '
              '(:action act :precondition (forall (?x) (edge ?x)) :effect (and)))')
    assert solve(encode(tmp_path, domain, '(edge a)', '(act)')) == z3.unsat
    assert solve(encode(tmp_path, domain, '(edge a) (edge b)', '(act)')) == z3.sat
