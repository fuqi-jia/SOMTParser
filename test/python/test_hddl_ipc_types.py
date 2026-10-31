"""Semantic checks for type lowering and the explicitly selected IPC dialect."""
import pytest
import z3
import somtparser as sp


def translate(tmp_path, domain, problem, options=None):
    path = tmp_path / 'problem.hddl'
    path.write_text(problem)
    return sp.translate(source=domain, data=[str(path)], language='hddl', profile='bmc',
                        options={'plan_horizon': '1', 'decomposition_depth': '1',
                                 **(options or {})})


def check(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


@pytest.mark.parametrize('types', ['base peer - object child - base',
                                  'child - base base peer - object'])
@pytest.mark.parametrize('initial,expected', [('', z3.unsat), ('(ready c)', z3.sat)])
def test_root_type_group_boundary_preserved(tmp_path, types, initial, expected):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              f'(:types {types}) (:predicates (ready ?x - base) (done)) '
              '(:action act :parameters (?x - base) :precondition (ready ?x) '
              ':effect (done)))')
    problem = ('(define (problem p) (:domain d) (:objects c - base) '
               f'(:htn :subtasks (act c)) (:init {initial}) (:goal (done)))')
    assert check(translate(tmp_path, domain, problem)) == expected


@pytest.mark.parametrize('initial,expected', [('', z3.unsat), ('(ready c s)', z3.sat)])
def test_compiled_method_keeps_object_parameter_before_subtype(tmp_path, initial, expected):
    domain = ('(define (domain d) (:requirements :hierarchy :typing :method-preconditions) '
              '(:types special) (:predicates (ready ?x - object ?y - special)) '
              '(:task t :parameters (?x - object ?y - special)) '
              '(:method m :parameters (?x - object ?y - special) :task (t ?x ?y) '
              ':precondition (ready ?x ?y)))')
    problem = ('(define (problem p) (:domain d) (:objects c - object s - special) '
               f'(:htn :subtasks (t c s)) (:init {initial}))')
    assert check(translate(tmp_path, domain, problem)) == expected


def test_compact_typing_and_adjacent_comment_preserve_names(tmp_path):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:types heading-condition) (:predicates (done)) '
              '(:action check-landing :parameters (?heading -Heading-Condition;comment\n) '
              ':effect (done)))')
    problem = ('(define (problem p) (:domain d) (:objects c -heading-condition) '
               '(:htn :subtasks (check-landing c)) (:init) (:goal (done)))')
    assert check(translate(tmp_path, domain, problem)) == z3.sat


@pytest.mark.parametrize('initial,expected', [('', z3.unsat), ('(ready c)', z3.sat)])
def test_ipc_parent_only_sort_and_explicit_file_pairing(tmp_path, initial, expected):
    domain = ('(define (domain supplied) (:requirements :hierarchy :typing) '
              '(:types child - parent) (:predicates (ready ?x - parent)) '
              '(:task t :parameters (?x - parent)) '
              '(:method m :parameters (?x - parent) :task (t ?x) :precondition (ready ?x)))')
    problem = ('(define (problem p) (:domain legacy-name) (:objects c - child) '
               f'(:htn :subtasks (t c)) (:init {initial}))')
    assert not translate(tmp_path, domain, problem).ok
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})
    assert check(result) == expected
    messages = '\n'.join(d.message for d in result.diagnostic_items)
    assert "parent-only type 'parent'" in messages
    assert "'legacy-name' paired" in messages
    assert 'ipc-hddl-compatibility' in result.report.to_json()


@pytest.mark.parametrize('types', ['a - b b - a', 'a - absent b - a'])
def test_cycles_and_missing_ancestors_have_type_diagnostics(tmp_path, types):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              f'(:types {types}) (:predicates (p)))')
    problem = '(define (problem p) (:domain d) (:htn :subtasks (and)) (:init))'
    result = translate(tmp_path, domain, problem)
    assert not result.ok
    assert any('type' in d.message for d in result.diagnostic_items)
    assert not any('hddl frontend:' in d.message for d in result.diagnostic_items)
    if types == 'a - b b - a':
        assert not translate(tmp_path, domain, problem, {'ipc_compatibility': '1'}).ok


def test_ipc_does_not_invent_unmentioned_parameter_type(tmp_path):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:predicates (p)) (:task t :parameters (?x - missing)))')
    problem = '(define (problem p) (:domain d) (:htn :subtasks (and)) (:init))'
    assert not translate(tmp_path, domain, problem, {'ipc_compatibility': '1'}).ok


@pytest.mark.parametrize('object_type,expected_ok', [('colour', True), ('other', False)])
def test_repeated_domain_constant_retains_identity_and_type(tmp_path, object_type, expected_ok):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:types colour other) (:constants red - colour) (:predicates (done)) '
              '(:action paint :parameters (?c - colour) :effect (done)))')
    problem = ('(define (problem p) (:domain d) '
               f'(:objects red - {object_type}) '
               '(:htn :subtasks (paint red)) (:init) (:goal (done)))')
    assert not translate(tmp_path, domain, problem).ok
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})
    assert result.ok == expected_ok
    if expected_ok:
        assert check(result) == z3.sat
        assert 'repeated object' in result.report.to_json()


@pytest.mark.parametrize('value', ['false', '0', 'typo'])
def test_compatibility_needs_explicit_true_value(tmp_path, value):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:types child - parent) (:predicates (p)))')
    problem = '(define (problem p) (:domain d) (:htn :subtasks (and)) (:init))'
    assert not translate(tmp_path, domain, problem, {'ipc_compatibility': value}).ok


@pytest.mark.parametrize('parents', ['child - left child - right',
                                    'child - right child - left',
                                    'child - left child - right child - left'])
@pytest.mark.parametrize('initial,expected', [('', z3.unsat), ('(ready c c)', z3.sat)])
def test_multiple_inheritance_preserves_both_parent_domains(tmp_path, parents, initial, expected):
    # A diamond must not be mistaken for a cycle, nor may the last declaration
    # replace the earlier parent. The classical encoder must use the same DAG.
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              f'(:types {parents} left right - ancestor ancestor - object) '
              '(:predicates (ready ?x - left ?y - right) (done)) '
              '(:task t :parameters (?x - left ?y - right)) '
              '(:method m :parameters (?c - child) :task (t ?c ?c) '
              ':subtasks (act ?c ?c)) '
              '(:action act :parameters (?x - left ?y - right) '
              ':precondition (ready ?x ?y) :effect (done)))')
    problem = ('(define (problem p) (:domain d) (:objects c - child) '
               f'(:htn :subtasks (t c c)) (:init {initial}) (:goal (done)))')
    assert not translate(tmp_path, domain, problem).ok
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})
    assert check(result) == expected
    assert 'also inherits' in result.report.to_json()


@pytest.mark.parametrize('types', [
    'child - left child - right right - child left - object',
    'child - left child - child left - object',
])
def test_second_parent_cycle_is_rejected(tmp_path, types):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              f'(:types {types}) (:predicates (p)))')
    problem = '(define (problem p) (:domain d) (:htn :subtasks (and)) (:init))'
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})
    assert not result.ok
    assert any('cyclic HDDL' in d.message for d in result.diagnostic_items)


def test_multiple_inheritance_does_not_widen_parent_to_child(tmp_path):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:types child - left child - right) (:predicates (p)) '
              '(:action act :parameters (?c - child) :effect (p)))')
    problem = ('(define (problem p) (:domain d) (:objects c - left) '
               '(:htn :subtasks (act c)) (:init))')
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})
    assert not result.ok
    assert any('incompatible' in d.message or 'where' in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize('object_type,expected', [('engine', z3.sat), ('part', z3.unsat)])
def test_ipc_method_parameter_is_narrowed_by_subtask_signature(tmp_path, object_type, expected):
    domain = ('(define (domain d) (:requirements :hierarchy :typing :method-preconditions) '
              '(:types engine - part part - object) (:predicates (ready ?x - engine) (done)) '
              '(:task t :parameters (?x - part)) '
              '(:method m :parameters (?x - part) :task (t ?x) '
              ':precondition (ready ?x) :subtasks (act ?x)) '
              '(:action act :parameters (?e - engine) :effect (done)))')
    initial = '(ready c)' if object_type == 'engine' else ''
    problem = ('(define (problem p) (:domain d) '
               f'(:objects c - {object_type}) (:htn :subtasks (t c)) '
               f'(:init {initial}) (:goal (done)))')
    assert not translate(tmp_path, domain, problem).ok
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})
    assert check(result) == expected
    assert 'restricted to the intersection' in result.report.to_json()


@pytest.mark.parametrize('object_type,expected', [('both', z3.sat), ('other-both', z3.sat),
                                               ('left', z3.unsat), ('right', z3.unsat)])
def test_ipc_intersection_retains_all_common_descendants(tmp_path, object_type, expected):
    domain = ('(define (domain d) (:requirements :hierarchy :typing :method-preconditions) '
              '(:types left right - object both - left both - right '
              'other-both - left other-both - right) '
              '(:predicates (l ?x - left) (r ?x - right) (done)) '
              '(:task t :parameters (?x - object)) '
              '(:method m :parameters (?x - object) :task (t ?x) '
              ':precondition (and (l ?x) (r ?x)) :subtasks (and (a ?x) (b ?x))) '
              '(:action a :parameters (?x - left) :effect (done)) '
              '(:action b :parameters (?x - right) :effect (done)))')
    initial = '(l c) (r c)' if expected == z3.sat else ''
    problem = ('(define (problem p) (:domain d) '
               f'(:objects c - {object_type}) (:htn :subtasks (t c)) '
               f'(:init {initial}) (:goal (done)))')
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true', 'plan_horizon': '2'})
    assert check(result) == expected


def test_ipc_empty_intersection_disables_method_without_invalid_ground_call(tmp_path):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:types left right) (:predicates (done)) (:task t) '
              '(:method m :parameters (?x - left) :task (t) :subtasks (act ?x)) '
              '(:action act :parameters (?x - right) :effect (done)))')
    problem = ('(define (problem p) (:domain d) (:objects l - left r - right) '
               '(:htn :subtasks (t)) (:init) (:goal (done)))')
    assert check(translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})) == z3.unsat


@pytest.mark.parametrize('objects,expected', [('c - engine d - part', z3.sat),
                                           ('d - part', z3.unsat)])
def test_ipc_initial_network_parameter_domain_is_intersection(tmp_path, objects, expected):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:types engine - part part - object) (:predicates (done)) '
              '(:action act :parameters (?e - engine) :effect (done)))')
    problem = ('(define (problem p) (:domain d) '
               f'(:objects {objects}) (:htn :parameters (?x - part) :subtasks (act ?x)) '
               '(:init) (:goal (done)))')
    assert check(translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})) == expected


def test_ipc_narrowing_does_not_accept_bad_constant_in_unreachable_method(tmp_path):
    domain = ('(define (domain d) (:requirements :hierarchy :typing) '
              '(:types engine - part part - object) (:constants c - part) '
              '(:predicates (done)) (:task t) '
              '(:method unused :task (t) :subtasks (act c)) '
              '(:action act :parameters (?e - engine) :effect (done)))')
    problem = '(define (problem p) (:domain d) (:htn :subtasks (and)) (:init))'
    result = translate(tmp_path, domain, problem, {'ipc_compatibility': 'true'})
    assert not result.ok
    assert any("'c'" in d.message and 'where' in d.message for d in result.diagnostic_items)
