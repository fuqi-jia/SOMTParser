"""Exact bounded action costs, independently replayed with rational arithmetic."""
from fractions import Fraction
from pathlib import Path
import re

import pytest
import z3
import somtparser as sp


def translate(tmp_path, actions, initial='(= (total-cost) 0)', horizon=2,
              declarations='', goal='(done)', language='pddl', hierarchy='', tasks='(t)'):
    domain = ('(define (domain d) (:requirements :adl :action-costs '
              + (':hierarchy :htn-method-pre-eff' if language == 'hddl' else '') + ') '
              '(:predicates (p) (done)) (:functions (total-cost) - number ' + declarations + ') '
              + hierarchy + actions + ')')
    problem = tmp_path / 'problem.pddl'
    problem.write_text('(define (problem p) (:domain d) '
                       + (f'(:htn :subtasks {tasks}) ' if language == 'hddl' else '')
                       + f'(:init {initial}) (:goal {goal}) (:metric minimize (total-cost)))')
    return sp.translate(source=domain, data=[str(problem)], language=language, profile='bmc',
                        options={'plan_horizon': str(horizon), 'decomposition_depth': '2'})


def optimizer(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Optimize()
    solver.set(timeout=10000)
    text = result.to_smt2(dialect=sp.OmtDialect.Z3)
    assert '(minimize ' in text
    solver.from_string(text)
    assert solver.check() == z3.sat
    return solver


@pytest.mark.parametrize('horizon', [1, 2, 3])
def test_longer_plan_can_be_cheaper_and_padding_is_free(tmp_path, horizon):
    actions = '''(:action direct :effect (and (done) (increase (total-cost) 7)))
      (:action prepare :effect (and (p) (increase (total-cost) 0.1)))
      (:action finish :precondition (p) :effect (and (done) (increase (total-cost) 0.2)))'''
    result = translate(tmp_path, actions, initial='(= (total-cost) 1.25)', horizon=horizon)
    solver = optimizer(result)
    value = solver.model().eval(z3.Real(f'__pddl_total_cost@{horizon}'))
    expected = Fraction('1.25') + (Fraction(7) if horizon == 1 else Fraction('0.1') + Fraction('0.2'))
    assert value.as_fraction() == expected
    assert not result.report.fidelity.preserves_optimum  # only bounded optimization


def test_conditional_costs_use_old_state_and_all_increases_add(tmp_path):
    actions = '''(:action a :effect (and (p) (done) (increase (total-cost) 2)
      (when (p) (increase (total-cost) 100))
      (when (not (p)) (increase (total-cost) 0.5))))'''
    solver = optimizer(translate(tmp_path, actions, horizon=1))
    assert solver.model().eval(z3.Real('__pddl_total_cost@1')).as_fraction() == Fraction('2.5')


def test_static_function_cost_and_zero_cost_method_event(tmp_path):
    result = translate(tmp_path,
        '(:action a :precondition (p) :effect (and (done) (increase (total-cost) (price))))',
        declarations='(price) - number', initial='(= (total-cost) 0) (= (price) 2.75)',
        horizon=1, language='hddl', hierarchy='(:task t) '
        '(:method m :task (t) :effect (p) :subtasks (a))')
    solver = optimizer(result)
    assert solver.model().eval(z3.Real('__pddl_total_cost@1')).as_fraction() == 0
    assert solver.model().eval(z3.Real('__pddl_total_cost@2')).as_fraction() == Fraction('2.75')


@pytest.mark.parametrize('effect,initial,declarations', [
    ('(increase (total-cost) -1)', '(= (total-cost) 0)', ''),
    ('(increase (total-cost) (total-cost))', '(= (total-cost) 0)', ''),
    ('(assign (total-cost) 3)', '(= (total-cost) 0)', ''),
    ('(increase (price) 3)', '(= (total-cost) 0) (= (price) 1)', '(price) - number'),
    ('(increase (total-cost) (price))', '(= (total-cost) 0)', '(price) - number'),
    ('(increase (total-cost) 1)', '(= (total-cost) 0) (= (total-cost) 2)', ''),
    ('(increase (total-cost) 1)', '', ''),
])
def test_invalid_or_dynamic_costs_are_rejected(tmp_path, effect, initial, declarations):
    result = translate(tmp_path, f'(:action a :effect (and (done) {effect}))',
                       initial=initial, declarations=declarations)
    assert not result.ok


@pytest.mark.parametrize('horizon', [0, 1])
def test_unused_bad_action_is_validated_before_hierarchy_filter(tmp_path, horizon):
    result = translate(tmp_path, '(:action unused :effect (increase (total-cost) -2))',
        horizon=horizon, language='hddl', hierarchy='(:task t) (:method m :task (t))', goal='(and)')
    assert not result.ok


def test_universal_cost_effect_preserves_each_ground_increment(tmp_path):
    result = translate(tmp_path,
        '(:constants a b) (:action act :effect (and (done) '
        '(forall (?x) (increase (total-cost) (price ?x)))))',
        declarations='(price ?x) - number',
        initial='(= (total-cost) 0) (= (price a) 0.2) (= (price b) 0.3)', horizon=1)
    solver = optimizer(result)
    assert solver.model().eval(z3.Real('__pddl_total_cost@1')).as_fraction() == Fraction('0.5')


@pytest.mark.parametrize('material,cost', [('wood', 1), ('stone', 2), ('earth', 3)])
def test_minecraft_original_domain_single_block_cost(tmp_path, material, cost):
    # A derived task, not counted as conversion of the original full house.
    root = Path(__file__).resolve().parents[2] / 'languages/hddl/instances/upstream'
    original = (root / 'minecraft-costs-problem.hddl').read_text()
    problem = tmp_path / 'single-block.hddl'
    problem.write_text(re.sub(r'\(buildhouse [^()]+\)',
        f'(placeblockabstract l-1-0-0 {material})', original))
    result = sp.translate(str(root / 'minecraft-costs.hddl'), data=[str(problem)],
        language='hddl', profile='bmc', options={'plan_horizon': '1',
        'decomposition_depth': '1', 'lenient_requirements': '1'})
    solver = optimizer(result)
    assert solver.model().eval(z3.Real('__pddl_total_cost@2')).as_fraction() == cost


def test_original_minecraft_pair_keeps_metric_and_reports_only_bounded_unsat():
    root = Path(__file__).resolve().parents[2] / 'languages/hddl/instances/upstream'
    result = sp.translate(str(root / 'minecraft-costs.hddl'),
        data=[str(root / 'minecraft-costs-problem.hddl')], language='hddl', profile='bmc',
        options={'plan_horizon': '6', 'decomposition_depth': '3', 'lenient_requirements': '1'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Optimize()
    solver.set(timeout=10000)
    text = result.to_smt2(dialect=sp.OmtDialect.Z3)
    assert '(minimize ' in text
    solver.from_string(text)
    assert solver.check() == z3.unsat
    assert not result.report.fidelity.complete
