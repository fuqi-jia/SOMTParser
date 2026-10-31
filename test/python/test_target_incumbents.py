"""Incumbents are available during search and never assert optimality."""
import json

import pytest
import z3

from tools.semantic_checks import target_solve as api


def integer(value):
    return dict(type='int', value=str(value))


def target(body):
    return (body + '\n(check-sat)\n(get-model)\n(exit)\n').encode()


def projection(*names):
    return [dict(id=name, symbol=name) for name in names]


@pytest.mark.parametrize('direction,expected', [('minimize', 2), ('maximize', 8)])
def test_incumbents_arrive_inside_check_and_do_not_stop_optimization(monkeypatch, direction, expected):
    real_check = z3.Optimize.check
    checking = False
    captured = []

    def check(self, *args):
        nonlocal checking
        checking = True
        try:
            return real_check(self, *args)
        finally:
            checking = False

    def receive(candidate):
        assert checking
        # Serializing is safe after the Z3 callback model itself expires.
        captured.append(json.loads(json.dumps(candidate)))

    monkeypatch.setattr(z3.Optimize, 'check', check)
    data = target('(declare-const x Int) (assert (and (>= x 2) (<= x 8))) '
                  '(' + direction + ' x)')
    result = api.solve_target(data, projection('x'), candidate_callback=receive)
    assert result['optimal'] and result['original_objective_values'] == [integer(expected)]
    assert captured and result['candidate_output']['emitted'] == len(captured)
    for i, candidate in enumerate(captured, 1):
        assert candidate['sequence'] == i and candidate['status'] == 'candidate'
        assert candidate['optimal'] is False and candidate['target_witness_replay'] == 'pending'
        assert candidate['target_sha256'] == result['target_sha256']
        assert candidate['objective_directions'] == [direction]
        replay = api.solve_target(data, projection('x'), fixed_values=candidate['witness'],
                                  fixed_objectives=candidate['original_objective_values'])
        assert replay['status'] == replay['target_witness_replay'] == 'sat'


def test_all_ordered_objectives_array_coordinates_and_finite_sets_are_copied():
    data = target('(declare-const a (Array Int Int)) (declare-const s (Array Int Bool)) '
                  '(assert (= s (store ((as const (Array Int Bool)) false) 7 true))) '
                  '(assert (and (<= 0 (select a (- 2))) (<= (select a (- 2)) 3))) '
                  '(assert (and (<= 4 (select a 8)) (<= (select a 8) 9))) '
                  '(maximize (select a (- 2))) (minimize (select a 8))')
    coords = [dict(id='a[-2]', symbol='a', indices=[-2]),
              dict(id='a[8]', symbol='a', indices=[8]), dict(id='s', symbol='s')]
    captured = []
    result = api.solve_target(data, coords, candidate_callback=captured.append)
    assert result['optimal'] and result['original_objective_values'] == [integer(3), integer(4)]
    assert captured
    for c in captured:
        assert c['objective_directions'] == ['maximize', 'minimize']
        assert c['objective_priority'] == 'lex' and c['target_objectives'] == 2
        assert len(c['witness']) == 3
        assert c['witness']['s'] == dict(type='set-int', elements=['7'])
        assert c['signed_objective_values'][0]['value'] == str(-int(c['original_objective_values'][0]['value']))
        assert c['signed_objective_values'][1] == c['original_objective_values'][1]
        replay = api.solve_target(data, coords, fixed_values=c['witness'],
                                  fixed_objectives=c['original_objective_values'])
        assert replay['status'] == 'sat'


def test_unsat_does_not_publish_a_successful_candidate():
    captured = []
    data = target('(declare-const x Int) (assert (> x 5)) (assert (< x 2)) (minimize x)')
    result = api.solve_target(data, projection('x'), candidate_callback=captured.append)
    assert result['status'] == 'unsat' and not captured


def test_callback_failure_is_not_swallowed_by_ctypes():
    def fail(candidate):
        raise RuntimeError('candidate storage failed')

    data = target('(declare-const x Int) (assert (= x 4)) (minimize x)')
    with pytest.raises(RuntimeError, match='candidate storage failed'):
        api.solve_target(data, projection('x'), candidate_callback=fail)


def test_consumer_can_stop_snapshots_without_stopping_optimization():
    captured = []

    def first_only(candidate):
        captured.append(candidate)
        return False

    data = target('(declare-const x Int) (assert (and (>= x 2) (<= x 8))) (maximize x)')
    result = api.solve_target(data, projection('x'), candidate_callback=first_only)
    assert len(captured) == result['candidate_output']['emitted'] == 1
    assert result['candidate_output']['enabled'] is False
    assert result['optimal'] and result['original_objective_values'] == [integer(8)]


def test_unrepresentable_intermediate_model_is_skipped_without_poisoning_final_result(monkeypatch):
    real_encode = api.encode_value
    first = True

    def encode(value):
        nonlocal first
        if first:
            first = False
            raise ValueError('provisional set is not finite')
        return real_encode(value)

    monkeypatch.setattr(api, 'encode_value', encode)
    data = target('(declare-const x Int) (assert (= x 4)) (minimize x)')
    result = api.solve_target(data, projection('x'), candidate_callback=lambda candidate: None)
    assert result['optimal'] and result['target_witness_replay'] == 'sat'
    assert result['candidate_output']['skipped'] == 1
    assert result['candidate_output']['last_skip_reason'] == 'provisional set is not finite'


@pytest.mark.parametrize('fixed,callback', [(True, lambda c: None), (False, 5)])
def test_invalid_callback_modes_are_rejected(fixed, callback):
    data = target('(declare-const x Int) (assert (= x 4)) (minimize x)')
    kwargs = dict(fixed_values={'x': integer(4)}, fixed_objectives=[integer(4)]) if fixed else {}
    with pytest.raises(ValueError):
        api.solve_target(data, projection('x'), candidate_callback=callback, **kwargs)


def test_plain_sat_requires_no_optimization_callback():
    with pytest.raises(ValueError, match='independent target optimization'):
        api.solve_target(target('(declare-const x Int)'), projection('x'),
                         candidate_callback=lambda c: None)


def test_unattained_infimum_candidates_do_not_claim_an_optimum():
    captured = []
    data = target('(declare-const x Real) (assert (> x 0)) (minimize x)')
    result = api.solve_target(data, projection('x'), candidate_callback=captured.append)
    assert result['status'] == 'sat' and result['optimal'] is False
    assert all(c['optimal'] is False for c in captured)
