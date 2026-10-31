import pytest
import z3

from tools.semantic_checks import target_solve
from tools.semantic_checks.target_bound_solve import solve_target_at_objectives


def iv(value):
    return dict(type='int', value=str(value))


def target(body):
    return (body + '\n(check-sat)\n(exit)\n').encode()


def hint(value):
    return dict(projection=[dict(id='hidden', symbol='y')],
                values={'hidden': iv(value)}, origin='test candidate')


PUBLIC = [dict(id='x', symbol='x')]
DATA = target('(declare-const x Int) (declare-const y Int) '
              '(assert (= y (+ x 1))) (assert (>= x 0)) (minimize x)')


@pytest.mark.parametrize('value,attempt', [(2, 'sat'), (9, 'unsat')])
def test_auxiliary_candidate_success_or_exact_fallback(value, attempt):
    result = target_solve.solve_target(DATA, PUBLIC, fixed_values={'x': iv(1)},
        fixed_objectives=[iv(1)], auxiliary_candidate=hint(value))
    assert result['status'] == result['target_witness_replay'] == 'sat'
    assert result['auxiliary_attempt']['status'] == attempt
    assert result['auxiliary_attempt']['fallback_to_public_witness'] == (attempt != 'sat')
    assert result['witness'] == {'x': iv(1)}
    assert result['auxiliary_witness'] == {'hidden': iv(2)}
    assert result['projection'] == PUBLIC
    assert not result['optimal']


def unknown_first(monkeypatch):
    original = z3.Solver.check
    calls = []
    def check(self, *args, **kwargs):
        calls.append(1)
        return z3.unknown if len(calls) == 1 else original(self, *args, **kwargs)
    monkeypatch.setattr(z3.Solver, 'check', check)


def test_unknown_auxiliary_candidate_retries_original_public_witness(monkeypatch):
    unknown_first(monkeypatch)
    result = target_solve.solve_target(DATA, PUBLIC, fixed_values={'x': iv(1)},
        fixed_objectives=[iv(1)], auxiliary_candidate=hint(2))
    assert result['status'] == result['target_witness_replay'] == 'sat'
    assert result['auxiliary_attempt']['status'] == 'unknown'
    assert result['auxiliary_attempt']['fallback_status'] == 'sat'


def test_array_cells_and_finite_sets_are_serialized_and_replayed():
    data = target('(declare-const x Int) (declare-const a (Array Int Int)) '
        '(declare-const s (Array Int Bool)) (assert (= x (select a 0))) '
        '(assert (= (select a 1) (+ x 1))) '
        '(assert (= s (store (store ((as const (Array Int Bool)) false) (- 2) true) 3 true)))')
    auxiliary = dict(projection=[dict(id='a0', symbol='a', indices=[0]),
        dict(id='a1', symbol='a', indices=[1]), dict(id='s', symbol='s')],
        values={'a0': iv(3), 'a1': iv(4), 's': dict(type='set-int', elements=['-2', '3'])},
        origin='complete source output')
    result = target_solve.solve_target(data, PUBLIC, fixed_values={'x': iv(3)},
        fixed_objectives=[], auxiliary_candidate=auxiliary)
    assert result['target_witness_replay'] == result['auxiliary_witness_replay'] == 'sat'
    assert result['auxiliary_witness'] == auxiliary['values']
    assert result['witness'] == {'x': iv(3)}


def test_suboptimal_auxiliary_candidate_never_enters_better_query():
    result = solve_target_at_objectives(DATA, PUBLIC, [iv(1)], candidate_witness={'x': iv(1)},
        auxiliary_candidate=hint(2))
    assert result['status'] == 'sat' and not result['optimal']
    assert result['optimality_status'] == 'sat'
    assert result['no_candidate_auxiliary_equalities_in_optimality_query']
    solver = z3.Solver(); solver.from_string(result['no_better_query_smt2'])
    solver.add(z3.Int('x') == 0, z3.Int('y') == 1)
    assert solver.check() == z3.sat


def test_wrong_bound_hint_falls_back_before_proving_optimum():
    result = solve_target_at_objectives(DATA, PUBLIC, [iv(0)], candidate_witness={'x': iv(0)},
        auxiliary_candidate=hint(99))
    assert result['optimal'] and result['optimality_status'] == 'unsat'
    assert result['candidate_auxiliary_attempt']['status'] == 'unsat'
    assert result['candidate_auxiliary_attempt']['fallback_status'] == 'sat'
    assert result['auxiliary_witness'] == {'hidden': iv(1)}


def test_unknown_bound_hint_falls_back(monkeypatch):
    unknown_first(monkeypatch)
    result = solve_target_at_objectives(DATA, PUBLIC, [iv(0)], candidate_witness={'x': iv(0)},
        auxiliary_candidate=hint(1))
    assert result['optimal']
    assert result['candidate_auxiliary_attempt']['status'] == 'unknown'
    assert result['candidate_auxiliary_attempt']['fallback_status'] == 'sat'


@pytest.mark.parametrize('indices', [[], [0]])
def test_auxiliary_cannot_extend_a_public_symbol(indices):
    data = DATA if not indices else target('(declare-const x (Array Int Int))')
    projection = PUBLIC if not indices else [dict(id='x0', symbol='x', indices=[0])]
    extra = dict(projection=[dict(id='extra', symbol='x', indices=indices)],
                 values={'extra': iv(1)}, origin='invalid overlap')
    with pytest.raises(ValueError, match='outside public projection'):
        target_solve.solve_target(data, projection,
            fixed_values={projection[0]['id']: iv(1)}, fixed_objectives=[iv(1)] if not indices else [],
            auxiliary_candidate=extra)


def test_malformed_auxiliary_value_is_an_interface_error():
    extra = hint(1); extra['values']['hidden'] = dict(type='bool', value=True)
    with pytest.raises(ValueError, match='Boolean witness'):
        target_solve.solve_target(DATA, PUBLIC, fixed_values={'x': iv(0)},
            fixed_objectives=[iv(0)], auxiliary_candidate=extra)


def test_auxiliary_is_rejected_in_ordinary_optimize_mode():
    with pytest.raises(ValueError, match='fixed public feasibility'):
        target_solve.solve_target(DATA, PUBLIC, auxiliary_candidate=hint(1))


def test_serialized_auxiliary_values_are_rechecked_against_original_assertions(monkeypatch):
    original = target_solve.encode_value
    def corrupt(value):
        if z3.is_int_value(value) and value.as_long() == 2:
            return iv(9)
        return original(value)
    monkeypatch.setattr(target_solve, 'encode_value', corrupt)
    result = target_solve.solve_target(DATA, PUBLIC, fixed_values={'x': iv(1)},
        fixed_objectives=[iv(1)], auxiliary_candidate=hint(2))
    assert result['status'] == 'sat'
    assert result['auxiliary_witness_replay'] == result['target_witness_replay'] == 'unsat'


@pytest.mark.parametrize('bound_mode', [False, True])
def test_rejected_finite_hint_does_not_require_finite_hidden_fallback_value(bound_mode):
    data = target('(declare-const x Int) (declare-const s (Array Int Bool)) '
        '(assert (= s ((as const (Array Int Bool)) true))) (assert (>= x 0)) (minimize x)')
    auxiliary = dict(projection=[dict(id='s', symbol='s')],
        values={'s': dict(type='set-int', elements=[])}, origin='bad finite guess')
    if bound_mode:
        result = solve_target_at_objectives(data, PUBLIC, [iv(0)],
            candidate_witness={'x': iv(0)}, auxiliary_candidate=auxiliary)
        assert result['optimal'] and result['optimality_status'] == 'unsat'
        assert result['candidate_auxiliary_attempt']['fallback_status'] == 'sat'
        assert result['candidate_auxiliary_serialization_skipped']
    else:
        result = target_solve.solve_target(data, PUBLIC, fixed_values={'x': iv(0)},
            fixed_objectives=[iv(0)], auxiliary_candidate=auxiliary)
        assert result['auxiliary_attempt']['fallback_status'] == 'sat'
        assert result['auxiliary_serialization_skipped']
    assert result['status'] == result['target_witness_replay'] == 'sat'
    assert result['witness'] == {'x': iv(0)}
