import pytest
import z3

from tools.semantic_checks.target_bound_solve import solve_target_at_objectives


def integer(value):
    return dict(type='int', value=str(value))


def target(body):
    return (body + '\n(check-sat)\n(get-model)\n(exit)\n').encode()


@pytest.mark.parametrize('direction,bound', [('minimize', 2), ('maximize', 8)])
def test_correct_finite_bound_and_complete_no_better_query(direction, bound):
    data = target('(declare-const x Int) (assert (and (<= 2 x) (<= x 8))) (' + direction + ' x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(bound)])
    assert result['status'] == result['target_witness_replay'] == 'sat'
    assert result['optimal'] and result['optimality_status'] == 'unsat'
    assert result['original_objective_values'] == [integer(bound)]
    expected = bound if direction == 'minimize' else -bound
    certified = result['objective_bounds'][0]
    assert certified['finite_attained'] and certified['lexicographic_prefix'] == []
    assert certified['lower_smt2'] == certified['upper_smt2'] == z3.IntVal(expected).sexpr()
    replay = z3.Solver(); replay.from_string(result['no_better_query_smt2'])
    assert replay.check() == z3.unsat


@pytest.mark.parametrize('direction,bound,better', [('minimize', 5, 2), ('maximize', 5, 8)])
def test_suboptimal_candidate_is_never_assumed_optimal(direction, bound, better):
    data = target('(declare-const x Int) (assert (and (<= 2 x) (<= x 8))) (' + direction + ' x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(bound)])
    assert result['status'] == 'sat' and result['optimal'] is False
    assert result['optimality_status'] == 'sat'
    assert not result.get('objective_bounds')
    actual = int(result['better_original_objective_values'][0]['value'])
    assert actual < bound if direction == 'minimize' else actual > bound
    # An erroneous candidate equality inside this query would make it UNSAT.
    replay = z3.Solver(); replay.from_string(result['no_better_query_smt2'])
    assert replay.check() == z3.sat


def test_infeasible_bound_does_not_report_model_unsat():
    data = target('(declare-const x Int) (assert (>= x 2)) (minimize x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(1)])
    assert result['status'] == 'candidate-infeasible'
    assert result['optimal'] is False


def test_full_lexicographic_prefix_and_maximization_sign():
    data = target('(declare-const x Int) (declare-const y Int) '
                  '(assert (and (>= x 0) (>= y 0) (<= (+ x y) 4))) (maximize x) (minimize y)')
    projection = [dict(id=name, symbol=name) for name in ('x', 'y')]
    good = solve_target_at_objectives(data, projection, [integer(4), integer(0)])
    bad = solve_target_at_objectives(data, projection, [integer(3), integer(1)])
    assert good['optimal'] and not bad['optimal']


def test_quantified_original_assertion_is_retained_in_both_queries():
    data = target('(declare-const a (Array Int Int)) (declare-const x Int) '
                  '(assert (forall ((i Int)) (>= (select a i) 7))) '
                  '(assert (= x (select a 3))) (minimize x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(7)])
    assert result['optimal'] and result['witness']['x'] == integer(7)
    assert '(forall ' in result['no_better_query_smt2']


def test_real_infimum_is_not_an_attained_optimum():
    data = target('(declare-const x Real) (assert (> x 0)) (minimize x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')],
                                        [dict(type='real', numerator='0', denominator='1')])
    assert result['status'] == 'candidate-infeasible' and not result['optimal']


def test_missing_objectives_are_refused():
    with pytest.raises(ValueError):
        solve_target_at_objectives(target('(declare-const x Int) (minimize x)'),
                                   [dict(id='x', symbol='x')], [])


@pytest.mark.parametrize('seed,expected', [(0, True), (2, False)])
def test_seed_is_only_a_feasibility_witness_and_cannot_prove_optimality(seed, expected):
    data = target('(declare-const x Int) (assert (and (<= 0 x) (<= x 5))) (minimize x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(seed)],
                                        candidate_witness={'x': integer(seed)})
    assert result['status'] == result['target_witness_replay'] == 'sat'
    assert result['optimal'] is expected
    assert result['witness'] == {'x': integer(seed)}
    assert result['candidate_witness_origin'] == 'caller'
    replay = z3.Solver(); replay.from_string(result['no_better_query_smt2'])
    assert replay.check() == (z3.unsat if expected else z3.sat)


@pytest.mark.parametrize('seed', [{}, {'x': {'type': 'bool', 'value': True}}])
def test_partial_or_wrongly_typed_seed_is_rejected(seed):
    data = target('(declare-const x Int) (assert (>= x 0)) (minimize x)')
    with pytest.raises(ValueError):
        solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(0)],
                                   candidate_witness=seed)


@pytest.mark.parametrize('seed', [-1, 1])
def test_seed_must_satisfy_every_assertion_and_its_claimed_objective(seed):
    data = target('(declare-const x Int) (assert (>= x 0)) (minimize x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(0)],
                                        candidate_witness={'x': integer(seed)})
    assert result['status'] == 'candidate-infeasible' and not result['optimal']


def test_seed_does_not_constrain_later_lexicographic_improvement():
    data = target('(declare-const x Int) (declare-const y Int) '
                  '(assert (and (>= x 0) (>= y 0) (<= x 4) (<= y 4))) '
                  '(minimize x) (maximize y)')
    result = solve_target_at_objectives(data, [dict(id=n, symbol=n) for n in ('x', 'y')],
                                        [integer(0), integer(2)],
                                        candidate_witness={'x': integer(0), 'y': integer(2)})
    assert not result['optimal'] and result['optimality_status'] == 'sat'
    better = result['better_original_objective_values']
    assert better[0] == integer(0) and int(better[1]['value']) > 2


@pytest.mark.parametrize('direction,sign', [('minimize', 1), ('maximize', -1)])
def test_exact_rational_attained_bounds_preserve_normalized_direction(direction, sign):
    data = target('(declare-const x Real) (assert (= x (/ 1.0 3.0))) (' + direction + ' x)')
    value = dict(type='real', numerator='1', denominator='3')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [value])
    assert result['optimal'] and result['target_witness_replay'] == 'sat'
    bounds = result['objective_bounds']
    assert len(bounds) == 1 and bounds[0]['finite_attained']
    assert bounds[0]['lower_smt2'] == bounds[0]['upper_smt2'] == z3.RealVal(str(sign) + '/3').sexpr()
    assert bounds[0]['lexicographic_prefix'] == []


def test_later_attained_bound_requires_earlier_optimal_prefix():
    # Without fixing the first optimum, y can be 0. At optimal x=0, y is 10.
    data = target('(declare-const x Int) (declare-const y Int) '
                  '(assert (or (and (= x 0) (= y 10)) (and (= x 1) (= y 0)))) '
                  '(minimize x) (minimize y)')
    projection = [dict(id=n, symbol=n) for n in ('x', 'y')]
    result = solve_target_at_objectives(data, projection, [integer(0), integer(10)])
    assert result['optimal']
    first, second = result['objective_bounds']
    assert first['lexicographic_prefix'] == []
    assert second['lexicographic_prefix'] == [dict(objective_index=0, signed_value=integer(0))]
    assert second['lower_smt2'] == second['upper_smt2'] == '10'
    x, y = z3.Ints('x y')
    source = z3.Solver()
    source.add(z3.Or(z3.And(x == 0, y == 10), z3.And(x == 1, y == 0)), y < 10)
    assert source.check() == z3.sat
    source.add(x == 0)
    assert source.check() == z3.unsat


def test_unknown_improvement_query_cannot_create_attained_bounds(monkeypatch):
    import tools.semantic_checks.target_bound_solve as module
    original_solver = z3.Solver

    class UnknownImprovement:
        def __init__(self, *args, **kwargs):
            self.inner = original_solver(*args, **kwargs)

        def add(self, *args):
            self.inner.add(*args)

        def check(self):
            return z3.unknown

        def reason_unknown(self):
            return 'controlled unknown improvement result'

        def sexpr(self):
            return self.inner.sexpr()

    def progress(event):
        # Switch factories only after the real feasibility and witness replay.
        if event['phase'] == 'target-witness-replay' and event['event'] == 'completed':
            monkeypatch.setattr(module.z3, 'Solver', UnknownImprovement)

    data = target('(declare-const x Int) (assert (= x 1)) (minimize x)')
    result = solve_target_at_objectives(data, [dict(id='x', symbol='x')], [integer(1)],
                                        progress_callback=progress)
    assert result['status'] == result['target_witness_replay'] == 'sat'
    assert not result['optimal'] and result['optimality_status'] == 'unknown'
    assert not result.get('objective_bounds')
