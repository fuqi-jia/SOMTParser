import pytest
import z3

from tools.semantic_checks.ground_candidate import verify_ground_candidate
from tools.semantic_checks.target_solve import solve_target
from tools.semantic_checks.target_bound_solve import solve_target_at_objectives


def iv(value):return dict(type='int', value=str(value))
def bv(value):return dict(type='bool', value=value)
def target(body):return (body+'\n(check-sat)\n(exit)\n').encode()


def test_complete_array_map_candidate_and_serialization():
    data=target('(declare-const x (Array Int (Array Int Bool))) (declare-const y Int) '
        '(assert (= ((_ map and) (select x 0) (store ((as const (Array Int Bool)) false) 3 true)) (select x 0))) '
        '(assert (select (select x 0) 3)) (assert (= y 2)) (minimize y)')
    projection=[dict(id='x0',symbol='x',indices=[0])]
    values={'x0':dict(type='set-int',elements=['3'])}
    extra=dict(projection=[dict(id='y',symbol='y')],values={'y':iv(2)},origin='test')
    result=verify_ground_candidate(data,projection,values,[iv(2)],extra)
    assert result['status']==result['target_witness_replay']=='sat'
    assert not result['solver_search_performed']
    assert result['ground_candidate_certificate']['all_original_assertions_true']==3
    solver=z3.Solver();solver.from_string(data.decode().split('(minimize')[0]+result['ground_candidate_certificate']['serialized_assignments_smt2'])
    assert solver.check()==z3.sat


def test_array_defaults_are_choices_not_a_weakened_domain():
    data=target('(declare-const a (Array Int Bool)) (assert (select a 4))')
    p=[dict(id='a0',symbol='a',indices=[0])]
    assert verify_ground_candidate(data,p,{'a0':bv(True)},[]) is None
    result=solve_target(data,p,fixed_values={'a0':bv(True)},fixed_objectives=[],ground_candidate=True)
    assert result['status']==result['target_witness_replay']=='sat'
    assert 'ground_candidate_certificate' not in result


def test_false_auxiliary_candidate_is_not_model_unsat():
    data=target('(declare-const x Int) (declare-const y Int) (assert (= y (+ x 1)))')
    p=[dict(id='x',symbol='x')];extra=dict(projection=[dict(id='y',symbol='y')],values={'y':iv(9)},origin='wrong')
    assert verify_ground_candidate(data,p,{'x':iv(0)},[],extra) is None
    result=solve_target(data,p,fixed_values={'x':iv(0)},fixed_objectives=[],auxiliary_candidate=extra,ground_candidate=True)
    assert result['status']=='sat' and result['auxiliary_attempt']['fallback_to_public_witness']


def test_nested_array_coordinates_survive_exact_smt_replay():
    data=target('(declare-const a (Array Int (Array Int Int))) '
        '(assert (= (+ (select (select a 2) 3) (select (select a (- 4)) 8)) 11))')
    p=[dict(id='p',symbol='a',indices=[2,3]),dict(id='q',symbol='a',indices=[-4,8])]
    result=verify_ground_candidate(data,p,{'p':iv(5),'q':iv(6)},[])
    assert result['witness']=={'p':iv(5),'q':iv(6)}
    assert result['target_witness_replay']=='sat'


@pytest.mark.parametrize('direction,value', [('minimize',0),('maximize',3)])
def test_ground_feasibility_keeps_original_objective_direction(direction,value):
    data=target('(declare-const x Int) (assert (and (>= x 0) (<= x 3))) ('+direction+' x)')
    p=[dict(id='x',symbol='x')]
    result=solve_target_at_objectives(data,p,[iv(value)],candidate_witness={'x':iv(value)},ground_candidate=True)
    assert result['optimal'] and result['optimality_status']=='unsat'
    assert result['feasibility_method']=='exact complete ground interpretation'
    assert result['original_objective_values']==[iv(value)]


def test_ground_candidate_never_restricts_better_query():
    data=target('(declare-const x Int) (declare-const y Int) (assert (= y (+ x 1))) (assert (>= x 0)) (minimize x)')
    p=[dict(id='x',symbol='x')];extra=dict(projection=[dict(id='y',symbol='y')],values={'y':iv(2)},origin='test')
    result=solve_target_at_objectives(data,p,[iv(1)],candidate_witness={'x':iv(1)},auxiliary_candidate=extra,ground_candidate=True)
    assert not result['optimal'] and result['optimality_status']=='sat'
    assert result['ground_candidate_certificate']['all_original_assertions_true']==2
    solver=z3.Solver();solver.from_string(result['no_better_query_smt2']);solver.add(z3.Int('x')==0,z3.Int('y')==1)
    assert solver.check()==z3.sat


def test_wrong_objective_and_unknown_functions_decline_certificate():
    p=[dict(id='x',symbol='x')]
    assert verify_ground_candidate(target('(declare-const x Int) (minimize x)'),p,{'x':iv(2)},[iv(1)])is None
    data=target('(declare-const x Int) (declare-fun f (Int) Int) (assert (= (f x) 7))')
    assert verify_ground_candidate(data,p,{'x':iv(2)},[])is None


@pytest.mark.parametrize('suffix', ['', '(minimize x)'])
def test_missing_costs_decline_optional_certificate_and_preserve_public_contract(suffix):
    data = target('(declare-const x Int) (assert (= x 2)) ' + suffix)
    projection = [dict(id='x', symbol='x')]
    assert verify_ground_candidate(data, projection, {'x': iv(2)}, None) is None
    for use_ground in [False, True]:
        with pytest.raises(ValueError, match='all ordered objective'):
            solve_target(data, projection, fixed_values={'x': iv(2)},
                         ground_candidate=use_ground)
    if not suffix:
        result = solve_target(data, projection, fixed_values={'x': iv(2)},
                              fixed_objectives=[], ground_candidate=True)
        assert result['status'] == 'sat' and result['original_objective_values'] == []


@pytest.mark.parametrize('corruption', [None, 'last-constraint', 'last-coordinate', 'second-objective'])
def test_large_complete_interpretation_checks_every_constraint_and_ordered_cost(corruption):
    size = 513
    declarations = ' '.join('(declare-const x' + str(i) + ' Int)' for i in range(size))
    constraints = ' '.join('(assert (= x' + str(i) + ' ' +
                           str(i + (1 if corruption == 'last-constraint' and i == size - 1 else 0)) + '))'
                           for i in range(size))
    data = target(declarations + constraints + '(minimize x512) (maximize x1)')
    projection = [dict(id='x' + str(i), symbol='x' + str(i)) for i in range(size)]
    values = {'x' + str(i): iv(i) for i in range(size)}
    costs = [iv(512), iv(1)]
    if corruption == 'last-coordinate':
        values['x512'] = iv(0)
    if corruption == 'second-objective':
        costs[1] = iv(0)
    result = verify_ground_candidate(data, projection, values, costs)
    if corruption is not None:
        assert result is None
        return
    assert result['witness'] == values
    assert result['original_objective_values'] == costs
    assert result['signed_objective_values'] == [iv(512), iv(-1)]
    certificate = result['ground_candidate_certificate']
    assert certificate['all_original_assertions_true'] == size
    assert certificate['serialized_replay_assertions_true'] == size
    assert certificate['source_coordinates_rechecked'] == size
    assert certificate['original_objectives_rechecked'] == 2
    assert result['target_witness_replay'] == 'sat'


def test_batch_interpretation_preserves_exact_real_values_and_mixed_directions():
    data = target('(declare-const r Real) (assert (= r (/ 3.0 2.0))) '
                  '(maximize r) (minimize (+ r (/ 1.0 2.0)))')
    projection = [dict(id='r', symbol='r')]
    value = dict(type='real', numerator='6', denominator='4')
    second = dict(type='real', numerator='2', denominator='1')
    result = verify_ground_candidate(data, projection, {'r': value}, [value, second])
    assert result['witness']['r'] == dict(type='real', numerator='3', denominator='2')
    assert result['signed_objective_values'] == [
        dict(type='real', numerator='-3', denominator='2'), second]
    assert result['objective_directions'] == ['maximize', 'minimize']
    assert result['target_witness_replay'] == 'sat'
