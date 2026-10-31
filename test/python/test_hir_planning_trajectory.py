"""Public PDDL3 constructors: exact relation, penalty identity and dense time."""
import pytest
import z3
from somtparser import planning as n
from somtparser import planning_trajectory as p


def literal(kind, text):
    return n.literal(getattr(n.HirSort, kind)(), text)


def target(model):
    result = model.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def exact(model, oracle):
    solver = z3.Solver()
    solver.add(z3.Tactic('qe')(z3.Xor(target(model), oracle)).as_expr())
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('name', [
    'AT_END', 'ALWAYS', 'SOMETIME', 'WITHIN', 'AT_MOST_ONCE',
    'SOMETIME_BEFORE', 'SOMETIME_AFTER', 'ALWAYS_WITHIN', 'HOLD_DURING', 'HOLD_AFTER',
])
def test_finite_complete_boolean_relation(name):
    model = n.HirModel()
    first = [model.declare(f'p{i}', n.HirSort.boolean()) for i in range(3)]
    second = [model.declare(f'q{i}', n.HirSort.boolean()) for i in range(3)]
    pair = name in {'SOMETIME_BEFORE', 'SOMETIME_AFTER', 'ALWAYS_WITHIN'}
    samples = [p.HirTrajectorySample(literal('boolean', 'true'), literal('real', str(i)),
               n.planning_numeric_predicate(first[i]), n.planning_numeric_predicate(second[i]) if pair else None)
               for i in range(3)]
    kwargs = {}
    if name in {'WITHIN', 'ALWAYS_WITHIN', 'HOLD_DURING', 'HOLD_AFTER'}:
        kwargs['lower'] = literal('real', '1')
    if name == 'HOLD_DURING':
        kwargs['upper'] = literal('real', '2')
    encoded = p.planning_finite_trajectory(model, getattr(p.TrajectoryOperator, name), samples, **kwargs)
    out = encoded.to_model(model, hard=True)
    a = [z3.Bool(f'p{i}') for i in range(3)]
    b = [z3.Bool(f'q{i}') for i in range(3)]
    expectations = {
        'AT_END': a[2], 'ALWAYS': z3.And(*a), 'SOMETIME': z3.Or(*a),
        'WITHIN': z3.Or(a[0], a[1]), 'AT_MOST_ONCE': z3.Not(z3.And(a[0], z3.Not(a[1]), a[2])),
        'SOMETIME_BEFORE': z3.And(z3.Not(a[0]), z3.Implies(a[1], b[0]), z3.Implies(a[2], z3.Or(b[0], b[1]))),
        'SOMETIME_AFTER': z3.And(*[z3.Implies(a[i], z3.Or(*b[i:])) for i in range(3)]),
        'ALWAYS_WITHIN': z3.And(*[z3.Implies(a[i], z3.Or(*b[i:min(3,i+2)])) for i in range(3)]),
        'HOLD_DURING': a[1], 'HOLD_AFTER': a[2],
    }
    exact(out, expectations[name])
    exact(model, z3.BoolVal(True))


def test_undefined_soft_preference_does_not_invalidate_plan():
    model = n.HirModel()
    value = model.declare('p', n.HirSort.boolean())
    defined = model.declare('d', n.HirSort.boolean())
    numeric = n.HirNumericValue(n.operation('ite', [value, literal('real', '1'), literal('real', '0')]), defined)
    condition = n.planning_numeric_compare('>', numeric, n.planning_numeric_constant('0'))
    sample = p.HirTrajectorySample(literal('boolean', 'true'), literal('real', '0'), condition)
    encoding = p.planning_finite_trajectory(model, p.TrajectoryOperator.ALWAYS, [sample])
    soft = encoding.to_model(model, hard=False)
    counts = p.planning_preferences(soft, [p.HirPreferenceInstance(
        'goal-1', 'quality', literal('boolean', 'true'), encoding.satisfied)])
    count = soft.declare('count', n.HirSort.integer())
    soft.constrain(n.operation('eq', [count, counts.violation_count('quality')]))
    exact(soft, z3.Int('count') == z3.If(z3.And(z3.Bool('p'), z3.Bool('d')), 0, 1))
    exact(encoding.to_model(model, hard=True), z3.And(z3.Bool('p'), z3.Bool('d')))


def test_quantified_groups_action_occurrences_and_anonymous_metric():
    model = n.HirModel()
    a = model.declare('a', n.HirSort.boolean()); b = model.declare('b', n.HirSort.boolean())
    active = model.declare('active', n.HirSort.boolean()); true = literal('boolean', 'true')
    instances = [p.HirPreferenceInstance('outer', 'whole', true, n.operation('and', [a, b])),
                 p.HirPreferenceInstance('ground-a', 'each', true, a),
                 p.HirPreferenceInstance('ground-b', 'each', true, b),
                 p.HirPreferenceInstance('anonymous', '', true, a)]
    instances += [p.HirPreferenceInstance(f'occurrence-{i}', 'pre', active, b) for i in range(3)]
    counts = p.planning_preferences(model, instances, declared_names=['empty'])
    for name in ['whole', 'each', 'pre', 'empty']:
        model.constrain(n.operation('eq', [model.declare(name, n.HirSort.integer()), counts.violation_count(name)]))
    metric = p.planning_preference_metric(model, literal('real', '1/3'), counts, minimize=False)
    model.constrain(n.operation('eq', [model.declare('metric', n.HirSort.real()), metric]))
    za, zb, on = z3.Bools('a b active')
    exact(model, z3.And(z3.Int('whole') == z3.If(z3.And(za, zb), 0, 1),
                       z3.Int('each') == z3.If(za, 0, 1) + z3.If(zb, 0, 1),
                       z3.Int('pre') == z3.If(z3.And(on, z3.Not(zb)), 3, 0),
                       z3.Int('empty') == 0, z3.Real('metric') == z3.RealVal('1/3') - z3.If(za, 0, 1)))
    with pytest.raises(ValueError, match='unknown named preference'):
        counts.violation_count('undeclared')
    with pytest.raises(ValueError, match='duplicate'):
        p.planning_preferences(model, instances + [instances[0]])


@pytest.mark.parametrize('operation,expected', [('ALWAYS', False), ('SOMETIME', True)])
def test_continuous_observation_interior_is_not_sampled(operation, expected):
    model = n.HirModel()
    time = n.bound_variable('time', n.HirSort.real()); phase = n.bound_variable('phase', n.HirSort.integer())
    zero = literal('real', '0'); two = literal('real', '2'); izero = literal('integer', '0')
    domain = p.HirTrajectoryObservationDomain('time', 'phase',
        n.operation('and', [n.operation('le', [zero, time]), n.operation('le', [time, two]),
                            n.operation('eq', [phase, izero])]),
        p.HirTrajectoryPoint(zero, izero), p.HirTrajectoryPoint(two, izero))
    # True only at t=1; the endpoint observations both miss the witness.
    condition = n.planning_numeric_predicate(n.operation('eq', [time, literal('real', '1')]))
    encoded = p.planning_observed_trajectory(model, domain, getattr(p.TrajectoryOperator, operation), condition)
    out = encoded.to_model(model, hard=False)
    out.constrain(n.operation('eq', [out.declare('answer', n.HirSort.boolean()), encoded.satisfied]))
    exact(out, z3.Bool('answer') == expected)


@pytest.mark.parametrize('bad', ['empty', 'missing_bound', 'extra_second', 'wrong_time_sort', 'free_variable'])
def test_invalid_constructions_are_atomic(bad):
    model = n.HirModel(); true = literal('boolean', 'true'); zero = literal('real', '0')
    condition = n.planning_numeric_predicate(true)
    operation = p.TrajectoryOperator.ALWAYS
    samples = [p.HirTrajectorySample(true, zero, condition)]
    if bad == 'empty': samples = []
    if bad == 'missing_bound': operation = p.TrajectoryOperator.WITHIN
    if bad == 'extra_second': samples = [p.HirTrajectorySample(true, zero, condition, condition)]
    if bad == 'wrong_time_sort': samples = [p.HirTrajectorySample(true, literal('integer', '0'), condition)]
    if bad == 'free_variable': samples = [p.HirTrajectorySample(true, zero,
        n.planning_numeric_predicate(n.bound_variable('free', n.HirSort.boolean())))]
    before = model.translate().to_smt2()
    with pytest.raises(ValueError): p.planning_finite_trajectory(model, operation, samples)
    assert model.translate().to_smt2() == before
