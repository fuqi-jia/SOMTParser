import pytest
import z3

from tools.semantic_checks.target_solve import decode_value, encode_value, solve_target


def target(body):
    return (body + '\n(check-sat)\n(get-model)\n(exit)\n').encode()


def integer(value):
    return dict(type='int', value=str(value))


def coordinate(name='x', **extra):
    return dict(id=name, symbol=name, **extra)


def test_sat_full_witness_and_wrong_source_assignment():
    data = target('(declare-const x Int) (declare-const y Int) '
                  '(assert (= x 5)) (assert (= y (+ x 2)))')
    projection = [coordinate('x'), coordinate('y')]
    result = solve_target(data, projection)
    assert result['status'] == result['target_witness_replay'] == 'sat'
    assert result['witness'] == {'x': integer(5), 'y': integer(7)}
    assert result['all_target_assertions_retained']
    assert result['target_assertions'] == 2
    assert result['equivalence_claimed'] is False
    for witness, expected in [(result['witness'], 'sat'),
                              ({'x': integer(5), 'y': integer(8)}, 'unsat')]:
        replay = solve_target(data, projection, fixed_values=witness, fixed_objectives=[])
        assert replay['status'] == expected


def test_unsat_including_late_constraint():
    result = solve_target(target('(declare-const x Int) (assert (> x 3)) '
                                 '(assert (< x 2))'), [coordinate()])
    assert result['status'] == 'unsat'
    assert 'witness' not in result


@pytest.mark.parametrize('direction,expected', [('minimize', 2), ('maximize', 8)])
def test_optimal_direction_and_wrong_cost(direction, expected):
    data = target('(declare-const x Int) (assert (and (<= 2 x) (<= x 8))) '
                  '(' + direction + ' x)')
    result = solve_target(data, [coordinate()])
    assert result['optimal'] and result['target_witness_replay'] == 'sat'
    assert result['witness'] == {'x': integer(expected)}
    assert result['original_objective_values'] == [integer(expected)]
    assert result['signed_objective_values'] == [integer(expected if direction == 'minimize' else -expected)]
    for cost, status in [(expected, 'sat'), (expected + 1, 'unsat')]:
        replay = solve_target(data, [coordinate()], fixed_values=result['witness'],
                              fixed_objectives=[integer(cost)])
        assert replay['status'] == status


def test_all_lex_objectives_and_signed_order():
    data = target('(set-option :opt.priority lex) '
                  '(declare-const x Int) (declare-const y Int) '
                  '(assert (and (>= x 0) (>= y 0) (<= (+ x y) 4))) '
                  '(maximize x) (minimize y)')
    result = solve_target(data, [coordinate('x'), coordinate('y')])
    assert result['optimal']
    assert result['original_objective_values'] == [integer(4), integer(0)]
    assert result['signed_objective_values'] == [integer(-4), integer(0)]
    replay = solve_target(data, [coordinate('x'), coordinate('y')],
                          fixed_values=result['witness'], fixed_objectives=[integer(0), integer(4)])
    assert replay['status'] == 'unsat'


@pytest.mark.parametrize('body', [
    '(declare-const x Int) (minimize x)',
    '(declare-const x Real) (assert (> x 0)) (minimize x)',
])
def test_unbounded_or_unattained_is_not_optimal(body):
    result = solve_target(target(body), [coordinate()])
    assert result['status'] == 'sat'
    assert result['optimal'] is False


def test_rational_value_is_exact():
    data = target('(declare-const x Real) (assert (= (* 3 x) 1)) (minimize x)')
    result = solve_target(data, [coordinate()])
    value = dict(type='real', numerator='1', denominator='3')
    assert result['witness'] == {'x': value}
    assert result['optimal'] and result['original_objective_values'] == [value]


def test_source_array_indices_are_not_guessed():
    data = target('(declare-const a (Array Int Int)) '
                  '(assert (= (select a (- 3)) 11)) (assert (= (select a 9) 17))')
    projection = [dict(id='a[-3]', symbol='a', indices=[-3]),
                  dict(id='a[9]', symbol='a', indices=[9])]
    result = solve_target(data, projection)
    assert result['witness'] == {'a[-3]': integer(11), 'a[9]': integer(17)}
    wrong = dict(result['witness']); wrong['a[-3]'] = integer(17)
    assert solve_target(data, projection, fixed_values=wrong, fixed_objectives=[])['status'] == 'unsat'


def test_finite_sets_include_outermost_deletions_and_whole_set_equality():
    data = target('(declare-const s (Array Int Bool)) '
                  '(assert (= s (store (store ((as const (Array Int Bool)) false) 3 true) 9 true)))')
    result = solve_target(data, [coordinate('s')])
    assert result['witness']['s'] == dict(type='set-int', elements=['3', '9'])
    bad = {'s': dict(type='set-int', elements=['3'])}
    assert solve_target(data, [coordinate('s')], fixed_values=bad, fixed_objectives=[])['status'] == 'unsat'
    value = z3.Store(z3.Store(z3.K(z3.IntSort(), z3.BoolVal(False)), 3, True), 3, False)
    assert encode_value(value) == dict(type='set-int', elements=[])


def test_boolean_and_quoted_symbols():
    data = target('(declare-const |flag x| Bool) (assert |flag x|)')
    result = solve_target(data, [coordinate('flag x')])
    assert result['witness'] == {'flag x': dict(type='bool', value=True)}


@pytest.mark.parametrize('projection,fixed', [
    ([coordinate()], {}),
    ([coordinate()], {'x': integer(1), 'extra': integer(2)}),
    ([coordinate(), coordinate()], {'x': integer(1)}),
    ([coordinate('missing')], {'missing': integer(1)}),
    ([coordinate(indices=[0])], {'x': integer(1)}),
])
def test_incomplete_or_ambiguous_mapping_refused(projection, fixed):
    with pytest.raises(ValueError):
        solve_target(target('(declare-const x Int)'), projection,
                     fixed_values=fixed, fixed_objectives=[])


@pytest.mark.parametrize('record', [
    dict(type='int', value=True), dict(type='int', value='01'),
    dict(type='int', value='1)', extra=1), dict(type='bool', value=True),
])
def test_invalid_typed_value_refused(record):
    with pytest.raises(ValueError):
        decode_value(record, z3.IntSort())


@pytest.mark.parametrize('cost', [None, [], [integer(1), integer(2)]])
def test_optimization_witness_requires_complete_costs(cost):
    with pytest.raises(ValueError):
        solve_target(target('(declare-const x Int) (minimize x)'), [coordinate()],
                     fixed_values={'x': integer(1)}, fixed_objectives=cost)


def test_infinite_sets_refused_and_custom_context_roundtrip():
    with pytest.raises(ValueError):
        encode_value(z3.K(z3.IntSort(), z3.BoolVal(True)))
    context = z3.Context()
    sort = z3.ArraySort(z3.IntSort(ctx=context), z3.BoolSort(ctx=context))
    record = dict(type='set-int', elements=['-7', '10'])
    assert encode_value(decode_value(record, sort)) == record


def test_unsupported_semantic_options_cannot_be_silently_ignored():
    with pytest.raises(ValueError):
        solve_target(target('(set-option :opt.priority pareto) (declare-const x Int)'), [coordinate()])


def test_source_coordinate_metadata_retained_with_flattened_target_index():
    data = target('(declare-const a (Array Int Int)) (assert (= (select a 0) 19))')
    projection = [dict(id='a[-2,7]', symbol='a', indices=[0], source_name='a', source_indices=[-2, 7])]
    result = solve_target(data, projection)
    assert result['witness'] == {'a[-2,7]': integer(19)}
    assert result['projection'] == projection
    replay = solve_target(data, projection, fixed_values=result['witness'], fixed_objectives=[])
    assert replay['status'] == 'sat'


def test_invalid_source_coordinate_metadata_is_rejected():
    data = target('(declare-const x Int)')
    with pytest.raises(ValueError):
        solve_target(data, [dict(id='x', symbol='x', source_name='y')])
    with pytest.raises(ValueError):
        solve_target(data, [dict(id='x', symbol='x', source_indices=[True])])
