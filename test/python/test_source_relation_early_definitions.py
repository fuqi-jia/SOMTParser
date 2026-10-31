"""Complete signed-cost checks keep source side conditions after early elimination."""
import pytest
import z3
from tools.semantic_checks.source_oracles.fzn_json_source import Source
from tools.semantic_checks.source_oracles.target_relation import compare


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
@pytest.mark.parametrize('change', ['none', 'lost-side-condition', 'wrong-cost'])
def test_conditional_chain_keeps_full_feasibility_and_signed_cost(direction, change):
    x, flag = z3.Int('source_x'), z3.Bool('source_flag')
    hidden = [z3.Int(f'private_{i}') for i in range(40)]
    constraints = [x >= 0, x <= 3, hidden[-1] <= 40]
    for i, value in enumerate(hidden):
        constraints.extend([z3.Implies(flag, value == x + i),
                            z3.Implies(z3.Not(flag), value == x - i)])
    variables = dict(x=x, flag=flag, **{f'h{i}': v for i, v in enumerate(hidden)})
    source = Source(variables, {}, constraints, z3.Sum(*hidden), direction, ())
    observations = [dict(name=name, value=value, indices=None, dimensions=[])
                    for name, value in [('x', x), ('flag', flag)]]
    side = 'true' if change == 'lost-side-condition' else '(<= (+ x (ite flag 39 (- 39))) 40)'
    objective = '(+ (* 40 x) (ite flag 780 (- 780)))'
    if change == 'wrong-cost':
        objective = f'(+ {objective} 1)'
    target = (f'(declare-const x Int)\n(declare-const flag Bool)\n'
              f'(assert (and (<= 0 x) (<= x 3) {side}))\n'
              f'({direction} {objective})\n(check-sat)\n(exit)').encode()
    result = compare(source, observations, target, solve=True)
    assert result['all_source_constraints_retained'] and result['all_target_assertions_retained']
    early = result['existential_definitions']['source']['before_reduction']
    assert early['direct'] + early['conditional'] == len(hidden)
    if change == 'none':
        assert result['equivalent'], result
    else:
        assert not result['equivalent'] and result['solver_answer'] == 'sat', result
        assert result['counterexample'] is not None
