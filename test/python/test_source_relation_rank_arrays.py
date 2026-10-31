"""End-to-end observation and signed-cost checks for a complete circuit witness."""
import pytest
import z3
from tools.semantic_checks.source_oracles.fzn_json_source import Source
from tools.semantic_checks.source_oracles.target_relation import compare


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
@pytest.mark.parametrize('wrong_cost', [False, True])
def test_native_rank_array_against_complete_source_cycles(direction, wrong_cost):
    xs = z3.Ints('x0 x1 x2')
    source_relation = z3.Or(z3.And(xs[0] == 2, xs[1] == 3, xs[2] == 1),
                            z3.And(xs[0] == 3, xs[1] == 1, xs[2] == 2))
    objective = xs[0] + 2 * xs[1] + 3 * xs[2]
    source = Source({str(x): x for x in xs}, {}, [source_relation],
                    objective, direction, ())
    observations = [dict(name=str(x), value=x, indices=None, dimensions=[]) for x in xs]
    rank = z3.Array('private_rank', z3.IntSort(), z3.IntSort())
    parts = [z3.Distinct(*xs), rank[1] == 0]
    for i, x in enumerate(xs, 1):
        parts.extend([x >= 1, x < 4, x != i, rank[i] >= 0, rank[i] < 3,
                      z3.Or(x == 1, rank[x] == rank[i] + 1)])
    native_relation = z3.Exists(rank, z3.And(*parts))
    native_cost = objective + 1 if wrong_cost else objective
    target = ('\n'.join([*(f'(declare-const {x} Int)' for x in xs),
                          f'(assert {native_relation.sexpr()})',
                          f'({direction} {native_cost.sexpr()})',
                          '(check-sat)', '(exit)'])).encode()
    result = compare(source, observations, target, solve=True)
    assert result['circuit_rank_normalization']['target'] == 1
    assert result['all_source_constraints_retained'] and result['all_target_assertions_retained']
    if wrong_cost:
        assert not result['equivalent'] and result['solver_answer'] == 'sat', result
    else:
        assert result['equivalent'], result
