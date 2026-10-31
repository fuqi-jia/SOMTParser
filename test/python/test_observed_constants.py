"""Complete relation controls for eliminating observed private constants."""
import pytest
import z3

from tools.semantic_checks.observed_constants import project_observed_constants


def close(variables, body):
    return z3.Exists(variables, body) if variables else body


def equivalent(left, right):
    goal = z3.Goal()
    goal.add(z3.Xor(left, right))
    reduced = z3.Then('simplify', 'qe-light', 'simplify')(goal).as_expr()
    solver = z3.Solver()
    solver.add(reduced)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('sort', [z3.IntSort(), z3.BoolSort(), z3.RealSort(), z3.BitVecSort(8)])
def test_public_observation_preserves_each_scalar_relation(sort):
    x, p, q = z3.Consts('private public alternative', sort)
    body = z3.And(p == x, x != q)
    result = project_observed_constants(body, [x], [p, q])
    assert not result.private_variables
    equivalent(close([x], body), result.body)
    equivalent(result.body, p != q)


def test_all_aliases_and_nonlinear_signed_cost_stay_constrained():
    x, y, p, q, alias, cost = z3.Ints('x y p q alias cost')
    body = z3.And(x == p, x == alias, q == y, x >= 0, y >= 0, cost == -x*y)
    result = project_observed_constants(body, [x, y], [p, q, alias])
    assert not result.private_variables
    expected = z3.And(alias == p, p >= 0, q >= 0, cost == -p*q)
    equivalent(close([x, y], body), result.body)
    equivalent(result.body, expected)
    solver = z3.Solver()
    solver.add(result.body, p == 2, q == 3, alias == 5)
    assert solver.check() == z3.unsat


def test_unobserved_private_coordinates_and_their_constraints_remain():
    x, y, p = z3.Ints('x y p')
    body = z3.And(z3.And(x == p, x >= 0), y > x, y < 3)
    result = project_observed_constants(body, [x, y], [p])
    assert len(result.private_variables) == 1 and result.private_variables[0].eq(y)
    equivalent(close([x, y], body), close(result.private_variables, result.body))
    equivalent(close(result.private_variables, result.body), z3.And(p >= 0, p <= 1))


@pytest.mark.parametrize('connective', ['or', 'not', 'implies', 'ite', 'quantifier'])
def test_conditional_or_quantified_bridges_are_never_used(connective):
    x, p, i = z3.Ints('x p i')
    guard = z3.Bool('guard')
    bridge = x == p
    body = {
        'or': z3.Or(bridge, guard),
        'not': z3.Not(bridge),
        'implies': z3.Implies(guard, bridge),
        'ite': z3.If(guard, bridge, z3.BoolVal(True)),
        'quantifier': z3.Exists([i], z3.And(i == x, i == p)),
    }[connective]
    result = project_observed_constants(body, [x], [p])
    assert not result.substitutions and result.body.eq(body)
    assert len(result.private_variables) == 1


def test_substitution_is_capture_avoiding_under_other_quantifiers():
    x, p, i = z3.Ints('x p i')
    body = z3.And(x == p, z3.ForAll([i], z3.Implies(i >= 0, i+x >= p)))
    result = project_observed_constants(body, [x], [p])
    equivalent(close([x], body), result.body)
    equivalent(result.body, z3.BoolVal(True))


def test_numeric_coercion_is_not_a_direct_constant_binding():
    x, p = z3.Int('x'), z3.Real('p')
    body = x == p
    result = project_observed_constants(body, [x], [p])
    assert not result.substitutions and result.body.eq(body)
    solver = z3.Solver()
    solver.add(close(result.private_variables, result.body), p == z3.RealVal('1/2'))
    assert solver.check() == z3.unsat


def test_array_observations_remain_for_the_array_projection():
    x, p = [z3.Array(n, z3.IntSort(), z3.IntSort()) for n in ['x', 'p']]
    body = x == p
    result = project_observed_constants(body, [x], [p])
    assert not result.substitutions and result.body.eq(body)


@pytest.mark.parametrize('problem', ['overlap', 'private-duplicate', 'public-duplicate', 'expression'])
def test_invalid_coordinate_contract_is_rejected(problem):
    x, p = z3.Ints('x p')
    private, public = [x], [p]
    if problem == 'overlap':
        public = [x]
    elif problem == 'private-duplicate':
        private = [x, x]
    elif problem == 'public-duplicate':
        public = [p, p]
    else:
        private = [x+1]
    with pytest.raises(ValueError):
        project_observed_constants(x == p, private, public)
