import pytest
import z3

from tools.semantic_checks.existential_definitions import eliminate_existential_definitions


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_long_shared_definition_chain_retains_all_relations():
    public, cost = z3.Ints('chain_public chain_cost')
    xs = [z3.Int(f'chain_x_{i}') for i in range(1200)]
    equations = [xs[0] == public]
    equations.extend(xs[i] == xs[i - 1] + 1 for i in range(1, len(xs)))
    body = z3.And(*equations, xs[-1] <= 1500, cost == -xs[-1])
    result = eliminate_existential_definitions(z3.Exists(xs, body))
    assert result.direct_definitions == len(xs)
    assert not z3.is_quantifier(result.formula)
    equivalent(result.formula, z3.And(public + 1199 <= 1500, cost == -(public + 1199)))


@pytest.mark.parametrize('sign', [-1, 1])
def test_nonlinear_shared_dependency_and_signed_cost(sign):
    p, q, x, y, cost = z3.Ints('p q x y signed_cost')
    original = z3.Exists([x, y], z3.And(x == p * q, y == x + 3, y <= 12, cost == sign * y))
    projected = eliminate_existential_definitions(original)
    expected = z3.And(p * q + 3 <= 12, cost == sign * (p * q + 3))
    equivalent(projected.formula, expected)
    equivalent(original, projected.formula)


def test_inconsistent_competing_definitions_remain_constraints():
    p, x, y = z3.Ints('conflict_p conflict_x conflict_y')
    original = z3.Exists([x, y], z3.And(x == p, y == x + 1, y == p + 2))
    result = eliminate_existential_definitions(original)
    equivalent(result.formula, z3.BoolVal(False))
    equivalent(original, result.formula)


def test_dependency_cycle_keeps_a_witness_until_exact_definition_available():
    p, x, y, cost = z3.Ints('cycle_p cycle_x cycle_y cycle_cost')
    original = z3.Exists([x, y], z3.And(x == y + 1, y == x - 1, x == p, cost == y))
    result = eliminate_existential_definitions(original)
    equivalent(result.formula, cost == p - 1)
    equivalent(original, result.formula)


def test_nested_binder_and_same_spelled_free_variable_are_capture_safe():
    p = z3.Int('capture_x')
    x = z3.Int('capture_witness')
    y = z3.Int('capture_inner')
    original = z3.Exists(x, z3.And(x == p, z3.ForAll(y, z3.Implies(y >= p, x <= y))))
    result = eliminate_existential_definitions(original)
    equivalent(result.formula, z3.BoolVal(True))
    equivalent(original, result.formula)


@pytest.mark.parametrize('negated', [False, True])
def test_definition_inside_nonconjunctive_context_is_not_assumed(negated):
    p, x, y = z3.Ints('context_p context_x context_y')
    choice = z3.Or(x == p, y == p + 1)
    body = z3.Not(choice) if negated else choice
    original = z3.Exists([x, y], body)
    result = eliminate_existential_definitions(original)
    assert result.formula.eq(original)
    assert result.direct_definitions == result.conditional_definitions == 0


def test_exact_real_unit_coefficient_and_public_cost():
    p, x, y, cost = z3.Reals('real_p real_x real_y real_cost')
    original = z3.Exists([x, y], z3.And(x + z3.RealVal('1/3') == p, y == x / 2, cost == -y))
    result = eliminate_existential_definitions(original)
    equivalent(result.formula, cost == -(p - z3.RealVal('1/3')) / 2)
    equivalent(original, result.formula)


def test_incompatible_boolean_definitions_are_retained():
    p, x, y = z3.Bools('bool_p bool_x bool_y')
    original = z3.Exists([x, y], z3.And(x == p, y == z3.Not(x), y == p))
    result = eliminate_existential_definitions(original)
    equivalent(result.formula, z3.BoolVal(False))
    equivalent(original, result.formula)


def test_many_independent_conditional_definitions_retain_every_branch():
    guard, public, cost = z3.Bool('many_guard'), z3.Int('many_public'), z3.Int('many_cost')
    xs = [z3.Int(f'branch_x_{i}') for i in range(180)]
    parts = []
    for i, x in enumerate(xs):
        parts.extend([z3.Implies(guard, x == public + i),
                      z3.Implies(z3.Not(guard), x == public - i)])
    original = z3.Exists(xs, z3.And(*parts, cost == z3.Sum(*xs)))
    result = eliminate_existential_definitions(original)
    assert result.direct_definitions + result.conditional_definitions == len(xs)
    delta = sum(range(len(xs)))
    equivalent(result.formula, cost == 180 * public + z3.If(guard, delta, -delta))


def test_conditional_dependencies_keep_guard_variable_in_scope():
    g, x, y = z3.Bools('branch_g branch_x branch_y')
    p = z3.Bool('branch_public')
    original = z3.Exists([x, y], z3.And(
        z3.Implies(g, x == p), z3.Implies(z3.Not(g), x == z3.Not(p)),
        z3.Implies(x, y), z3.Implies(z3.Not(x), z3.Not(y)), y))
    result = eliminate_existential_definitions(original)
    equivalent(original, result.formula)
    equivalent(result.formula, g == p)
