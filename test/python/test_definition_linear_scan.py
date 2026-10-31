import pytest
import z3

from tools.semantic_checks.existential_definitions import eliminate_existential_definitions


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('sign', [-1, 1])
def test_shared_nonlinear_summands_keep_every_private_domain_and_signed_cost(sign):
    x, public, cost = z3.Ints('linear_x linear_public linear_cost')
    ys = z3.IntVector('linear_hidden', 12)
    shared = z3.Sum(*[z3.If(y >= 1, 3 * y * y, 7 - y) for y in ys])
    domains = [z3.And(y >= -2, y <= 4) for y in ys]
    body = z3.And(x + shared == public, *domains, x >= 0, cost == sign * (x + 9))
    original = z3.Exists([x, *ys], body)
    result = eliminate_existential_definitions(original)
    expected = z3.Exists(ys, z3.substitute(body, (x, public - shared)))
    assert result.direct_definitions == 1
    assert result.formula.num_vars() == len(ys)
    # Prove the stronger pointwise body identity under a common witness tuple.
    # It entails equality of the existential closures, while asking a general
    # quantified nonlinear solver to discover the same tuple is unnecessary.
    assert expected.num_vars() == result.formula.num_vars()
    witnesses = [z3.FreshConst(expected.var_sort(i)) for i in range(expected.num_vars())]
    equivalent(z3.substitute_vars(result.formula.body(), *reversed(witnesses)),
               z3.substitute_vars(expected.body(), *reversed(witnesses)))


@pytest.mark.parametrize('conditional', [False, True])
def test_unit_coefficient_does_not_hide_a_second_nonlinear_occurrence(conditional):
    v, public = z3.Ints('blocked_v blocked_public')
    flag = z3.Bool('blocked_flag')
    term = z3.If(flag, v, 0) if conditional else v * v
    original = z3.Exists(v, v + term == public)
    result = eliminate_existential_definitions(original)
    assert result.formula.eq(original)
    assert result.direct_definitions == result.conditional_definitions == 0


def test_fractional_summands_isolate_only_the_exact_unit_coefficient():
    x, y, public, cost = z3.Reals('fraction_x fraction_y fraction_public fraction_cost')
    body = z3.And(x / 2 + y == public, x >= -3, x <= 7, cost == -y)
    result = eliminate_existential_definitions(z3.Exists([x, y], body))
    expected = z3.Exists(x, z3.And(x >= -3, x <= 7, cost == -public + x / 2))
    assert result.direct_definitions == 1
    equivalent(result.formula, expected)


def test_unit_isolation_retains_conflicting_full_equation():
    x, y, public, cost = z3.Ints('conflicting_x conflicting_y conflicting_public conflicting_cost')
    nonlinear = z3.If(y > 0, y * y, -y)
    original = z3.Exists([x, y], z3.And(x + nonlinear == public,
                                         x + nonlinear == public + 1,
                                         cost == -x))
    result = eliminate_existential_definitions(original)
    equivalent(result.formula, z3.BoolVal(False))
