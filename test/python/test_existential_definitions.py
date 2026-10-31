"""Full-relation checks for explicit existential witness substitution."""
import pytest
import z3
from tools.semantic_checks.existential_definitions import eliminate_existential_definitions


def check(formula, expected=None):
    result = eliminate_existential_definitions(formula)
    solver = z3.Solver()
    solver.add(z3.Xor(formula, result.formula))
    assert solver.check() == z3.unsat
    if expected is not None:
        solver = z3.Solver()
        solver.add(z3.Xor(expected, result.formula))
        assert solver.check() == z3.unsat
    return result


@pytest.mark.parametrize('reverse', [False, True])
def test_negative_boolean_equality_with_unbounded_arithmetic(reverse):
    b = z3.Bool('b')
    x, y = z3.Ints('x y')
    predicate = x + y == 0
    definition = z3.Not(predicate == b if reverse else b == predicate)
    result = check(z3.Exists([b], z3.And(definition, z3.Or(b, x > 7))),
                   z3.Or(z3.Not(predicate), x > 7))
    assert result.direct_definitions == 1 and not z3.is_quantifier(result.formula)


@pytest.mark.parametrize('negative', [False, True])
def test_literal_boolean_definition(negative):
    b, p = z3.Bools('b p')
    literal = z3.Not(b) if negative else b
    check(z3.Exists([b], z3.And(literal, b == p)), z3.Not(p) if negative else p)


@pytest.mark.parametrize('sort', [z3.IntSort(), z3.RealSort()])
@pytest.mark.parametrize('implications', [False, True])
def test_complementary_guards_preserve_all_bounds_and_signed_cost(sort, implications):
    x, v, cost = [z3.Const(name, sort) for name in ('x', 'v', 'cost')]
    p = z3.Bool('p')
    first, second = (1 == v - x), (v == 0)
    if implications:
        arms = [z3.Implies(p, z3.And(first, v != 0)), z3.Implies(z3.Not(p), second)]
    else:
        arms = [z3.Or(z3.Not(p), z3.And(first, v != 0)), z3.Or(p, second)]
    body = z3.And(*arms, v >= -4, v <= 12, cost == -2 * v + x)
    expected = z3.substitute(body, (v, z3.If(p, x + 1, 0)))
    result = check(z3.Exists([v], body), expected)
    assert result.conditional_definitions == 1 and not z3.is_quantifier(result.formula)
    wrong = z3.substitute(expected, (cost, cost + 1))
    solver = z3.Solver(); solver.add(z3.Xor(result.formula, wrong))
    assert solver.check() == z3.sat


def test_reified_zero_sentinel_eliminates_boolean_then_integer():
    b, p = z3.Bools('b p')
    v, x, cost = z3.Ints('v x cost')
    body = z3.And(z3.Not((v == 0) == b),
                  z3.Or(z3.Not(p), z3.And(b, 1 == v - x)),
                  z3.Or(p, z3.Not(b)), v <= 100, cost == v * x)
    expected = z3.substitute(body, (v, z3.If(p, x + 1, 0)),
                             (b, z3.If(p, x + 1, 0) != 0))
    result = check(z3.Exists([b, v], body), expected)
    assert result.direct_definitions == 1 and result.conditional_definitions == 1
    assert not z3.is_quantifier(result.formula)


def test_partial_guards_never_invent_an_else_value():
    v, x = z3.Ints('v x'); p, q = z3.Bools('p q')
    for body in [z3.Implies(p, v == x),
                 z3.And(z3.Implies(p, v == x), z3.Implies(q, v == 0)),
                 z3.Or(p, v == x, v == 0)]:
        formula = z3.Exists([v], body)
        result = eliminate_existential_definitions(formula)
        assert result.formula.eq(formula)
        assert result.direct_definitions == result.conditional_definitions == 0


def test_nonunit_integer_coefficients_and_nonlinear_occurrences_remain():
    v, x = z3.Ints('v x'); p = z3.Bool('p')
    for atom in (2 * v == x, v * v == x, z3.If(p, v, 0) == x):
        formula = z3.Exists([v], atom)
        result = eliminate_existential_definitions(formula)
        assert result.formula.eq(formula)


def test_conflicting_definitions_and_remaining_constraints_are_retained():
    v, x = z3.Ints('v x'); p = z3.Bool('p')
    body = z3.And(z3.Implies(p, v == x), z3.Implies(z3.Not(p), v == 0),
                  z3.Implies(p, v == x + 1))
    check(z3.Exists([v], body), z3.Not(p))
    check(z3.Exists([v], z3.And(v == x, v == x + 1)), z3.BoolVal(False))


def test_cyclic_definitions_and_guard_dependencies_stay_exact():
    a, b = z3.Bools('a b'); v, w, x = z3.Ints('v w x')
    check(z3.Exists([a, b], z3.And(a == z3.Not(b), b == z3.Not(a), a == (x > 0))))
    check(z3.Exists([v, w], z3.And(v == w + 1, w == v - 1, v > x)))
    formula = z3.Exists([v], z3.And(z3.Implies(v > 0, v == x),
                                  z3.Implies(v <= 0, v == 0)))
    assert eliminate_existential_definitions(formula).formula.eq(formula)


def test_nested_quantifier_and_same_display_names_do_not_capture():
    x, y = z3.Ints('x y'); b = z3.Bool('b')
    body = z3.And(z3.Not(b == (x == 0)), z3.ForAll([y], z3.Or(b, y == x)))
    check(z3.Exists([b], body), x != 0)
    outer = z3.Exists([x], z3.And(x == y, z3.Exists([y], y == x + 1)))
    check(outer, z3.BoolVal(True))


def test_nonexistential_root_is_unchanged():
    x, y = z3.Ints('x y')
    for formula in [x == y, z3.ForAll([x], x == y)]:
        assert eliminate_existential_definitions(formula).formula.eq(formula)
