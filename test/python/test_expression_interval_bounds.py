import pytest
import z3

from tools.semantic_checks.expression_interval_bounds import remove_entailed_expression_bounds


def checked(formula, removed=None):
    audit = []
    result = remove_entailed_expression_bounds(formula, audit.append)
    solver = z3.Solver(ctx=formula.ctx)
    solver.add(formula != result.formula)
    assert solver.check() == z3.unsat
    if removed is not None:
        assert result.removed_bounds == removed
    assert len(audit) == result.removed_bounds
    assert all(r['asserted_inequalities_used'] == 0 for r in audit)
    return result


@pytest.mark.parametrize('name', ['sum', 'sub', 'product', 'negative', 'division', 'modulo'])
def test_finite_expression_both_endpoints(name):
    a, b = z3.Bools('a b')
    x, y = z3.If(a, -7, 9), z3.If(b, -3, 4)
    term, low, high = {
        'sum': (x+y, -10, 13), 'sub': (x-y, -11, 12),
        'product': (x*y, -28, 36), 'negative': (-x, -9, 7),
        'division': (x/3, -3, 3), 'modulo': (z3.Int('unbounded') % 5, 0, 4)
    }[name]
    checked(z3.And(term >= low, term <= high), 2)


@pytest.mark.parametrize('which', ['le', 'lt', 'ge', 'gt', 'not-le', 'not-lt', 'not-ge', 'not-gt'])
def test_strict_reversed_and_negated_bound(which):
    t = z3.If(z3.Bool('condition'), -8, 13)
    bound = {'le': t <= 13, 'lt': t < 14, 'ge': t >= -8, 'gt': t > -9,
             'not-le': z3.Not(14 <= t), 'not-lt': z3.Not(13 < t),
             'not-ge': z3.Not(-9 >= t), 'not-gt': z3.Not(-8 > t)}[which]
    checked(bound, 1)


@pytest.mark.parametrize('bound', ['lower', 'upper'])
def test_wrong_bound_is_retained(bound):
    t = z3.If(z3.Bool('condition'), -8, 13)
    checked(t >= -7 if bound == 'lower' else t <= 12, 0)


def test_bounds_cannot_justify_themselves():
    x = z3.Int('x')
    checked(z3.And(x >= 0, x <= 3), 0)


def test_full_objective_definition_is_retained():
    objective = z3.Int('objective')
    t = 7*z3.If(z3.Bool('a'), -3, 11) + z3.If(z3.Bool('b'), -8, 15)
    definition = objective + -1*t == 0
    r = checked(z3.And(definition, objective >= -29, objective <= 92), 2)
    assert r.inferred_coordinates == 1
    assert any(c.eq(definition) for c in r.formula.children())


def test_multiple_definition_passes_are_well_founded():
    x, y, z = z3.Ints('x y z')
    formula = z3.And(z == y+3, y == x-2, x == z3.If(z3.Bool('b'), -5, 7), z >= -4, z <= 8)
    r = checked(formula, 2)
    assert r.inferred_coordinates == 3


def test_definition_cycle_does_not_invent_range():
    x, y = z3.Ints('x y')
    r = checked(z3.And(x == y+1, y == x-1, x >= 0), 0)
    assert r.inferred_coordinates == 0


def test_repeated_coordinate_coefficient_does_not_fake_unit_definition():
    x = z3.Int('x')
    checked(z3.And(x+x == 4, x <= 1), 0)


def test_self_referential_condition_still_has_unconditional_branch_range():
    x = z3.Int('x')
    checked(z3.And(x == z3.If(x > 0, 2, -4), x >= -4, x <= 2), 2)


def test_conditional_definition_cannot_supply_coordinate_range():
    x = z3.Int('x')
    checked(z3.And(z3.Implies(z3.Bool('a'), x == 3), x <= 4), 0)


def test_unbounded_ite_branch_is_not_assumed_unreachable():
    x = z3.Int('x')
    checked(z3.If(z3.Bool('a'), 1, x) <= 2, 0)


def test_definition_under_disjunction_is_not_extracted():
    x = z3.Int('x')
    checked(z3.And(z3.Or(x == 3, z3.Bool('a')), x <= 4), 0)


def test_real_and_bitvector_bounds_are_retained():
    a = z3.Bool('a')
    checked(z3.And(z3.If(a, z3.RealVal('1/2'), z3.RealVal('3/2')) <= 2,
                   z3.UGE(z3.If(a, z3.BitVecVal(1, 8), z3.BitVecVal(255, 8)), 1)), 0)


@pytest.mark.parametrize('divisor', [0, -3])
def test_unsupported_divisor_is_retained(divisor):
    x = z3.If(z3.Bool('a'), -7, 8)
    checked(x/divisor <= 99, 0)


def test_no_bound_is_removed_inside_quantifier():
    x = z3.Int('x')
    checked(z3.ForAll([x], z3.If(x > 0, 2, 3) <= 3), 0)


def test_quantified_condition_does_not_affect_constant_branch_bounds():
    x = z3.Int('x')
    checked(z3.If(z3.Exists([x], x > 0), -7, 9) <= 9, 1)


def test_nonlinear_definition_preserves_numeral_factors():
    a, b = z3.Bools('a b')
    x = z3.Int('x')
    t = 3*z3.If(a, -2, 4)*z3.If(b, -7, 3)
    checked(z3.And(x == t, x >= -84, x <= 42), 2)


def test_huge_integer_bounds_use_exact_arithmetic():
    n = 10**100
    t = z3.If(z3.Bool('a'), -n, n+1)
    checked(z3.And(t >= -n, t <= n+1, t < n+1), 2)


def test_custom_context_and_empty_conjunction():
    ctx = z3.Context()
    t = z3.If(z3.Bool('a', ctx=ctx), z3.IntVal(-4, ctx=ctx), z3.IntVal(7, ctx=ctx))
    checked(t <= 7, 1)
    checked(z3.BoolVal(True, ctx=ctx), 0)


def test_repeated_calls_do_not_share_ranges():
    x = z3.Int('x')
    checked(z3.And(x == 1, x <= 1), 1)
    checked(x <= 1, 0)


def test_large_shared_dag_is_processed_iteratively():
    t = z3.If(z3.Bool('b'), 0, 1)
    for _ in range(150):
        t = t+t
    result = checked(t <= 2**150, 1)
    assert result.visited_nodes < 500


def test_non_boolean_input_rejected():
    with pytest.raises(ValueError):
        remove_entailed_expression_bounds(z3.Int('x'))


def test_large_shared_definition_does_not_expand_paths():
    t = z3.If(z3.Bool('b'), 0, 1)
    for _ in range(150):
        t = t+t
    x = z3.Int('x')
    result = checked(z3.And(x == t, x <= 2**150), 1)
    assert result.inferred_coordinates == 1


def test_repeated_shared_conjunction_does_not_expand_paths():
    x = z3.Int('x')
    clause = z3.And(x == z3.If(z3.Bool('b'), -1, 7), x <= 7)
    for _ in range(150):
        clause = z3.And(clause, clause)
    result = checked(clause, 1)
    assert result.retained_definitions == 1
    assert result.visited_nodes < 50
