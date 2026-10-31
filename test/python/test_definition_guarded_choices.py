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
        solver.add(z3.Xor(result.formula, expected))
        assert solver.check() == z3.unsat
    return result


@pytest.mark.parametrize('sign', [-1, 1])
def test_argmax_strict_tie_break_keeps_bounds_and_signed_cost(sign):
    xs = z3.IntVector('choice_value', 3)
    v, cost = z3.Ints('chosen_index chosen_cost')
    arms = [z3.And(v == i, *(xs[i] > x if j < i else xs[i] >= x
                            for j, x in enumerate(xs) if i != j))
            for i in range(3)]
    body = z3.And(z3.Or(*arms), v >= 1, cost == sign * (7 * v + xs[0]))
    result = check(z3.Exists(v, body))
    assert result.conditional_definitions == 1
    assert not z3.is_quantifier(result.formula)


def test_overlapping_distinct_values_remain_existential():
    v, x, cost = z3.Ints('overlap_choice overlap_x overlap_cost')
    # At x=0 both values are feasible and the observed cost distinguishes them.
    body = z3.And(z3.Or(z3.And(v == 0, x <= 0), z3.And(v == 1, x >= 0)),
                  cost == v * v)
    formula = z3.Exists(v, body)
    result = check(formula)
    assert result.formula.eq(formula)
    assert result.conditional_definitions == 0


def test_missing_guard_case_preserves_infeasibility():
    v, x, cost = z3.Ints('partial_choice partial_x partial_cost')
    formula = z3.Exists(v, z3.And(
        z3.Or(z3.And(v == 4, x < 0), z3.And(v == 9, x > 0)), cost == v * v))
    # These guards are disjoint, but do not contain a literal complementary
    # pair. This sufficient structural rule may leave them uneliminated.
    result = check(formula)
    solver = z3.Solver(); solver.add(result.formula, x == 0)
    assert solver.check() == z3.unsat


def test_nonexhaustive_complementary_guards_keep_the_original_disjunction():
    v, x, cost = z3.Ints('guarded_choice guarded_x guarded_cost')
    a, b, p = z3.Bools('guarded_a guarded_b guarded_p')
    formula = z3.Exists(v, z3.And(z3.Or(z3.And(v == 2, p, a),
                                                        z3.And(v == 5, z3.Not(p), b)),
                                  cost == v * v + x))
    expected = z3.Or(z3.And(p, a, cost == 4 + x), z3.And(z3.Not(p), b, cost == 25 + x))
    result = check(formula, expected)
    assert result.conditional_definitions == 1


def test_same_value_overlapping_guards_are_safe():
    v, x = z3.Ints('same_choice same_x'); p, q = z3.Bools('same_p same_q')
    formula = z3.Exists(v, z3.And(z3.Or(z3.And(v == x, p), z3.And(v == x, q)), v < 3))
    result = check(formula, z3.And(z3.Or(p, q), x < 3))
    assert result.conditional_definitions == 1


def test_guard_depending_on_selected_witness_is_not_a_definition():
    v, x = z3.Ints('self_choice self_x')
    formula = z3.Exists(v, z3.Or(z3.And(v == 2, v > x), z3.And(v == 5, v <= x)))
    result = check(formula)
    assert result.formula.eq(formula)


def test_other_private_dependencies_and_nested_binders_remain_capture_safe():
    v, w, x, y = z3.Ints('outer_choice dependency_choice choice_x choice_y')
    p = z3.Bool('choice_guard')
    formula = z3.Exists([v, w], z3.And(
        z3.Or(z3.And(v == w + 1, p), z3.And(v == w - 1, z3.Not(p))),
        w == x, z3.ForAll(y, z3.Implies(y > v, y > x))))
    result = check(formula)
    assert result.direct_definitions == 1 and result.conditional_definitions == 1
