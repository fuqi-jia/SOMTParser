"""Whole-relation oracles for capture-safe existential conjunct factoring."""
import time

import pytest
import z3

from tools.semantic_checks.directional_equivalence import check_equivalence
from tools.semantic_checks.existential_conjuncts import factor_existential_conjuncts


def equivalent(original, rewritten):
    solver = z3.Solver(ctx=original.ctx)
    solver.add(z3.Xor(original, rewritten))
    assert solver.check() == z3.unsat


def test_lifts_observable_bounds_but_preserves_integer_witness():
    h, x = z3.Ints("factor_h factor_x")
    original = z3.Exists(h, z3.And(x >= 16, x <= 120, 8 * h == x, h >= 1))
    result = factor_existential_conjuncts(original)
    assert result.lifted_conjuncts == 2
    assert result.rewritten_quantifiers == 1
    equivalent(original, result.formula)
    equivalent(result.formula, z3.And(x >= 16, x <= 120, x % 8 == 0))


def test_impossible_hidden_relation_is_not_discarded():
    h, x = z3.Ints("factor_impossible_h factor_impossible_x")
    original = z3.Exists(h, z3.And(x >= 0, h > 0, h < 0))
    result = factor_existential_conjuncts(original)
    assert result.lifted_conjuncts == 1
    equivalent(original, result.formula)
    equivalent(result.formula, z3.BoolVal(False))


def test_nested_quantifier_outer_reference_remains_bound():
    h, inner, x = z3.Ints("factor_outer factor_inner factor_observed")
    original = z3.Exists(h, z3.And(x >= 0, z3.ForAll(inner, inner + h == inner + x), h == 3))
    result = factor_existential_conjuncts(original)
    assert result.lifted_conjuncts == 1
    equivalent(original, result.formula)
    equivalent(result.formula, x == 3)


def test_same_spelled_inner_binding_does_not_capture_free_symbol():
    x, h = z3.Ints("factor_shadow_x factor_shadow_h")
    inner = z3.ForAll(x, x + h >= x)
    original = z3.Exists(h, z3.And(x == 5, inner, h == 2))
    result = factor_existential_conjuncts(original)
    assert result.lifted_conjuncts == 1
    equivalent(original, result.formula)
    equivalent(result.formula, x == 5)


def test_independent_nested_quantifier_may_be_lifted():
    h, inner, x = z3.Ints("factor_free_h factor_free_inner factor_free_x")
    original = z3.Exists(h, z3.And(z3.ForAll(inner, inner + x >= inner), h == 4))
    result = factor_existential_conjuncts(original)
    assert result.lifted_conjuncts == 1
    equivalent(original, result.formula)
    equivalent(result.formula, x >= 0)


def test_mixed_bool_int_binders_preserve_order():
    b = z3.Bool("factor_b")
    h, x = z3.Ints("factor_mixed_h factor_mixed_x")
    original = z3.Exists([b, h], z3.And(x <= 9, h == x, b == (h > 3), b))
    result = factor_existential_conjuncts(original)
    equivalent(original, result.formula)
    equivalent(result.formula, z3.And(x > 3, x <= 9))


def test_array_function_arguments_are_dependencies():
    h, x = z3.Ints("factor_index factor_array_x")
    array = z3.Array("factor_array", z3.IntSort(), z3.IntSort())
    fn = z3.Function("factor_function", z3.IntSort(), z3.IntSort())
    original = z3.Exists(h, z3.And(x == 0, h == 2, z3.Select(array, h) == fn(h)))
    result = factor_existential_conjuncts(original)
    assert result.lifted_conjuncts == 1
    equivalent(original, result.formula)
    equivalent(result.formula, z3.And(x == 0, array[2] == fn(2)))


@pytest.mark.parametrize("context", ["not", "or", "implies"])
def test_no_rewrite_under_nonconjunctive_context(context):
    h, x = z3.Ints("factor_context_h factor_context_x")
    q = z3.Exists(h, z3.And(x >= 0, h == x))
    original = {"not": z3.Not(q), "or": z3.Or(q, x == 2),
                "implies": z3.Implies(x == 2, q)}[context]
    result = factor_existential_conjuncts(original)
    assert result.formula is original and result.lifted_conjuncts == 0


def test_universal_quantifier_is_unchanged():
    h, x = z3.Ints("factor_forall_h factor_forall_x")
    original = z3.ForAll(h, z3.And(x >= 0, h >= x))
    assert factor_existential_conjuncts(original).formula is original


def test_solver_patterns_are_conservatively_unchanged():
    h, x = z3.Ints("factor_pattern_h factor_pattern_x")
    fn = z3.Function("factor_pattern_fn", z3.IntSort(), z3.IntSort())
    original = z3.Exists(h, z3.And(x >= 0, fn(h) == x), patterns=[fn(h)])
    assert factor_existential_conjuncts(original).formula is original


def test_expired_deadline_rolls_back_exact_input():
    h, x = z3.Ints("factor_expired_h factor_expired_x")
    original = z3.Exists(h, z3.And(x >= 0, h == x))
    result = factor_existential_conjuncts(original, deadline=time.monotonic() - 1)
    assert result.formula is original and result.deadline_exhausted
    assert result.lifted_conjuncts == result.rewritten_quantifiers == 0


def test_shared_subexpression_dependency_and_custom_context():
    ctx = z3.Context()
    h, x = z3.Ints("factor_shared_h factor_shared_x", ctx=ctx)
    shared = h + x
    for _ in range(30):
        shared = shared + shared
    original = z3.Exists(h, z3.And(x == 3, shared == 0))
    result = factor_existential_conjuncts(original)
    assert result.lifted_conjuncts == 1 and result.formula.ctx == ctx
    equivalent(original, result.formula)
    equivalent(result.formula, x == 3)


def test_nonboolean_input_is_rejected():
    with pytest.raises(TypeError):
        factor_existential_conjuncts(z3.IntVal(3))


def test_checker_reports_real_observable_domain_counterexample():
    h, x = z3.Ints("factor_checker_h factor_checker_x")
    reference = z3.Exists(h, z3.And(x >= 16, x <= 120, 8 * h == x))
    candidate = z3.And(x > 0, x % 8 == 0)
    result = check_equivalence(reference, candidate,
                               total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.status == "counterexample"
    assert result.existential_conjuncts_lifted == 2
    assert result.right_implies_left.counterexample_conjunct is not None


def test_checker_retains_objective_offset_difference():
    h, x, cost = z3.Ints("factor_cost_h factor_cost_x factor_cost")
    reference = z3.Exists(h, z3.And(x >= 0, h == x + 1, cost == h))
    candidate = z3.And(x >= 0, cost == x)
    result = check_equivalence(reference, candidate,
                               total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.status == "counterexample"


def test_simplify_false_keeps_existing_checker_protocol():
    h, x = z3.Ints("factor_disabled_h factor_disabled_x")
    original = z3.Exists(h, z3.And(x >= 0, h == x))
    result = check_equivalence(original, original, simplify=False,
                               total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.status == "equivalent" and result.existential_conjuncts_lifted == 0
