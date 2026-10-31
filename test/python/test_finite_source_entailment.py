"""Exact complete-tuple enumeration, with conservative fragment refusals."""
import time

import pytest
import z3

from tools.semantic_checks.finite_source_entailment import prove_finite_source_entailment
from tools.semantic_checks.directional_equivalence import check_equivalence


def test_finite_source_is_proved_only_after_exhaustion():
    x, h = z3.Ints("finite_entail_x finite_entail_h")
    result = prove_finite_source_entailment(
        z3.Or(x == 2, x == 4), z3.Exists(h, 2 * h == x))
    assert result.status == "proved" and result.checked_models == 2


def test_target_unsat_returns_real_source_counterexample():
    x, h = z3.Ints("finite_counter_x finite_counter_h")
    result = prove_finite_source_entailment(x == 3, z3.Exists(h, 2 * h == x))
    assert result.status == "counterexample" and result.checked_models == 0
    assert result.counterexample_values and "3" in result.counterexample_model


def test_same_witness_need_not_work_for_different_observations():
    x, h = z3.Ints("finite_choice_x finite_choice_h")
    result = prove_finite_source_entailment(
        z3.Or(x == 1, x == 5), z3.Exists(h, z3.And(h == x + 1, h > 0)))
    assert result.status == "proved" and result.checked_models == 2


def test_partial_source_model_does_not_invent_target_coordinate():
    x, y, h = z3.Ints("finite_partial_x finite_partial_y finite_partial_h")
    result = prove_finite_source_entailment(x == 1, z3.Exists(h, z3.And(h == x, y >= 0)))
    assert result.status == "unknown" and "omits" in result.reason


def test_unbounded_source_is_not_truncated_into_a_proof():
    x, h = z3.Ints("finite_unbounded_x finite_unbounded_h")
    result = prove_finite_source_entailment(x >= 0, z3.Exists(h, h == x), max_models=3)
    assert result.status == "unknown" and result.checked_models == 3
    assert result.reason == "source enumeration not exhausted"


def test_exact_limit_allows_final_exhaustion_check():
    x, h = z3.Ints("finite_limit_x finite_limit_h")
    result = prove_finite_source_entailment(z3.Or(x == 0, x == 1), z3.Exists(h, h == x), max_models=2)
    assert result.status == "proved" and result.checked_models == 2


def test_false_source_needs_no_witness():
    h = z3.Int("finite_empty_h")
    result = prove_finite_source_entailment(z3.BoolVal(False), z3.Exists(h, h != h))
    assert result.status == "proved" and result.checked_models == 0


def test_closed_false_target_is_a_counterexample():
    h = z3.Int("finite_closed_h")
    result = prove_finite_source_entailment(z3.BoolVal(True), z3.ForAll(h, h == 0))
    assert result.status == "counterexample"


def test_bool_coordinate_and_private_bool_witness():
    p, b = z3.Bools("finite_bool_p finite_bool_b")
    result = prove_finite_source_entailment(p, z3.Exists(b, z3.And(b == p, b)))
    assert result.status == "proved" and result.checked_models == 1


def test_nested_shadowed_binders_remain_closed():
    x, h, k = z3.Ints("finite_nested_x finite_nested_h finite_nested_k")
    target = z3.Exists(h, z3.And(h == x, z3.ForAll(k, k + h >= k)))
    result = prove_finite_source_entailment(z3.Or(x == 0, x == 1), target)
    assert result.status == "proved" and result.checked_models == 2


def test_array_interpretation_is_not_assumed_fixed():
    x = z3.Int("finite_array_x")
    a = z3.Array("finite_array", z3.IntSort(), z3.IntSort())
    result = prove_finite_source_entailment(x == 0, a[x] == 3)
    assert result.status == "unknown"


def test_free_function_interpretation_is_not_assumed_fixed():
    x = z3.Int("finite_uf_x")
    f = z3.Function("finite_uf", z3.IntSort(), z3.IntSort())
    result = prove_finite_source_entailment(x == 0, f(x) == 3)
    assert result.status == "unknown" and "function interpretation" in result.reason


@pytest.mark.parametrize("operator", ["div", "mod"])
def test_zero_division_underspecification_is_rejected(operator):
    x = z3.Int("finite_divzero_x")
    expression = x / 0 if operator == "div" else x % 0
    result = prove_finite_source_entailment(x == 1, expression == 3)
    assert result.status == "unknown" and "nonzero" in result.reason


def test_constant_nonzero_modulo_is_defined():
    x, h = z3.Ints("finite_mod_x finite_mod_h")
    result = prove_finite_source_entailment(z3.Or(x == 2, x == 4), z3.Exists(h, z3.And(x % 2 == 0, h == x / 2)))
    assert result.status == "proved"


def test_nonlinear_and_noninteger_fragments_are_skipped():
    x, y = z3.Ints("finite_nonlinear_x finite_nonlinear_y")
    assert prove_finite_source_entailment(x == 1, x * y == 1).status == "unknown"
    real = z3.Real("finite_real")
    assert prove_finite_source_entailment(real == 1, real > 0).status == "unknown"


def test_free_de_bruijn_variable_is_not_a_closed_sentence():
    result = prove_finite_source_entailment(z3.BoolVal(True), z3.Var(0, z3.IntSort()) == 1)
    assert result.status == "unknown" and "unbound" in result.reason


def test_expired_deadline_is_unknown():
    x = z3.Int("finite_deadline_x")
    result = prove_finite_source_entailment(x == 1, x == 1, deadline=time.monotonic() - 1)
    assert result.status == "unknown" and result.checked_models == 0


def test_custom_context_and_multiple_coordinates():
    ctx = z3.Context()
    x, y, h = z3.Ints("finite_context_x finite_context_y finite_context_h", ctx=ctx)
    source = z3.Or(z3.And(x == 1, y == 2), z3.And(x == 3, y == 4))
    result = prove_finite_source_entailment(source, z3.Exists(h, z3.And(y == x + 1, h == x + y)))
    assert result.status == "proved" and result.checked_models == 2


def test_invalid_strategy_limit_is_rejected():
    for limit in (0, -1, True, 1.5):
        with pytest.raises(ValueError):
            prove_finite_source_entailment(z3.BoolVal(True), z3.BoolVal(True), max_models=limit)


def force_first_solver_unknown(monkeypatch):
    """Only the primary solver is forced unknown; all fallback checks are real."""
    original = z3.Solver
    constructed = 0

    class FirstUnknown:
        def __init__(self, solver):
            self.solver = solver
            self.first = True

        def __getattr__(self, name):
            return getattr(self.solver, name)

        def check(self):
            if self.first:
                self.first = False
                return z3.unknown
            return self.solver.check()

        def reason_unknown(self):
            return "test primary incomplete quantifiers"

    def create(*args, **kwargs):
        nonlocal constructed
        constructed += 1
        solver = original(*args, **kwargs)
        return FirstUnknown(solver) if constructed == 1 else solver

    monkeypatch.setattr(z3, "Solver", create)


def test_checker_accepts_only_complete_fallback_proof(monkeypatch):
    x, h = z3.Ints("finite_integration_x finite_integration_h")
    source = z3.Or(x == 2, x == 4)
    target = z3.Exists(h, z3.And(2 * h == x, h >= 1, h <= 2))
    force_first_solver_unknown(monkeypatch)
    result = check_equivalence(source, target, simplify=False,
                               total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.status == "equivalent"
    proof, = result.left_implies_right.finite_source_checks
    assert proof["status"] == "proved" and proof["checked_models"] == 2


def test_checker_preserves_fallback_counterexample(monkeypatch):
    x, h = z3.Ints("finite_integration_bad_x finite_integration_bad_h")
    force_first_solver_unknown(monkeypatch)
    result = check_equivalence(x == 3, z3.Exists(h, 2 * h == x), simplify=False,
                               total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.status == "counterexample"
    proof, = result.left_implies_right.finite_source_checks
    assert proof["status"] == "counterexample"
    assert result.left_implies_right.counterexample_values
