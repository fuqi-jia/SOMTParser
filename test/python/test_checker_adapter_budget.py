"""End-to-end projection and directional checking share one wall budget."""
import time

import pytest

z3 = pytest.importorskip("z3")

from tools.semantic_checks import checker_adapter
from tools.semantic_checks.checker_adapter import check_relation_equivalence


def _relations():
    ctx = z3.Context()
    reference_value = z3.Int("budget_reference_value", ctx=ctx)
    candidate_value = z3.Int("budget_candidate_value", ctx=ctx)
    observed = z3.Int("budget_observed", ctx=ctx)
    reference_cost = z3.Int("budget_reference_cost", ctx=ctx)
    candidate_cost = z3.Int("budget_candidate_cost", ctx=ctx)
    cost_alias = z3.Int("budget_cost", ctx=ctx)
    return {
        "reference_assertions": [reference_value == 7],
        "candidate_assertions": [candidate_value == 7],
        "reference_bridges": [(observed, reference_value)],
        "candidate_bridges": [(observed, candidate_value)],
        "reference_cost_bridge": (cost_alias, reference_cost),
        "candidate_cost_bridge": (cost_alias, candidate_cost),
    }


def test_preprocessing_elapsed_time_is_deducted_from_directional_budget(monkeypatch):
    original = checker_adapter.optimize_observation_projection
    budgets = []

    def delayed(body, bridges, *, guarded_bool_budget_ms):
        budgets.append(guarded_bool_budget_ms)
        time.sleep(0.02)
        return original(body, bridges,
                        guarded_bool_budget_ms=guarded_bool_budget_ms)

    monkeypatch.setattr(checker_adapter, "optimize_observation_projection", delayed)
    result = check_relation_equivalence(
        **_relations(), total_timeout_ms=500, preprocessing_budget_ms=100,
        per_obligation_timeout_ms=100)

    assert len(budgets) == 2
    assert budgets[0] <= 100
    assert budgets[1] <= budgets[0]
    assert result.preprocessing_elapsed_ms >= 35
    assert result.directional_budget_ms <= 500 - result.preprocessing_elapsed_ms
    assert result.total_elapsed_ms <= 500
    assert result.comparison.status == "equivalent"


def test_expired_total_budget_is_reported_unknown_without_fresh_solver_budget(
        monkeypatch):
    original = checker_adapter.optimize_observation_projection

    def delayed(body, bridges, *, guarded_bool_budget_ms):
        time.sleep(0.015)
        return original(body, bridges,
                        guarded_bool_budget_ms=guarded_bool_budget_ms)

    monkeypatch.setattr(checker_adapter, "optimize_observation_projection", delayed)
    result = check_relation_equivalence(
        **_relations(), total_timeout_ms=10, preprocessing_budget_ms=5,
        per_obligation_timeout_ms=10)

    assert result.directional_budget_ms == 0
    assert result.comparison.status == "unknown"
    assert result.comparison.equivalent is None


def test_objective_only_mismatch_remains_visible_to_relation_check():
    ctx = z3.Context()
    reference_value, candidate_value = z3.Ints(
        "objective_reference_value objective_candidate_value", ctx=ctx)
    observed = z3.Int("objective_observed", ctx=ctx)
    cost_alias = z3.Int("objective_cost", ctx=ctx)
    values = {
        "reference_assertions": [reference_value == 7],
        "candidate_assertions": [candidate_value == 7],
        "reference_bridges": [(observed, reference_value)],
        "candidate_bridges": [(observed, candidate_value)],
        "reference_cost_bridge": (cost_alias, z3.IntVal(3, ctx=ctx)),
        "candidate_cost_bridge": (cost_alias, z3.IntVal(4, ctx=ctx)),
    }

    result = check_relation_equivalence(
        **values, total_timeout_ms=1000, preprocessing_budget_ms=100)
    assert result.comparison.status == "counterexample"
    assert result.comparison.equivalent is False


def test_progress_callback_reports_projection_and_directional_boundaries():
    progress = []
    result = check_relation_equivalence(
        **_relations(), total_timeout_ms=1000, preprocessing_budget_ms=200,
        per_obligation_timeout_ms=100,
        progress_callback=progress.append)

    phases = [event["phase"] for event in progress]
    assert phases.index("reference_projection.start") < phases.index(
        "reference_projection.done")
    assert phases.index("reference_projection.done") < phases.index(
        "candidate_projection.start")
    assert phases.index("candidate_projection.start") < phases.index(
        "candidate_projection.done")
    assert phases.index("candidate_projection.done") < phases.index(
        "directional_check.start")
    assert phases.index("directional_check.start") < phases.index(
        "directional_check.done")
    assert result.comparison.status == "equivalent"


def test_total_budget_arguments_are_validated():
    values = _relations()
    with pytest.raises(TypeError):
        check_relation_equivalence(**values, total_timeout_ms=True)
    with pytest.raises(ValueError):
        check_relation_equivalence(**values, preprocessing_budget_ms=-1)
