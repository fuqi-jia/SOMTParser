"""Unbounded verification still proves complete relations and exact costs."""
from types import SimpleNamespace

import pytest

z3 = pytest.importorskip("z3")

from tools.semantic_checks import checker_adapter as adapter
from tools.semantic_checks import directional_equivalence as directional
from tools.semantic_checks import guarded_bool_definitions as guarded
from tools.semantic_checks import private_sort_witness as witness


def record_solver_timers(monkeypatch):
    timers = []
    original = z3.Solver.set

    def record(solver, *args, **kwargs):
        if "timeout" in kwargs:
            timers.append(kwargs["timeout"])
        return original(solver, *args, **kwargs)

    monkeypatch.setattr(z3.Solver, "set", record)
    return timers


def advancing_clocks(monkeypatch):
    clock = [0.0]

    def tick():
        clock[0] += 3600.0
        return clock[0]

    for module in (adapter, directional, guarded, witness):
        monkeypatch.setattr(module, "time", SimpleNamespace(monotonic=tick))


def test_unbounded_entailment_uses_no_solver_or_simplification_timer(monkeypatch):
    advancing_clocks(monkeypatch)
    timers = record_solver_timers(monkeypatch)

    def forbidden_timer(*args, **kwargs):
        raise AssertionError("unbounded simplification must not install TryFor")

    monkeypatch.setattr(z3, "TryFor", forbidden_timer)
    x = z3.Int("unbounded_x")
    result = directional.check_equivalence(
        z3.And(x >= 0, x <= 0), x == 0,
        total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.status == "equivalent"
    assert timers and set(timers) == {0}
    assert not result.left_implies_right.budget_exhausted
    assert not result.right_implies_left.budget_exhausted


@pytest.mark.parametrize("total,individual,expected", [
    (None, 10000, 10000), (10000, None, 10000),
])
def test_one_finite_limit_still_applies(monkeypatch, total, individual, expected):
    monkeypatch.setattr(directional, "time", SimpleNamespace(monotonic=lambda: 100.0))
    timers = record_solver_timers(monkeypatch)
    x = z3.Int("one_finite_limit_x")
    result = directional.check_equivalence(x == 0, z3.And(x >= 0, x <= 0),
        total_timeout_ms=total, per_obligation_timeout_ms=individual, simplify=False)
    assert result.status == "equivalent"
    assert timers and set(timers) == {expected}


def test_zero_total_budget_keeps_its_existing_unknown_meaning():
    x = z3.Int("zero_unbounded_x")
    result = directional.check_equivalence(x == 0, x == 0,
        total_timeout_ms=0, per_obligation_timeout_ms=None)
    assert result.status == "unknown"
    assert result.left_implies_right.budget_exhausted


@pytest.mark.parametrize("different_cost", [False, True])
def test_unbounded_projection_checks_every_observable_and_exact_cost(monkeypatch, different_cost):
    advancing_clocks(monkeypatch)
    timers = record_solver_timers(monkeypatch)
    r, c, observed = z3.Ints("unbounded_ref unbounded_cand unbounded_observed")
    cost = z3.Real("unbounded_cost")
    result = adapter.check_relation_equivalence(
        [r >= 0, r <= 2], [c >= 0, c <= 2],
        reference_bridges=[(observed, r)], candidate_bridges=[(observed, c)],
        reference_cost_bridge=(cost, r * z3.RealVal("1/3")),
        candidate_cost_bridge=(cost, c * z3.RealVal("1/2" if different_cost else "1/3")),
        total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.comparison.status == ("counterexample" if different_cost else "equivalent")
    assert result.total_budget_ms is result.preprocessing_budget_ms is result.directional_budget_ms is None
    assert result.reference.optimization.guarded_bool_budget_ms is None
    assert result.candidate.optimization.guarded_bool_budget_ms is None
    assert all(timer == 0 for timer in timers)


def test_unbounded_private_carrier_check_retains_independent_singleton_certificate(monkeypatch):
    advancing_clocks(monkeypatch)
    timers = record_solver_timers(monkeypatch)
    person = z3.DeclareSort("UnboundedPrivatePerson")
    a, b, c = z3.Consts("ua ub uc", person)
    ref, cand, observed = z3.Ints("private_ref private_cand private_observed")
    events = []
    result = adapter.check_relation_equivalence(
        [ref == 0], [cand == 0, z3.Distinct(a, b, c)],
        reference_bridges=[(observed, ref)], candidate_bridges=[(observed, cand)],
        total_timeout_ms=None, per_obligation_timeout_ms=None,
        progress_callback=events.append)
    assert result.comparison.status == "equivalent"
    receipt = result.counterexample_validation
    assert receipt.status == "certified-singleton-equivalence"
    assert receipt.antecedent_status == receipt.consequent_status == "sat"
    assert receipt.antecedent_other_status == receipt.consequent_other_status == "unsat"
    assert not receipt.budget_exhausted
    assert timers and set(timers) == {0}
    assert all(row["budget_ms"] is None for row in events if "budget_ms" in row)


def test_unbounded_guarded_elimination_keeps_the_projected_relation(monkeypatch):
    advancing_clocks(monkeypatch)
    sequence, integer = z3.Ints("unbounded_sequence unbounded_integer")
    bit = z3.Bool("unbounded_bit")
    body = z3.And(sequence >= 0, sequence <= 2,
        z3.If(bit, 1, 0) == integer, integer >= 0, integer <= 1,
        z3.Implies(sequence == 0, integer == 1),
        z3.Implies(sequence == 1, integer == 0),
        z3.Implies(sequence == 2, integer == 1))
    result = guarded.eliminate_guarded_bool_definitions(body, budget_ms=None)
    assert result.group_count == 1 and not result.fallback_reason
    from tools.semantic_checks.projection import existential_projection
    original = existential_projection(body, [sequence])
    changed = existential_projection(result.body, [sequence])
    solver = z3.Solver()
    solver.add(z3.Xor(original, changed))
    assert solver.check() == z3.unsat


def test_finite_preprocessing_setting_is_retained_without_total_deadline():
    r, c, observed = z3.Ints("finite_prep_ref finite_prep_cand finite_prep_observed")
    result = adapter.check_relation_equivalence([r == 1], [c == 1],
        reference_bridges=[(observed, r)], candidate_bridges=[(observed, c)],
        total_timeout_ms=None, preprocessing_budget_ms=0, per_obligation_timeout_ms=None)
    assert result.comparison.status == "equivalent"
    assert result.preprocessing_budget_ms == 0
    assert result.reference.optimization.guarded_bool_budget_ms == 0
    assert result.directional_budget_ms is None
