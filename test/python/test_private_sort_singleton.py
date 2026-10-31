"""Independent SAT/UNSAT certificates for exact singleton observable relations."""
from types import SimpleNamespace

import pytest

z3 = pytest.importorskip("z3")

from tools.semantic_checks.checker_adapter import (
    candidate_projection, check_relation_equivalence)
from tools.semantic_checks.directional_equivalence import check_equivalence
from tools.semantic_checks import private_sort_witness as witness


def _relations():
    ctx = z3.Context()
    person = z3.DeclareSort("PrivatePerson", ctx=ctx)
    a, b, c = z3.Consts("a b c", person)
    reference, candidate, observed = z3.Ints("reference candidate observed", ctx=ctx)
    values = dict(reference_assertions=[reference == 0],
        candidate_assertions=[candidate == 0, z3.Distinct(a, b, c)],
        reference_bridges=[(observed, reference)], candidate_bridges=[(observed, candidate)])
    return values, (ctx, reference, candidate, observed)


def _check(values):
    return check_relation_equivalence(**values, total_timeout_ms=5000,
        preprocessing_budget_ms=500, per_obligation_timeout_ms=1000)


def _assert_certificate(result):
    assert result.comparison.status == "equivalent"
    assert result.comparison.equivalent is True
    assert result.comparison.proof_kind == "independent-singleton-observable-equivalence"
    receipt = result.counterexample_validation
    assert receipt.status == "certified-singleton-equivalence"
    assert receipt.antecedent_status == receipt.consequent_status == "sat"
    assert receipt.antecedent_other_status == receipt.consequent_other_status == "unsat"
    assert result.comparison.raw_same_carrier_comparison.status == "counterexample"
    assert result.comparison.left_implies_right.proof_kind == "independent-singleton-observable-inclusion"
    assert result.comparison.right_implies_left.proof_kind == "independent-singleton-observable-inclusion"
    assert result.comparison.left_implies_right.counterexample_model is None
    assert result.comparison.right_implies_left.counterexample_model is None


def test_singleton_relations_are_equivalent_across_different_carriers():
    values, _ = _relations()
    result = _check(values)
    _assert_certificate(result)
    assert result.counterexample_validation.observable_values == (("observed", "Int", "0"),)


def test_reverse_direction_singleton_certificate():
    values, _ = _relations()
    values["reference_assertions"], values["candidate_assertions"] = values["candidate_assertions"], values["reference_assertions"]
    values["reference_bridges"], values["candidate_bridges"] = values["candidate_bridges"], values["reference_bridges"]
    result = _check(values)
    _assert_certificate(result)
    assert result.counterexample_validation.direction == "right_implies_left"


def test_all_output_and_cost_coordinates_are_in_the_certificate():
    values, parts = _relations()
    ctx = parts[0]
    ref_extra, cand_extra, extra = z3.Ints("ref_extra cand_extra extra", ctx=ctx)
    values["reference_assertions"].append(ref_extra == 9)
    values["candidate_assertions"].append(cand_extra == 9)
    values["reference_bridges"].append((extra, ref_extra))
    values["candidate_bridges"].append((extra, cand_extra))
    cost = z3.Real("cost", ctx=ctx)
    values["reference_cost_bridge"] = (cost, z3.RealVal("1/3", ctx=ctx))
    values["candidate_cost_bridge"] = (cost, z3.RealVal("1/3", ctx=ctx))
    result = _check(values)
    _assert_certificate(result)
    actual = {name: (sort, value) for name, sort, value in result.counterexample_validation.observable_values}
    assert actual == {"observed": ("Int", "0"), "extra": ("Int", "9"),
                      "cost": ("Real", z3.RealVal("1/3", ctx=ctx).sexpr())}


def test_non_singleton_cost_prevents_false_equivalence_certificate():
    values, parts = _relations()
    ref_cost, cand_cost, cost = z3.Reals("ref_cost cand_cost cost", ctx=parts[0])
    values["reference_cost_bridge"] = (cost, ref_cost)
    values["candidate_cost_bridge"] = (cost, cand_cost)
    result = _check(values)
    assert result.comparison.status == "unknown"
    receipt = result.counterexample_validation
    assert receipt.antecedent_status == receipt.consequent_status == "sat"
    assert receipt.antecedent_other_status == "sat"
    assert receipt.consequent_other_status is None


def test_non_singleton_extra_output_prevents_false_equivalence_certificate():
    values, parts = _relations()
    ref_extra, cand_extra, extra = z3.Bools("ref_extra cand_extra extra", ctx=parts[0])
    values["reference_bridges"].append((extra, ref_extra))
    values["candidate_bridges"].append((extra, cand_extra))
    result = _check(values)
    assert result.comparison.status == "unknown"
    assert result.counterexample_validation.antecedent_other_status == "sat"


def test_consequent_with_more_than_one_tuple_stays_unknown():
    values, parts = _relations()
    values["candidate_assertions"] = [parts[2] >= 0, parts[2] <= 1,
                                      values["candidate_assertions"][1]]
    result = _check(values)
    assert result.comparison.status == "unknown"
    receipt = result.counterexample_validation
    assert receipt.antecedent_other_status == "unsat"
    assert receipt.consequent_other_status == "sat"
    assert "consequent" in receipt.reason


def test_empty_tuple_means_each_relation_only_needs_to_be_feasible():
    ctx = z3.Context()
    person = z3.DeclareSort("Person", ctx=ctx)
    a, b, c = z3.Consts("a b c", person)
    result = _check(dict(reference_assertions=[z3.BoolVal(True, ctx=ctx)],
        candidate_assertions=[z3.Distinct(a, b, c)], reference_bridges=[], candidate_bridges=[]))
    _assert_certificate(result)
    assert result.counterexample_validation.observable_values == ()


def _raw_and_inputs():
    values, _ = _relations()
    reference = candidate_projection(values["reference_assertions"], values["reference_bridges"]).formula
    candidate = candidate_projection(values["candidate_assertions"], values["candidate_bridges"]).formula
    raw = check_equivalence(reference, candidate, total_timeout_ms=1000)
    assert raw.status == "counterexample"
    ref_body, ref_aliases = witness.original_relation(values["reference_assertions"], values["reference_bridges"], None)
    cand_body, cand_aliases = witness.original_relation(values["candidate_assertions"], values["candidate_bridges"], None)
    options = dict(reference_body=ref_body, candidate_body=cand_body,
        reference_aliases=ref_aliases, candidate_aliases=cand_aliases,
        private_sorts=("PrivatePerson",), per_query_timeout_ms=1000)
    return raw, reference, candidate, options


def test_singleton_queries_share_the_existing_total_deadline(monkeypatch):
    raw, reference, candidate, options = _raw_and_inputs()
    clock = [10.0]
    progress = []
    monkeypatch.setattr(witness, "time", SimpleNamespace(monotonic=lambda: clock[0]))

    def event(row):
        progress.append(row)
        if row["phase"] == "counterexample_consequent.done":
            clock[0] = 12.0

    result, receipt = witness.revalidate_private_sort_counterexample(
        raw, reference, candidate, **options, deadline=11.0, progress_callback=event)
    assert result.status == "unknown"
    assert receipt.budget_exhausted
    assert receipt.antecedent_other_status == "unknown"
    assert receipt.consequent_other_status is None
    assert not any(row["phase"].startswith("singleton_") for row in progress)


def test_unknown_exclusion_proof_does_not_become_equivalence(monkeypatch):
    raw, reference, candidate, options = _raw_and_inputs()
    original_solver = z3.Solver
    created = []

    class UnknownOnFourth:
        def __init__(self, *args, **kwargs):
            self.solver = original_solver(*args, **kwargs)
            created.append(self)
            self.index = len(created)

        def __getattr__(self, name):
            return getattr(self.solver, name)

        def check(self):
            return z3.unknown if self.index == 4 else self.solver.check()

        def reason_unknown(self):
            return "controlled exclusion timeout"

    monkeypatch.setattr(z3, "Solver", UnknownOnFourth)
    result, receipt = witness.revalidate_private_sort_counterexample(raw,
        reference, candidate, **options, deadline=witness.time.monotonic() + 5)
    assert result.status == "unknown"
    assert result.equivalent is None
    assert receipt.antecedent_other_status == "unknown"
    assert receipt.consequent_other_status is None
    assert len(created) == 4
    assert "controlled exclusion timeout" in receipt.reason


def test_closed_boolean_output_is_part_of_the_singleton_tuple():
    values, parts = _relations()
    ref_flag, cand_flag, flag = z3.Bools("ref_flag cand_flag flag", ctx=parts[0])
    values["reference_assertions"].append(ref_flag)
    values["candidate_assertions"].append(cand_flag)
    values["reference_bridges"].append((flag, ref_flag))
    values["candidate_bridges"].append((flag, cand_flag))
    result = _check(values)
    _assert_certificate(result)
    assert ("flag", "Bool", "true") in result.counterexample_validation.observable_values
