"""Private carriers cannot manufacture observable relation counterexamples."""
import time

import pytest

z3 = pytest.importorskip("z3")

from tools.semantic_checks.checker_adapter import check_relation_equivalence
from tools.semantic_checks.directional_equivalence import check_equivalence
from tools.semantic_checks.private_sort_witness import (
    private_sort_names, revalidate_private_sort_counterexample)


def _relations(reference_value=0, candidate_value=0):
    ctx = z3.Context()
    person = z3.DeclareSort("Person", ctx=ctx)
    a, b, c = z3.Consts("a b c", person)
    ref, cand, observed = z3.Ints("reference candidate observed", ctx=ctx)
    values = dict(reference_assertions=[ref == reference_value],
        candidate_assertions=[cand == candidate_value, z3.Distinct(a, b, c)],
        reference_bridges=[(observed, ref)], candidate_bridges=[(observed, cand)])
    return values, (ctx, person, a, b, c, ref, cand, observed)


def _check(values):
    return check_relation_equivalence(**values, total_timeout_ms=5000,
        preprocessing_budget_ms=500, per_obligation_timeout_ms=1000)


def test_small_private_carrier_is_not_a_counterexample():
    values, parts = _relations()
    values["reference_assertions"] = [parts[5] >= 0, parts[5] <= 1]
    values["candidate_assertions"] = [parts[6] >= 0, parts[6] <= 1,
                                      z3.Distinct(*parts[2:5])]
    checked = _check(values)
    assert checked.comparison.status == "unknown"
    assert checked.comparison.equivalent is None
    receipt = checked.counterexample_validation
    assert receipt.status == "carrier-dependent-witness"
    assert receipt.antecedent_status == receipt.consequent_status == "sat"
    assert receipt.observable_values in ((("observed", "Int", "0"),),
                                          (("observed", "Int", "1"),))
    assert receipt.antecedent_other_status == "sat"
    assert receipt.original_counterexample_model is not None
    assert not receipt.budget_exhausted
    assert checked.comparison.left_implies_right.counterexample_model is None
    assert checked.comparison.left_implies_right.counterexample_conjunct is None
    assert "private-sort-alignment-required" in receipt.reason


def test_real_output_difference_is_independently_certified():
    values, _ = _relations(candidate_value=1)
    checked = _check(values)
    assert checked.comparison.status == "counterexample"
    assert checked.comparison.equivalent is False
    receipt = checked.counterexample_validation
    assert receipt.status == "certified-counterexample"
    assert receipt.antecedent_status == "sat"
    assert receipt.consequent_status == "unsat"
    assert receipt.observable_values == (("observed", "Int", "0"),)
    assert checked.comparison.left_implies_right.counterexample_model is not None


def test_cost_bridge_is_part_of_independent_witness():
    values, parts = _relations()
    ctx = parts[0]
    cost = z3.Real("observed_cost", ctx=ctx)
    values["reference_cost_bridge"] = (cost, z3.IntVal(2, ctx=ctx))
    values["candidate_cost_bridge"] = (cost, z3.IntVal(3, ctx=ctx))
    checked = _check(values)
    assert checked.comparison.status == "counterexample"
    receipt = checked.counterexample_validation
    assert receipt.status == "certified-counterexample"
    assert receipt.consequent_status == "unsat"
    assert ("observed_cost", "Real", "2.0") in receipt.observable_values


def test_same_carrier_unsat_proof_remains_sufficient():
    values, parts = _relations()
    values["reference_assertions"].append(z3.Distinct(*parts[2:5]))
    checked = _check(values)
    assert checked.comparison.status == "equivalent"
    assert checked.counterexample_validation is None


def test_closed_enumeration_carrier_retains_equivalence_support():
    ctx = z3.Context()
    person, _ = z3.EnumSort("ClosedPerson", ["Agatha", "Butler", "Charles"], ctx=ctx)
    a, b, c = z3.Consts("a b c", person)
    ref, cand, observed = z3.Ints("reference candidate observed", ctx=ctx)
    checked = _check(dict(reference_assertions=[ref == 0],
        candidate_assertions=[cand == 0, z3.Distinct(a, b, c)],
        reference_bridges=[(observed, ref)], candidate_bridges=[(observed, cand)]))
    assert checked.comparison.status == "equivalent"
    assert checked.counterexample_validation is None


def test_domain_valued_observable_requires_explicit_alignment():
    ctx = z3.Context()
    person = z3.DeclareSort("Person", ctx=ctx)
    ref, cand, observed, a, b = z3.Consts("reference candidate observed a b", person)
    checked = _check(dict(reference_assertions=[ref == a],
        candidate_assertions=[cand == a, z3.Distinct(a, b)],
        reference_bridges=[(observed, ref)], candidate_bridges=[(observed, cand)]))
    assert checked.comparison.status == "unknown"
    receipt = checked.counterexample_validation
    assert "domain-valued" in receipt.reason
    assert receipt.witness_status is None
    assert not receipt.budget_exhausted


def test_alias_mismatch_cannot_certify_private_sort_witness():
    values, parts = _relations(candidate_value=1)
    other_observed = z3.Int("other_observed", ctx=parts[0])
    values["candidate_bridges"] = [(other_observed, parts[6])]
    checked = _check(values)
    assert checked.comparison.status == "unknown"
    assert "observable aliases differ" in checked.counterexample_validation.reason


def test_iterator_relations_are_retained_for_independent_checks():
    values, _ = _relations(candidate_value=1)
    values = {name: iter(value) for name, value in values.items()}
    checked = _check(values)
    assert checked.comparison.status == "counterexample"
    assert checked.counterexample_validation.status == "certified-counterexample"


def test_builtin_mismatch_does_not_require_private_carrier_validation():
    values, _ = _relations(candidate_value=1)
    values["candidate_assertions"] = values["candidate_assertions"][:1]
    checked = _check(values)
    assert checked.comparison.status == "counterexample"
    assert checked.counterexample_validation is None


def test_revalidation_never_restarts_expired_total_budget(monkeypatch):
    ctx = z3.Context()
    observed = z3.Int("observed", ctx=ctx)
    left, right = observed == 0, observed == 1
    raw = check_equivalence(left, right, total_timeout_ms=1000)
    assert raw.status == "counterexample"

    def forbidden_solver(*args, **kwargs):
        raise AssertionError("expired deadline must not start a solver")

    monkeypatch.setattr(z3, "Solver", forbidden_solver)
    checked, receipt = revalidate_private_sort_counterexample(
        raw, left, right, reference_body=left, candidate_body=right,
        reference_aliases=[observed], candidate_aliases=[observed],
        private_sorts=("Person",), deadline=time.monotonic() - 1,
        per_query_timeout_ms=1000)
    assert checked.status == "unknown"
    assert checked.equivalent is None
    assert receipt.budget_exhausted
    assert receipt.witness_status == "unknown"


def test_binder_only_private_sort_is_detected():
    ctx = z3.Context()
    person = z3.DeclareSort("Person", ctx=ctx)
    x = z3.Const("x", person)
    expression = z3.ForAll([x], z3.BoolVal(True, ctx=ctx))
    assert private_sort_names([expression]) == ("Person",)


def test_array_index_and_value_sorts_are_detected():
    ctx = z3.Context()
    index = z3.DeclareSort("PrivateIndex", ctx=ctx)
    value = z3.DeclareSort("PrivateValue", ctx=ctx)
    array = z3.Array("array", index, value)
    assert private_sort_names([array == array]) == ("PrivateIndex", "PrivateValue")


def test_multidomain_array_includes_later_private_index():
    ctx = z3.Context()
    person = z3.DeclareSort("LaterIndex", ctx=ctx)
    sort = z3.ArraySort(z3.IntSort(ctx=ctx), person, z3.BoolSort(ctx=ctx))
    array = z3.Const("array", sort)
    assert private_sort_names([array == array]) == ("LaterIndex",)


def test_builtin_arrays_are_not_private_carriers():
    ctx = z3.Context()
    array = z3.Array("array", z3.IntSort(ctx=ctx), z3.BoolSort(ctx=ctx))
    assert private_sort_names([array == array]) == ()


def test_recursive_datatype_field_private_sort_is_detected():
    ctx = z3.Context()
    person = z3.DeclareSort("Person", ctx=ctx)
    tree = z3.Datatype("Tree", ctx=ctx)
    tree.declare("leaf", ("person", person))
    tree.declare("branch", ("child", tree))
    tree = tree.create()
    value = z3.Const("value", tree)
    assert private_sort_names([value == value]) == ("Person",)


def test_sequence_element_private_sort_is_detected():
    ctx = z3.Context()
    person = z3.DeclareSort("Person", ctx=ctx)
    value = z3.Const("value", z3.SeqSort(person))
    assert private_sort_names([value == value]) == ("Person",)


def test_progress_records_revalidation_under_remaining_deadline():
    values, _ = _relations(candidate_value=1)
    progress = []
    checked = check_relation_equivalence(**values, total_timeout_ms=5000,
        preprocessing_budget_ms=500, per_obligation_timeout_ms=1000,
        progress_callback=progress.append)
    assert checked.comparison.status == "counterexample"
    phases = [row["phase"] for row in progress]
    for name in ("counterexample_witness", "counterexample_antecedent", "counterexample_consequent"):
        assert phases.index(name + ".start") < phases.index(name + ".done")
    assert all(0 < row["budget_ms"] <= 1000 for row in progress
               if row["phase"].startswith("counterexample_") and "budget_ms" in row)
    assert phases.index("counterexample_consequent.done") < phases.index("directional_check.done")
    assert checked.total_elapsed_ms < 5000


def test_reverse_direction_small_carrier_is_not_a_counterexample():
    values, parts = _relations()
    values["reference_assertions"] = [parts[5] >= 0, parts[5] <= 1]
    values["candidate_assertions"] = [parts[6] >= 0, parts[6] <= 1,
                                      z3.Distinct(*parts[2:5])]
    values["reference_assertions"], values["candidate_assertions"] = (
        values["candidate_assertions"], values["reference_assertions"])
    values["reference_bridges"], values["candidate_bridges"] = (
        values["candidate_bridges"], values["reference_bridges"])
    checked = _check(values)
    assert checked.comparison.status == "unknown"
    receipt = checked.counterexample_validation
    assert receipt.direction == "right_implies_left"
    assert receipt.status == "carrier-dependent-witness"
    assert receipt.antecedent_status == receipt.consequent_status == "sat"
    assert checked.comparison.right_implies_left.counterexample_model is None


def test_reverse_direction_output_difference_is_certified():
    values, parts = _relations()
    values["reference_assertions"].append(z3.Distinct(*parts[2:5]))
    values["candidate_assertions"] = [parts[6] >= 0, parts[6] <= 1,
                                      z3.Distinct(*parts[2:5])]
    checked = _check(values)
    assert checked.comparison.status == "counterexample"
    receipt = checked.counterexample_validation
    assert receipt.direction == "right_implies_left"
    assert receipt.status == "certified-counterexample"
    assert receipt.observable_values == (("observed", "Int", "1"),)
    assert receipt.antecedent_status == "sat"
    assert receipt.consequent_status == "unsat"


def test_string_and_regular_language_have_builtin_carriers():
    ctx = z3.Context()
    text = z3.String("text", ctx=ctx)
    language = z3.Re("literal", ctx=ctx)
    assert private_sort_names([text == "value", z3.InRe(text, language)]) == ()


def test_string_counterexample_is_not_blocked_as_private_sort():
    ctx = z3.Context()
    ref, cand, observed = [z3.String(name, ctx=ctx)
                            for name in ("reference", "candidate", "observed")]
    checked = _check(dict(reference_assertions=[ref == "left"],
        candidate_assertions=[cand == "right"],
        reference_bridges=[(observed, ref)], candidate_bridges=[(observed, cand)]))
    assert checked.comparison.status == "counterexample"
    assert checked.counterexample_validation is None
