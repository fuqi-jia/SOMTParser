"""Sparse explicit maps preserve all observed cells and signed cost."""
from __future__ import annotations

from copy import deepcopy

import pytest
import z3

from tools.semantic_checks.coordinate_map import ObservableMapRefusal
from tools.semantic_checks.finite_observables import align_finite_observables


def make_case(candidate_cost_sign: int = 1):
    ctx = z3.Context()
    leaf = z3.IntSort(ctx=ctx)
    row_sort = z3.ArraySort(leaf, leaf)
    # The finite-observable adapter binds candidate terms from the declared
    # model name. Keep the synthetic constraint root identical to that name.
    dist = z3.Const("dist", z3.ArraySort(leaf, row_sort))
    reference_cells = {}
    elements = []
    coordinates = []
    reference_assertions = []
    candidate_assertions = []
    observed = [(i, j) for i in range(10) for j in range(i + 2, 10)]
    for ordinal, index in enumerate(observed):
        symbol = f"sparse_reference_d_{index[0]}_{index[1]}"
        reference = z3.Int(symbol, ctx=ctx)
        candidate = z3.Select(z3.Select(dist, index[0]), index[1])
        reference_cells[index] = reference
        elements.append({"index": list(index), "symbol": symbol, "sort": "Int"})
        coordinates.append({"reference_index": list(index), "candidate_index": list(index)})
        reference_assertions.append(reference == ordinal)
        candidate_assertions.append(candidate == ordinal)

    hidden = [[i, j] for i in range(10) for j in range(10) if (i, j) not in set(observed)]
    ref_cost = z3.Int("sparse_reference_cost", ctx=ctx)
    cand_cost = z3.Real("sparse_candidate_cost", ctx=ctx)
    reference_assertions.append(ref_cost == 5)
    candidate_assertions.append(cand_cost == 5)
    metadata = {
        "observables": [{"name": "d", "shape": [10, 10], "sort": "Int",
                         "sparse": True, "elements": elements}],
        "coordinate_maps": [{"reference_name": "d", "candidate_name": "dist",
                             "coordinates": coordinates, "reconstruct": [],
                             "hidden_candidate_indices": hidden}],
    }
    payload = {"model": {"declarations": [{"name": "dist", "sort": "Int", "shape": [10, 10]}]}}
    aligned = align_finite_observables(
        metadata, payload,
        reference_assertions=reference_assertions,
        candidate_assertions=candidate_assertions,
        reference_objectives=[ref_cost],
        candidate_objectives=[cand_cost if candidate_cost_sign > 0 else -cand_cost],
        coordinate_maps=metadata["coordinate_maps"],
    )
    cost = z3.FreshConst(z3.RealSort(ctx=ctx), prefix="sparse_exact_signed_cost")
    reference_cost_bridge = (cost, ref_cost)
    candidate_cost_bridge = (cost, cand_cost if candidate_cost_sign > 0 else -cand_cost)
    return (metadata, payload, aligned, reference_assertions, candidate_assertions,
            reference_cost_bridge, candidate_cost_bridge, observed, hidden)


def test_sparse_36_of_100_coordinates_and_signed_cost_preserve_relation():
    from tools.semantic_checks.checker_adapter import check_relation_equivalence

    (_, _, aligned, reference_assertions, candidate_assertions,
     reference_cost, candidate_cost, observed, hidden) = make_case()
    checked = check_relation_equivalence(
        reference_assertions, candidate_assertions,
        reference_bridges=aligned.reference_bridges,
        candidate_bridges=aligned.candidate_bridges,
        reference_cost_bridge=reference_cost,
        candidate_cost_bridge=candidate_cost,
        total_timeout_ms=10000,
        preprocessing_budget_ms=None,
        per_obligation_timeout_ms=5000,
    )
    assert checked.comparison.equivalent is True
    assert checked.comparison.left_implies_right.unknown_obligations == 0
    assert checked.comparison.right_implies_left.unknown_obligations == 0
    assert len(observed) == 36
    assert len(hidden) == 64
    assert len(aligned.reference_bridges) == 36
    assert aligned.map_provenance[0]["sparse"] is True
    assert aligned.map_provenance[0]["hidden_candidate_indices"] == hidden


def test_sparse_map_detects_signed_cost_mismatch():
    from tools.semantic_checks.checker_adapter import check_relation_equivalence

    (_, _, aligned, reference_assertions, candidate_assertions,
     reference_cost, candidate_cost, _, _) = make_case(candidate_cost_sign=-1)
    checked = check_relation_equivalence(
        reference_assertions, candidate_assertions,
        reference_bridges=aligned.reference_bridges,
        candidate_bridges=aligned.candidate_bridges,
        reference_cost_bridge=reference_cost,
        candidate_cost_bridge=candidate_cost,
        total_timeout_ms=10000,
        preprocessing_budget_ms=None,
        per_obligation_timeout_ms=5000,
    )
    assert checked.comparison.equivalent is False
    assert (checked.comparison.left_implies_right.counterexample_conjunct is not None
            or checked.comparison.right_implies_left.counterexample_conjunct is not None)


@pytest.mark.parametrize("mutation,reason", [
    ("duplicate_reference", "duplicate-reference-coordinate"),
    ("duplicate_candidate", "duplicate-candidate-coordinate"),
    ("mapped_hidden", "mapped-coordinate-hidden"),
    ("out_of_bounds", "invalid-map"),
    ("missing_hidden", "candidate-coverage"),
    ("duplicate_hidden", "duplicate-hidden-coordinate"),
    ("hidden_out_of_bounds", "invalid-map"),
    ("hidden_boolean_index", "invalid-map"),
    ("missing_hidden_list", "invalid-map"),
    ("unobserved_reference", "reference-coverage"),
    ("missing_reference", "reference-coverage"),
    ("dense_reference", "reference-coverage"),
    ("nonboolean_sparse", "invalid-metadata"),
    ("missing_explicit_map", "invalid-map"),
])
def test_sparse_map_refuses_incomplete_or_conflicting_coverage(mutation, reason):
    metadata, payload, _, reference_assertions, candidate_assertions, *_ = make_case()
    metadata = deepcopy(metadata)
    mapping = metadata["coordinate_maps"][0]
    if mutation == "duplicate_reference":
        mapping["coordinates"].append(dict(mapping["coordinates"][0]))
    elif mutation == "duplicate_candidate":
        mapping["coordinates"][1]["candidate_index"] = list(mapping["coordinates"][0]["candidate_index"])
    elif mutation == "mapped_hidden":
        mapping["hidden_candidate_indices"].append(list(mapping["coordinates"][0]["candidate_index"]))
    elif mutation == "out_of_bounds":
        mapping["coordinates"][0]["candidate_index"] = [10, 0]
    elif mutation == "missing_hidden":
        mapping["hidden_candidate_indices"].pop()
    elif mutation == "duplicate_hidden":
        mapping["hidden_candidate_indices"].append(list(mapping["hidden_candidate_indices"][0]))
    elif mutation == "hidden_out_of_bounds":
        mapping["hidden_candidate_indices"][0] = [10, 0]
    elif mutation == "hidden_boolean_index":
        mapping["hidden_candidate_indices"][0] = [False, 0]
    elif mutation == "missing_hidden_list":
        del mapping["hidden_candidate_indices"]
    elif mutation == "unobserved_reference":
        mapping["coordinates"][0]["reference_index"] = [0, 0]
    elif mutation == "missing_reference":
        mapping["coordinates"].pop()
    elif mutation == "dense_reference":
        del metadata["observables"][0]["sparse"]
    elif mutation == "nonboolean_sparse":
        metadata["observables"][0]["sparse"] = 1
    else:
        metadata["coordinate_maps"] = []
    with pytest.raises(ObservableMapRefusal) as error:
        align_finite_observables(
            metadata, payload,
            reference_assertions=reference_assertions,
            candidate_assertions=candidate_assertions,
            coordinate_maps=metadata["coordinate_maps"],
        )
    assert error.value.code == "E_OBSERVABLE_COORDINATE_MAP"
    assert error.value.reason == reason


def test_hidden_coordinate_constraints_are_preserved_in_complete_relation():
    from tools.semantic_checks.checker_adapter import check_relation_equivalence

    (metadata, payload, _, refs, cands, ref_cost, cand_cost, _, _) = make_case()
    ctx = refs[0].ctx
    integer = z3.IntSort(ctx=ctx)
    dist = z3.Const("dist", z3.ArraySort(integer, z3.ArraySort(integer, integer)))
    # (0, 0) is hidden; (0, 2) is observed and fixed to zero. Dropping the
    # hidden cell's constraints would turn this inconsistent candidate SAT.
    cands.extend([dist[0][0] == dist[0][2], dist[0][0] == 1])
    aligned = align_finite_observables(
        metadata, payload, reference_assertions=refs, candidate_assertions=cands,
        coordinate_maps=metadata["coordinate_maps"])
    checked = check_relation_equivalence(
        refs, cands, reference_bridges=aligned.reference_bridges,
        candidate_bridges=aligned.candidate_bridges,
        reference_cost_bridge=ref_cost, candidate_cost_bridge=cand_cost,
        total_timeout_ms=10000, preprocessing_budget_ms=None,
        per_obligation_timeout_ms=5000)
    assert checked.comparison.equivalent is False
    assert checked.comparison.left_implies_right.counterexample_conjunct is not None


def test_dense_map_cannot_enable_hidden_coordinates_without_sparse_contract():
    metadata, payload, _, refs, cands, *_ = make_case()
    observable = metadata["observables"][0]
    del observable["sparse"]
    observable["shape"] = [36]
    # Make the reference dense while leaving the candidate's 64 cells hidden.
    for ordinal, (element, mapping) in enumerate(zip(
            observable["elements"], metadata["coordinate_maps"][0]["coordinates"])):
        element["index"] = [ordinal]
        mapping["reference_index"] = [ordinal]
    with pytest.raises(ObservableMapRefusal) as error:
        align_finite_observables(metadata, payload, reference_assertions=refs,
                                 candidate_assertions=cands,
                                 coordinate_maps=metadata["coordinate_maps"])
    assert error.value.reason == "invalid-map"
