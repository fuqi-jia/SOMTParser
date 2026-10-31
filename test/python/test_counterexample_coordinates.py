"""Diagnostic metadata must explain existing evidence, never repair a verdict."""
from copy import deepcopy
from dataclasses import asdict
from itertools import product
import json

import pytest
import z3

from tools.semantic_checks.counterexample_coordinates import (
    describe_counterexample, scalar_model_values, write_sidecar)
from tools.semantic_checks.directional_equivalence import check_equivalence
from tools.semantic_checks.finite_observables import align_finite_observables
from tools.semantic_checks.checker_adapter import check_relation_equivalence


def alignment(shape=(), sort="Int", candidate_sort=None, explicit=None):
    candidate_sort = candidate_sort or sort
    refs = {i: z3.Const("reference x" + str(i), z3.BoolSort() if sort == "Bool" else z3.IntSort())
            for i in product(*(range(n) for n in shape))}
    metadata = {"observables": [{"name": "x", "shape": list(shape), "elements": [
        {"index": list(i), "symbol": str(term.decl().name()), "sort": sort}
        for i, term in refs.items()]}]}
    payload = {"model": {"declarations": [{"name": "x", "sort": candidate_sort, "shape": list(shape)}]}}
    value = align_finite_observables(metadata, payload, reference_assertions=[],
                                    candidate_assertions=[], coordinate_maps=[] if explicit is None else [explicit])
    return value, refs


def comparison_at(alias, value):
    return check_equivalence(alias == value, alias != value,
                             total_timeout_ms=None, per_obligation_timeout_ms=None)


def diagnostic(value, comparison, **kw):
    return describe_counterexample(comparison, value.map_provenance, **kw)


@pytest.mark.parametrize("sort,value", [("Int", -4), ("Bool", True)])
def test_scalar_maps_actual_fresh_symbol_and_keeps_direction(sort, value):
    aligned, _ = alignment(sort=sort)
    alias = aligned.reference_bridges[0][0]
    comparison = comparison_at(alias, value)
    original = asdict(comparison)
    receipt = diagnostic(aligned, comparison)
    direction = receipt["directions"][0]
    row = direction["observations"][0]
    assert row["symbol"] == alias.sexpr()
    assert row["reference"]["name"] == row["candidate"]["name"] == "x"
    assert row["reference"]["index"] == []
    expected = z3.IntVal(value).sexpr() if sort == "Int" else "true"
    assert row["reference"]["value"] == expected
    assert (direction["admitted_by"], direction["excluded_by"]) == ("reference", "candidate")
    assert receipt["status"] == "counterexample" and receipt["equivalent"] is False
    assert asdict(comparison) == original


def test_multidimensional_indices_and_partial_model_do_not_get_defaults():
    aligned, _ = alignment((2, 2))
    alias = aligned.reference_bridges[2][0]
    comparison = comparison_at(alias, 17)
    rows = diagnostic(aligned, comparison)["directions"][0]["observations"]
    assert [row["reference"]["index"] for row in rows] == [[0, 0], [0, 1], [1, 0], [1, 1]]
    assert rows[2]["value"] == "17"
    assert all(row["status"] == "unknown" and row["reference"]["value"] is None
               for n, row in enumerate(rows) if n != 2)


def test_explicit_coordinate_permutation_only_no_value_inverse_inference():
    identity, _ = alignment((2,))
    raw = {"reference_name": "x", "candidate_name": "x", "reconstruct": [], "coordinates": [
        {"reference_index": [0], "candidate_index": [1]},
        {"reference_index": [1], "candidate_index": [0]}]}
    explicit, _ = alignment((2,), explicit=raw)
    for value, expected in ((identity, [0]), (explicit, [1])):
        result = diagnostic(value, comparison_at(value.reference_bridges[0][0], 1))
        assert result["directions"][0]["observations"][0]["candidate"]["index"] == expected
        assert "no inverse" in result["mapping_policy"]
    altered = deepcopy(explicit.map_provenance)
    altered[0]["kind"] = "identity"
    with pytest.raises(ValueError, match="explicit"):
        describe_counterexample(comparison_at(explicit.reference_bridges[0][0], 1), altered)
    # Value-dependent inversion of an assignment is not a fixed index map.
    altered[0]["kind"] = "inverse-permutation"
    with pytest.raises(ValueError, match="existing identity or explicit"):
        describe_counterexample(comparison_at(explicit.reference_bridges[0][0], 1), altered)


def test_bool_int_embedding_retains_out_of_range_tuple():
    aligned, _ = alignment(sort="Bool", candidate_sort="Int")
    comparison = comparison_at(aligned.reference_bridges[0][0], 2)
    row = diagnostic(aligned, comparison)["directions"][0]["observations"][0]
    assert row["value"] == row["candidate"]["value"] == "2"
    assert row["reference"]["status"] == "outside-Boolean-embedding"
    assert row["reference"]["value"] is None


def test_raw_model_capture_does_not_complete_array_or_unconstrained_symbols():
    x, unused = z3.Ints("capture_x capture_unused")
    array = z3.Array("capture_array", z3.IntSort(), z3.IntSort())
    solver = z3.Solver()
    solver.add(x == -3, array[0] == 4)
    assert solver.check() == z3.sat
    model = solver.model()
    before = model.sexpr()
    values = scalar_model_values(model)
    assert (x.sexpr(), "Int", "(- 3)") in values
    assert all(symbol not in (unused.sexpr(), array.sexpr()) for symbol, _, _ in values)
    assert model.sexpr() == before and model.get_interp(unused.decl()) is None


@pytest.mark.parametrize("reference_term,candidate_term,reference_direction,candidate_direction", [
    ("offset", "identity", "minimize", "minimize"),
    ("identity", "negative", "minimize", "maximize"),
])
def test_exact_cost_offset_and_direction_remain_counterexamples(reference_term, candidate_term,
                                                               reference_direction, candidate_direction):
    x, cost = z3.Ints("cost_x signed_cost_coordinate")
    terms = {"offset": x + 100, "identity": x, "negative": -x}
    ref, cand = terms[reference_term], terms[candidate_term]
    comparison = check_equivalence(z3.And(x == 3, cost == ref), z3.And(x == 3, cost == cand),
                                   total_timeout_ms=None, per_obligation_timeout_ms=None)
    metadata = [{"symbol": cost.sexpr(), "sort": "Int",
                 "reference": {"direction": reference_direction, "signed_expression": ref.sexpr()},
                 "candidate": {"direction": candidate_direction, "signed_expression": cand.sexpr()}}]
    original = deepcopy(metadata)
    receipt = describe_counterexample(comparison, [], cost_coordinates=metadata)
    objective = receipt["directions"][0]["objectives"][0]
    assert receipt["status"] == "counterexample" and receipt["equivalent"] is False
    assert objective["reference"] == metadata[0]["reference"]
    assert objective["candidate"] == metadata[0]["candidate"]
    assert objective["value"] == str(103 if reference_term == "offset" else 3)
    assert metadata == original


def test_old_receipt_reports_missing_bindings_without_suffix_guessing():
    aligned, _ = alignment()
    comparison = comparison_at(aligned.reference_bridges[0][0], 5)
    old = deepcopy(aligned.map_provenance)
    del old[0]["aliases"]
    receipt = describe_counterexample(comparison, old)
    assert len(receipt["unavailable_mappings"]) == 1
    assert receipt["directions"][0]["observations"] == []
    assert receipt["status"] == "counterexample"


def test_unknown_and_equivalent_have_no_fabricated_counterexample():
    aligned, _ = alignment()
    x = aligned.reference_bridges[0][0]
    for comparison in (check_equivalence(x == 1, x == 2, total_timeout_ms=0),
                       check_equivalence(x == 1, x == 1, total_timeout_ms=None)):
        receipt = diagnostic(aligned, comparison)
        assert receipt["directions"] == []
        assert receipt["status"] == comparison.status
        assert receipt["equivalent"] == comparison.equivalent


@pytest.mark.parametrize("mutate", ["duplicate_alias", "wrong_sort", "missing_coordinate"])
def test_inconsistent_recorded_bindings_refused(mutate):
    aligned, _ = alignment((2,))
    maps = deepcopy(aligned.map_provenance)
    if mutate == "duplicate_alias":
        maps[0]["aliases"][1]["symbol"] = maps[0]["aliases"][0]["symbol"]
    elif mutate == "wrong_sort":
        maps[0]["aliases"][0]["sort"] = "Bool"
    else:
        maps[0]["aliases"].pop()
    with pytest.raises(ValueError):
        describe_counterexample(comparison_at(aligned.reference_bridges[0][0], 2), maps)


def test_json_sidecar_pins_inputs_and_never_replaces_evidence(tmp_path):
    aligned, _ = alignment()
    comparison = comparison_at(aligned.reference_bridges[0][0], 5)
    paths = [tmp_path / name for name in ("semantic.json", "alignment.json", "diagnostic.json")]
    paths[0].write_text(json.dumps(asdict(comparison)))
    paths[1].write_text(json.dumps({"maps": aligned.map_provenance}))
    before = [path.read_bytes() for path in paths[:2]]
    sidecar = write_sidecar(*paths)
    import hashlib
    assert [row["sha256"] for row in sidecar["input_evidence"]] == [hashlib.sha256(raw).hexdigest() for raw in before]
    assert [path.read_bytes() for path in paths[:2]] == before
    with pytest.raises(FileExistsError):
        write_sidecar(*paths)
    with pytest.raises(ValueError, match="separate"):
        write_sidecar(paths[0], paths[1], paths[0])


def test_end_to_end_projected_array_relation_keeps_original_mismatch():
    aligned, refs = alignment((2,))
    array = z3.Array("x", z3.IntSort(), z3.IntSort())
    result = check_relation_equivalence([refs[(0,)] == 2, refs[(1,)] == 4],
        [array[0] == 2, array[1] == 5], reference_bridges=aligned.reference_bridges,
        candidate_bridges=aligned.candidate_bridges, total_timeout_ms=None,
        per_obligation_timeout_ms=None)
    rows = diagnostic(aligned, result.comparison)["directions"][0]["observations"]
    assert result.comparison.status == "counterexample"
    assert rows[1]["reference"]["index"] == [1] and rows[1]["value"] == "4"
