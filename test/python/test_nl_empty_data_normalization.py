"""Empty NL provider data containers normalize before digest selection only."""
from copy import deepcopy
import hashlib
import json

import pytest
import z3
import somtparser as sp
from somtparser.hir import build_hir
from somtparser.hir_canonical import canonicalize_hir
from somtparser.natural_language import Candidate, ModelError


SOURCE = "Choose a nonnegative real x at most 3; minimize twice x."


def model(data):
    def literal(value):
        return {"literal": str(value), "sort": "Real"}
    return {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "optimization",
        "declarations": [{"name": "x", "sort": "Real"}],
        "functions": [],
        "constraints": [
            {"expr": {"op": "ge", "args": [{"var": "x"}, literal(0)]},
             "span": [0, len(SOURCE)]},
            {"expr": {"op": "le", "args": [{"var": "x"}, literal(3)]},
             "span": [0, len(SOURCE)]},
        ],
        "objectives": [{"sense": "minimize",
                        "expr": {"op": "mul", "args": [literal(2), {"var": "x"}]},
                        "span": [0, len(SOURCE)]}],
        "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [], "data": deepcopy(data),
    }


def propose(raw):
    return sp.propose_nl(SOURCE, language="hir", provider=lambda _request: raw)


def test_empty_provider_data_preserves_full_relation_objective_and_input():
    raw = model([])
    original = deepcopy(raw)
    candidate = propose(raw)
    assert raw == original
    assert candidate.valid, candidate.diagnostics
    assert candidate.model["data"] == {}
    translated = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert translated.ok, translated.diagnostics
    actual = z3.Optimize()
    actual.from_string(translated.to_smt2())
    x = z3.Real("x")
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*actual.assertions()), z3.And(x >= 0, x <= 3)))
    assert solver.check() == z3.unsat
    assert len(actual.objectives()) == 1
    solver = z3.Solver()
    solver.add(actual.objectives()[0] != 2*x)
    assert solver.check() == z3.unsat
    assert translated.report()["normalization_ledger"] == candidate.normalization_ledger


def test_empty_data_ledger_replays_and_canonicalization_is_idempotent():
    raw = model([])
    normalized, ledger = canonicalize_hir(raw)
    assert ledger == [{"path": "/data", "rule": "empty-data-array-to-object",
                       "before": [], "after": {}}]
    replayed = deepcopy(raw)
    assert replayed["data"] == ledger[0]["before"]
    replayed["data"] = deepcopy(ledger[0]["after"])
    assert replayed == normalized
    assert canonicalize_hir(normalized) == (normalized, [])
    # Returned snapshots do not alias the original or the audit ledger.
    normalized["data"]["other"] = [9]
    assert raw["data"] == [] and ledger[0]["after"] == {}


@pytest.mark.parametrize("data", [[{}], [0], [["cost", []]], None, "", False])
def test_nonempty_or_other_data_shapes_remain_explicitly_invalid(data):
    raw = model(data)
    before = deepcopy(raw)
    normalized, ledger = canonicalize_hir(raw)
    assert normalized == before and ledger == []
    candidate = propose(raw)
    assert not candidate.valid
    assert any("data must be an object" in message for message in candidate.diagnostics)
    assert candidate.model["data"] == data
    assert raw == before and candidate.normalization_ledger == []


def test_valid_data_objects_and_nested_empty_arrays_are_untouched():
    raw = model({"empty_table": [], "matrix": [[], []]})
    normalized, ledger = canonicalize_hir(raw)
    assert normalized == raw and ledger == []
    assert propose(raw).valid


def test_missing_data_is_not_inserted_and_nonhir_payload_is_not_coerced():
    raw = model({})
    del raw["data"]
    assert canonicalize_hir(raw) == (raw, [])
    assert "data" not in propose(raw).model
    other = model([])
    other["language"] = "typed"
    assert canonicalize_hir(other) == (other, [])


def test_strict_hir_build_still_rejects_empty_data_list():
    with pytest.raises(ModelError, match="data must be an object"):
        build_hir(model([]), SOURCE)


def test_ledger_is_digest_bound_and_roundtrip_does_not_renormalize():
    candidate = propose(model([]))
    explicit_object = propose(model({}))
    assert candidate.model == explicit_object.model
    assert candidate.provider == explicit_object.provider
    assert candidate.digest != explicit_object.digest
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest and restored.valid
    assert restored.normalization_ledger == candidate.normalization_ledger
    for mutation in ("model", "ledger", "remove-ledger"):
        envelope = json.loads(candidate.to_json())
        if mutation == "model":
            envelope["model"]["data"] = []
        elif mutation == "ledger":
            envelope["normalization_ledger"][0]["before"] = [0]
        else:
            del envelope["normalization_ledger"]
        with pytest.raises(ModelError, match="digest"):
            Candidate.from_json(json.dumps(envelope))


def test_old_invalid_snapshot_keeps_its_model_digest_and_refusal():
    raw = model([])
    raw["context"] = {}
    payload = {"source": SOURCE, "model": raw, "provider": "old-sealed-provider"}
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True,
                                      separators=(",", ":")).encode()).hexdigest()
    envelope = dict(payload, schema="somt-nl-candidate-v1", digest=digest,
                    source_sha256=hashlib.sha256(SOURCE.encode()).hexdigest())
    restored = Candidate.from_json(json.dumps(envelope))
    assert restored.digest == digest and restored.model == raw
    assert not restored.valid and restored.normalization_ledger == []
    assert any("data must be an object" in text for text in restored.diagnostics)


def test_empty_data_does_not_hide_missing_lookup_or_unresolved_interpretation():
    raw = model([])
    raw["constraints"][0]["expr"] = {
        "op": "eq", "args": [
            {"data": "missing", "indices": [{"literal": 0, "sort": "Int"}],
             "default": {"literal": 0, "sort": "Int"}},
            {"literal": 0, "sort": "Int"},
        ],
    }
    candidate = propose(raw)
    assert not candidate.valid
    assert any("unknown data table" in text for text in candidate.diagnostics)
    ambiguous = model([])
    ambiguous["unresolved"] = ["The source gives conflicting bounds."]
    refused = propose(ambiguous)
    assert not refused.valid
    assert refused.model["unresolved"] == ambiguous["unresolved"]
