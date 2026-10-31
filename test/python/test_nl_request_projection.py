"""Focused guards for source-provenance-bound NL request projection."""
import copy
import hashlib
import json
from pathlib import Path
import sys

import pytest

TOOLS = Path(__file__).resolve().parents[2] / "tools"
sys.path.insert(0, str(TOOLS))
import nl_request_projection as adapter


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fixture_case():
    source = "x = VarArray(size=2, dom=range(3))\nsatisfy(x[0] < x[1])\n"
    request = {
        "id": "induscp/Test/0/hir",
        "source": source,
        "language": "hir",
        "context": {
            "task": "Preserve the model.",
            "observations": "Use these public output names and zero-based array shapes: "
                            '[{"name":"aux_gb","shape":[2],"sort":"Int"},'
                            '{"name":"x","shape":[2],"sort":"Int"}]. HIR: declare outputs.',
            "reference_access": "none",
        },
    }
    raw = (json.dumps(request, ensure_ascii=False, indent=2) + "\n").encode()
    model_sha, data_sha = "a" * 64, "b" * 64
    binding = {
        "id": request["id"],
        "request_sha256": sha(raw),
        "source_text_sha256": sha(source.encode()),
        "model_sha256": model_sha,
        "data_sha256": data_sha,
    }
    variables = []
    entities = []
    for i in range(2):
        variables.append({
            "source_symbol": f"aux_gb[{i}]", "entity": "aux_gb", "index": [i],
            "pycsp3_type": "integer", "role": "compiler-private",
            "auxiliary_registry_member": True, "explicit_source_bindings": [],
        })
    entities.append({"name": "aux_gb", "shape": [2], "elements": [
        {"index": [i], "source_symbol": f"aux_gb[{i}]", "role": "compiler-private"}
        for i in range(2)
    ]})
    for i in range(2):
        variables.append({
            "source_symbol": f"x[{i}]", "entity": "x", "index": [i],
            "pycsp3_type": "integer", "role": "source-public",
            "auxiliary_registry_member": False, "explicit_source_bindings": ["x"],
        })
    entities.append({"name": "x", "shape": [2], "elements": [
        {"index": [i], "source_symbol": f"x[{i}]", "role": "source-public"}
        for i in range(2)
    ]})
    provenance = {
        "schema": adapter.SCHEMA,
        "pycsp3_version": adapter.PY_CSP3_VERSION,
        "model": {"sha256": model_sha},
        "data": {"sha256": data_sha},
        "variables": variables,
        "entities": entities,
        "public_source_symbols": ["x[0]", "x[1]"],
        "compiler_private_symbols": ["aux_gb[0]", "aux_gb[1]"],
    }
    binding["provenance_sha256"] = adapter._canonical_sha(provenance)
    return raw, request, provenance, binding


def parsed_observations(raw):
    request = json.loads(raw)
    text = request["context"]["observations"]
    rows, start, end = adapter._observation_block(text)
    return request, rows, text[:start], text[end:]


def test_only_exactly_proven_private_observable_is_removed_and_other_fields_preserved():
    raw, original, provenance, binding = fixture_case()
    old_request = copy.deepcopy(original)
    projected, ledger = adapter.project_request_bytes(raw, provenance, binding)
    request, observations, prefix, suffix = parsed_observations(projected)
    assert [row["name"] for row in observations] == ["x"]
    assert observations[0] == {"name": "x", "shape": [2], "sort": "Int"}
    assert prefix.endswith("shapes: ")
    assert suffix == ". HIR: declare outputs."
    assert request["source"] == old_request["source"]
    assert request["context"]["task"] == old_request["context"]["task"]
    assert request["context"]["reference_access"] == old_request["context"]["reference_access"]
    assert json.loads(raw) == old_request
    assert ledger["removed_observations"] == [{"name": "aux_gb", "shape": [2], "sort": "Int"}]
    assert ledger["retained_observations"] == observations
    assert ledger["source_text_changed"] is False
    assert ledger["public_observation_order_preserved"] is True
    assert ledger["shapes_and_sorts_preserved"] is True


@pytest.mark.parametrize("field", ["model_sha256", "data_sha256"])
def test_wrong_runtime_model_or_data_pin_is_rejected(field):
    raw, _, provenance, binding = fixture_case()
    bad = dict(provenance)
    bad[field.removesuffix("_sha256")] = {"sha256": "c" * 64}
    with pytest.raises(adapter.RequestProjectionError, match="does not match"):
        adapter.project_request_bytes(raw, bad, binding)


def test_wrong_request_hash_is_rejected():
    raw, _, provenance, binding = fixture_case()
    bad = dict(binding, request_sha256="d" * 64)
    with pytest.raises(adapter.RequestProjectionError, match="request SHA256"):
        adapter.project_request_bytes(raw, provenance, bad)
    bad_provenance_pin = dict(binding, provenance_sha256="e" * 64)
    with pytest.raises(adapter.RequestProjectionError, match="provenance SHA256"):
        adapter.project_request_bytes(raw, provenance, bad_provenance_pin)


@pytest.mark.parametrize("mutation", ["role", "missing_aux_registry", "explicit_source_binding"])
def test_invalid_private_classification_is_rejected(mutation):
    raw, _, provenance, binding = fixture_case()
    bad = copy.deepcopy(provenance)
    record = bad["variables"][0]
    if mutation == "role":
        record["role"] = "source-public"
    elif mutation == "missing_aux_registry":
        record["auxiliary_registry_member"] = False
    else:
        record["explicit_source_bindings"] = ["aux_gb"]
    binding = dict(binding, provenance_sha256=adapter._canonical_sha(bad))
    with pytest.raises(adapter.RequestProjectionError, match="role conflicts"):
        adapter.project_request_bytes(raw, bad, binding)


def test_explicitly_bound_aux_named_source_variable_stays_public():
    raw, _, provenance, binding = fixture_case()
    request = json.loads(raw)
    request["source"] += "aux_gb = VarArray(size=2, dom=range(2))\n"
    source = request["source"]
    request["context"]["observations"] = (
        "Use these public output names and zero-based array shapes: "
        '[{"name":"aux_gb","shape":[2],"sort":"Int"},'
        '{"name":"x","shape":[2],"sort":"Int"}]. HIR: declare outputs.'
    )
    raw = (json.dumps(request, ensure_ascii=False, indent=2) + "\n").encode()
    binding = dict(binding, request_sha256=sha(raw), source_text_sha256=sha(source.encode()))
    bad = copy.deepcopy(provenance)
    for row in bad["variables"][:2]:
        row["role"] = "source-public"
        row["explicit_source_bindings"] = ["aux_gb"]
    for row in bad["entities"][0]["elements"]:
        row["role"] = "source-public"
    bad["public_source_symbols"] = ["aux_gb[0]", "aux_gb[1]", "x[0]", "x[1]"]
    bad["compiler_private_symbols"] = []
    binding = dict(binding, provenance_sha256=adapter._canonical_sha(bad))
    projected, ledger = adapter.project_request_bytes(raw, bad, binding)
    _, observations, _, _ = parsed_observations(projected)
    assert [row["name"] for row in observations] == ["aux_gb", "x"]
    assert ledger["removed_observations"] == []


def test_unknown_observation_ownership_fails_closed():
    raw, _, provenance, binding = fixture_case()
    request = json.loads(raw)
    request["context"]["observations"] = request["context"]["observations"].replace(
        '"name":"x"', '"name":"missing"')
    raw = (json.dumps(request, ensure_ascii=False, indent=2) + "\n").encode()
    binding = dict(binding, request_sha256=sha(raw))
    with pytest.raises(adapter.RequestProjectionError, match="no exact runtime entity"):
        adapter.project_request_bytes(raw, provenance, binding)
