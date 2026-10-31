#!/usr/bin/env python3
"""Project proven PyCSP3 compiler-private observables out of an NL request.

This is metadata-only glue around ``pycsp3_source_projection``. It does not
classify variables: it accepts only the existing PyCSP3 2.6.1 identity-based
provenance output, verifies request/model/data pins, and delegates role
validation and projection to ``project_observables``.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys

try:
    from pycsp3_source_projection import SCHEMA, PY_CSP3_VERSION, project_observables
except ImportError:  # import as a package from a test harness
    from .pycsp3_source_projection import SCHEMA, PY_CSP3_VERSION, project_observables


class RequestProjectionError(ValueError):
    """Raised when a request cannot be safely bound to role provenance."""


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _canonical_sha(value) -> str:
    return _sha(json.dumps(value, sort_keys=True, separators=(",", ":"),
                           ensure_ascii=False).encode("utf-8"))


def _validate_binding(request, raw_request: bytes, provenance, binding):
    required = {"id", "request_sha256", "source_text_sha256", "model_sha256", "data_sha256",
                "provenance_sha256"}
    if not isinstance(binding, dict) or not required.issubset(binding):
        raise RequestProjectionError("Binding must pin id, request/source/model/data SHA256")
    if request.get("id") != binding["id"]:
        raise RequestProjectionError("Request id does not match the pinned case")
    if _sha(raw_request) != binding["request_sha256"]:
        raise RequestProjectionError("Request bytes do not match the pinned request SHA256")
    source = request.get("source")
    if not isinstance(source, str) or _sha(source.encode("utf-8")) != binding["source_text_sha256"]:
        raise RequestProjectionError("Source text does not match the pinned source SHA256")
    if provenance.get("schema") != SCHEMA or provenance.get("pycsp3_version") != PY_CSP3_VERSION:
        raise RequestProjectionError("Unsupported or missing PyCSP3 source-projection provenance")
    model = provenance.get("model")
    data = provenance.get("data")
    if not isinstance(model, dict) or model.get("sha256") != binding["model_sha256"]:
        raise RequestProjectionError("Runtime provenance model SHA256 does not match the pinned model")
    if not isinstance(data, dict) or data.get("sha256") != binding["data_sha256"]:
        raise RequestProjectionError("Runtime provenance data SHA256 does not match the pinned data")
    if _canonical_sha(provenance) != binding["provenance_sha256"]:
        raise RequestProjectionError("Runtime provenance bytes do not match the pinned provenance SHA256")


def _validate_roles(provenance):
    records = provenance.get("variables")
    if not isinstance(records, list):
        raise RequestProjectionError("Provenance lacks a variable inventory")
    by_symbol = {}
    for row in records:
        if not isinstance(row, dict):
            raise RequestProjectionError("Malformed variable provenance entry")
        symbol = row.get("source_symbol")
        role = row.get("role")
        bindings = row.get("explicit_source_bindings")
        auxiliary = row.get("auxiliary_registry_member")
        if not isinstance(symbol, str) or not symbol or symbol in by_symbol:
            raise RequestProjectionError("Missing or duplicate provenance symbol")
        if not isinstance(bindings, list) or not all(isinstance(x, str) for x in bindings):
            raise RequestProjectionError("Malformed explicit source bindings")
        if not isinstance(auxiliary, bool):
            raise RequestProjectionError("Missing auxiliary-registry membership evidence")
        expected_role = "compiler-private" if auxiliary and not bindings else "source-public"
        if role != expected_role:
            raise RequestProjectionError("Variable role conflicts with registry/binding evidence: " + symbol)
        by_symbol[symbol] = row
    public = [r["source_symbol"] for r in records if r["role"] == "source-public"]
    private = [r["source_symbol"] for r in records if r["role"] == "compiler-private"]
    if provenance.get("public_source_symbols") != public:
        raise RequestProjectionError("Public symbol inventory conflicts with variable records")
    if provenance.get("compiler_private_symbols") != private:
        raise RequestProjectionError("Private symbol inventory conflicts with variable records")
    return by_symbol


def _observation_block(text: str):
    """Find the exact JSON observation list in the current public request form."""
    if not isinstance(text, str):
        raise RequestProjectionError("context.observations must be a string")
    marker = re.search(r"zero-based array shapes\s*:\s*", text, flags=re.IGNORECASE)
    if marker is None:
        raise RequestProjectionError("Unrecognized observation instruction format")
    start = marker.end()
    try:
        rows, relative_end = json.JSONDecoder().raw_decode(text[start:])
    except json.JSONDecodeError as exc:
        raise RequestProjectionError("Observation list is not valid JSON") from exc
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        raise RequestProjectionError("Observation list must be a JSON array of objects")
    end = start + relative_end
    return rows, start, end


def _indices_for_shape(shape):
    if not isinstance(shape, list) or any(type(size) is not int or size < 0 for size in shape):
        raise RequestProjectionError("Observation shape must be a list of nonnegative integers")
    if not shape:
        return [[]]
    return [list(index) for index in itertools.product(*(range(size) for size in shape))]


def _project_one_observable(observable, entity, by_symbol, provenance):
    name = observable.get("name")
    shape = observable.get("shape")
    if not isinstance(name, str) or entity.get("name") != name:
        raise RequestProjectionError("Observation name lacks an exact provenance entity")
    if entity.get("shape") != shape:
        raise RequestProjectionError("Observation shape differs from runtime entity: " + name)
    elements = entity.get("elements")
    if not isinstance(elements, list) or not elements:
        raise RequestProjectionError("Cannot establish ownership of an empty/malformed observable: " + name)
    expected_indices = _indices_for_shape(shape)
    actual_indices = [row.get("index") for row in elements]
    if actual_indices != expected_indices:
        raise RequestProjectionError("Runtime entity indices do not match the requested dense shape: " + name)

    selected_records = []
    meta_elements = []
    roles = set()
    for element in elements:
        symbol = element.get("source_symbol")
        record = by_symbol.get(symbol)
        if record is None or record.get("entity") != name or record.get("index") != element.get("index"):
            raise RequestProjectionError("Entity element does not match variable provenance: " + str(symbol))
        if element.get("role") != record.get("role"):
            raise RequestProjectionError("Entity and variable role records disagree: " + str(symbol))
        roles.add(record["role"])
        selected_records.append(record)
        meta_elements.append({"symbol": symbol, "index": element["index"]})
    if len(roles) != 1:
        raise RequestProjectionError("Mixed public/private ownership within an observable is unsupported: " + name)
    if observable.get("sort") == "Int":
        if any(record.get("pycsp3_type") not in ("TypeVar.INTEGER", "INTEGER", "Int", "integer")
               for record in selected_records):
            raise RequestProjectionError("Runtime variable type does not support requested Int sort: " + name)
    elif roles == {"compiler-private"}:
        raise RequestProjectionError("No verified PyCSP3 type mapping for private observable sort: " + name)

    # Reuse the canonical role validation/filtering path. Restrict the inventory
    # to this exact observable so unrelated source-public decisions need not be
    # listed as requested outputs.
    public = [r["source_symbol"] for r in selected_records if r["role"] == "source-public"]
    private = [r["source_symbol"] for r in selected_records if r["role"] == "compiler-private"]
    subset = dict(schema=SCHEMA, pycsp3_version=PY_CSP3_VERSION,
                  variables=selected_records, public_source_symbols=public,
                  compiler_private_symbols=private)
    metadata = {"observables": [dict(name=name, shape=copy.deepcopy(shape), elements=meta_elements)]}
    projected = project_observables(metadata, subset)
    remaining = projected["observables"]
    if not remaining:
        return False, projected["source_projection"]
    if len(remaining) != 1 or len(remaining[0]["elements"]) != len(elements):
        raise RequestProjectionError("Projection only partially retained observable: " + name)
    return True, projected["source_projection"]


def project_request_bytes(raw_request: bytes, provenance: dict, binding: dict):
    """Return (new_request_bytes, ledger); input request/provenance are untouched."""
    try:
        request = json.loads(raw_request)
    except (TypeError, json.JSONDecodeError) as exc:
        raise RequestProjectionError("Request bytes are not a JSON object") from exc
    if not isinstance(request, dict):
        raise RequestProjectionError("Request must be a JSON object")
    _validate_binding(request, raw_request, provenance, binding)
    by_symbol = _validate_roles(provenance)

    entities = provenance.get("entities")
    if not isinstance(entities, list):
        raise RequestProjectionError("Provenance lacks a registered entity inventory")
    entity_by_name = {}
    for entity in entities:
        if not isinstance(entity, dict) or not isinstance(entity.get("name"), str):
            raise RequestProjectionError("Malformed entity provenance")
        if entity["name"] in entity_by_name:
            raise RequestProjectionError("Duplicate entity name in provenance")
        entity_by_name[entity["name"]] = entity

    context = request.get("context")
    if not isinstance(context, dict):
        raise RequestProjectionError("Request context must be an object")
    observations_text = context.get("observations")
    observations, start, end = _observation_block(observations_text)
    kept = []
    removed = []
    projections = []
    seen_names = set()
    for observation in observations:
        if not all(key in observation for key in ("name", "shape", "sort")):
            raise RequestProjectionError("Every observation must specify name, shape, and sort")
        name = observation["name"]
        if name in seen_names:
            raise RequestProjectionError("Duplicate observation name: " + str(name))
        seen_names.add(name)
        entity = entity_by_name.get(name)
        if entity is None:
            raise RequestProjectionError("Observation has no exact runtime entity evidence: " + str(name))
        retain, projection = _project_one_observable(observation, entity, by_symbol, provenance)
        projections.append(dict(name=name, projection=projection))
        if retain:
            kept.append(observation)
        else:
            removed.append(copy.deepcopy(observation))

    new_request = copy.deepcopy(request)
    new_observations = observations_text[:start] + json.dumps(kept, ensure_ascii=False) + observations_text[end:]
    new_request["context"]["observations"] = new_observations
    new_bytes = (json.dumps(new_request, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    ledger = dict(
        schema="induscp-nl-request-private-observation-projection-v1",
        case_id=request["id"],
        original_request_sha256=_sha(raw_request),
        projected_request_sha256=_sha(new_bytes),
        source_text_sha256=binding["source_text_sha256"],
        model_sha256=binding["model_sha256"],
        data_sha256=binding["data_sha256"],
        provenance_sha256=_canonical_sha(provenance),
        provenance_schema=SCHEMA,
        pycsp3_version=PY_CSP3_VERSION,
        removed_observations=removed,
        retained_observations=kept,
        element_projections=projections,
        source_text_changed=False,
        other_context_fields_changed=False,
        public_observation_order_preserved=True,
        shapes_and_sorts_preserved=True,
    )
    return new_bytes, ledger


def _cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", required=True)
    parser.add_argument("--provenance", required=True)
    parser.add_argument("--binding", required=True, help="Pinned id/request/source/model/data SHA256 JSON")
    parser.add_argument("--output-request", required=True)
    parser.add_argument("--output-ledger", required=True)
    args = parser.parse_args()
    raw = Path(args.request).read_bytes()
    provenance = json.loads(Path(args.provenance).read_text(encoding="utf-8"))
    binding = json.loads(Path(args.binding).read_text(encoding="utf-8"))
    projected, ledger = project_request_bytes(raw, provenance, binding)
    # Refuse overwrite for both artifacts; callers should use a new attempt dir.
    with Path(args.output_request).open("xb") as stream:
        stream.write(projected)
    with Path(args.output_ledger).open("x", encoding="utf-8") as stream:
        json.dump(ledger, stream, ensure_ascii=False, sort_keys=True, indent=2)
        stream.write("\n")


if __name__ == "__main__":
    _cli()
