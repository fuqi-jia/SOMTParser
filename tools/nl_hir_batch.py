"""Build source-only HIR generation batches and seal locally validated outputs.

This utility uses the public ``hir_schema()``, ``hir_api()`` and ``build_hir()`` interfaces;
it makes no provider, solver, or reference calls.
"""
from __future__ import annotations

import hashlib
import json
import argparse
from pathlib import Path
import tarfile

from somtparser.hir import ModelError, build_hir, hir_api, hir_schema


class BatchPackageError(ValueError):
    """A malformed request or generated response rejected before sealing."""


def _canonical(value) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False).encode("utf-8")


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _dump(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, sort_keys=True,
                               indent=2, allow_nan=False) + "\n", encoding="utf-8")


def _source_line_spans(source: str) -> list[list[int]]:
    spans = []
    offset = 0
    for line in source.splitlines(keepends=True):
        if line.strip():
            spans.append([offset, offset + len(line.rstrip("\r\n"))])
        offset += len(line)
    return spans


def _response_envelope_schema(ident: str) -> dict:
    # The HIR schema has root-relative $refs. Keep it separate instead of
    # nesting it under properties.model and silently breaking those references.
    return {
        "type": "object", "additionalProperties": False,
        "required": ["id", "model", "modeling_notes"],
        "properties": {
            "id": {"const": ident},
            "model": {"type": "object", "not": {"required": ["context"]}},
            "modeling_notes": {"type": "string"},
        },
    }


def build_request_package(source_cases: list[dict]) -> dict:
    """Attach the complete live schema and operator catalog to each source case."""
    if not isinstance(source_cases, list) or not source_cases:
        raise BatchPackageError("source_cases must be a nonempty list")
    schema = hir_schema()
    catalog = hir_api()
    requests = []
    seen = set()
    for index, case in enumerate(source_cases):
        if not isinstance(case, dict):
            raise BatchPackageError(f"case {index}: expected object")
        ident, source = case.get("id"), case.get("source")
        context = case.get("context", {})
        if not isinstance(ident, str) or not ident or ident in seen:
            raise BatchPackageError(f"case {index}: id must be a unique nonempty string")
        if not isinstance(source, str) or not source.strip():
            raise BatchPackageError(f"{ident}: source must be nonempty text")
        if not isinstance(context, dict) or any(
            not isinstance(key, str) or not isinstance(value, str)
            for key, value in context.items()
        ):
            raise BatchPackageError(f"{ident}: context must map strings to strings")
        seen.add(ident)
        requests.append({
            "id": ident,
            "source": source,
            "source_sha256": _sha(source.encode("utf-8")),
            "source_length": len(source),
            "source_line_spans": _source_line_spans(source),
            "context": context,
            "hir_schema": schema,
            "operator_catalog": catalog,
            "response_envelope_schema": _response_envelope_schema(ident),
            "instruction": (
                "Return exactly one JSON object with fields id, model, modeling_notes. "
                "Follow response_envelope_schema: id is the given string; modeling_notes "
                "is a string, never an object or array. "
                "The model must satisfy the complete hir_schema and use the supplied "
                "operator_catalog. Keep context outside the model; the caller attaches it. "
                "Every constraint, objective, defined function and goal must cite a nonempty "
                "half-open Unicode code-point source span [start,end], with "
                "0 <= start < end <= source_length. Reuse source_line_spans when the "
                "requirement is on that line; use a wider span for a requirement that "
                "covers multiple lines. Never use [0,0] or UTF-8 byte offsets. "
                "Preserve source/context requirements, do not invent constraints, bounds, "
                "or objectives, and record genuine ambiguity in unresolved. Declarations, "
                "functions, datatype constructors and selectors share one global name namespace; "
                "declare each context observable exactly once with its stated sort and shape. "
                "Bool declarations need no lower/upper bounds; numeric bounds such as 0/1 "
                "are invalid for Bool. Use ite(b, 1, 0) with Int literals when counting "
                "Boolean choices. Availability means a choice is permitted: encode "
                "chosen implies available, never assert every available choice. For "
                "conditional comparisons, write the implication explicitly and check its "
                "direction (higher rating implies more units). Zero-based array indices "
                "do not change source labels stored in the array, such as bowl numbers "
                "or participant identifiers. A closest-to-target objective is absolute "
                "deviation unless the source separately forbids exceeding the target. "
                "The goal field is only the source-linked conclusion expression for decision=validity. "
                "If context requires a Bool somt_goal observable for satisfiability, declare it once, "
                "constrain it equal to the formalized conclusion, and keep goal null. For related "
                "association arrays, state a consistent row key and the meaning/direction of each "
                "array; inverse encodings are allowed when they preserve all source/context relations, "
                "using channeling constraints where needed. Do not guess when materially different "
                "mappings remain possible. Never erase unresolved solely to pass validation: a model "
                "with unresolved items is intentionally not sealable pending review. Return no markdown."
                + " " + catalog["semantics"]["source_modeling"]
            ),
        })
    return {"schema": "nl-hir-generation-requests-v2",
            "denominator": len(requests), "requests": requests}


def _validate_request(request: dict, schema=None, catalog=None) -> None:
    if not isinstance(request, dict):
        raise BatchPackageError("request entry must be an object")
    ident = request.get("id", "<unknown>")
    source = request.get("source")
    if not isinstance(ident, str) or not ident:
        raise BatchPackageError("request id must be a nonempty string")
    if not isinstance(source, str) or not source.strip():
        raise BatchPackageError(f"{ident}: request source must be nonempty text")
    if request.get("source_sha256") != _sha(source.encode("utf-8")):
        raise BatchPackageError(f"{ident}: request source hash mismatch")
    # Existing immutable v2 requests predate these optional generation aids.
    # When present, verify them against the exact source before using them.
    for key, expected in {
        "source_length": len(source),
        "source_line_spans": _source_line_spans(source),
        "response_envelope_schema": _response_envelope_schema(ident),
    }.items():
        if key in request and request[key] != expected:
            raise BatchPackageError(f"{ident}: request {key} differs from source/response contract")
    if not isinstance(request.get("context", {}), dict) or any(
        not isinstance(key, str) or not isinstance(value, str)
        for key, value in request.get("context", {}).items()
    ):
        raise BatchPackageError(f"{ident}: request context must map strings to strings")
    schema = hir_schema() if schema is None else schema
    catalog = hir_api() if catalog is None else catalog
    if request.get("hir_schema") != schema:
        raise BatchPackageError(f"{ident}: request HIR schema differs from live API")
    if request.get("operator_catalog") != catalog:
        raise BatchPackageError(f"{ident}: request operator catalog differs from live API")


def validate_output(request: dict, output: dict, *, schema=None, catalog=None) -> dict:
    """Validate envelope and construct native HIR nodes without translating/solving."""
    _validate_request(request, schema, catalog)
    ident = request["id"]
    if not isinstance(output, dict) or set(output) != {"id", "model", "modeling_notes"}:
        raise BatchPackageError(f"{ident}: output must have exactly id/model/modeling_notes")
    if output["id"] != ident or not isinstance(output["modeling_notes"], str):
        raise BatchPackageError(f"{ident}: output identity or modeling_notes type mismatch")
    model = output["model"]
    if not isinstance(model, dict) or "context" in model:
        raise BatchPackageError(f"{ident}: model must be an object; context must be omitted")
    try:
        # Match propose_nl: caller-owned public context is attached only after
        # generation, on a disposable model copy, so the stored model stays raw.
        validation_model = dict(model)
        validation_model["context"] = request.get("context", {})
        build_hir(validation_model, request["source"])
    except (ModelError, ValueError, TypeError, KeyError, RecursionError) as exc:
        raise BatchPackageError(f"{ident}: HIR validation failed: {exc}") from exc
    return model


def seal_outputs(request_package: dict, outputs: list[dict], destination: Path) -> dict:
    """Validate every response first, then write an immutable output manifest."""
    if destination.exists():
        raise BatchPackageError(f"refusing to overwrite existing seal: {destination}")
    if not isinstance(request_package, dict):
        raise BatchPackageError("request package must be an object")
    requests = request_package.get("requests")
    if (request_package.get("schema") != "nl-hir-generation-requests-v2"
            or not isinstance(requests, list)
            or not requests
            or request_package.get("denominator") != len(requests)
            or not isinstance(outputs, list) or len(outputs) != len(requests)):
        raise BatchPackageError("request/output denominator or package schema mismatch")

    live_schema, live_catalog = hir_schema(), hir_api()
    prepared = []
    seen = set()
    for index, (request, output) in enumerate(zip(requests, outputs)):
        model = validate_output(request, output, schema=live_schema, catalog=live_catalog)
        ident = request["id"]
        if ident in seen:
            raise BatchPackageError(f"duplicate request id: {ident}")
        seen.add(ident)
        raw = _canonical(output) + b"\n"
        prepared.append((index, ident, model, raw, _sha(_canonical(request))))

    destination.mkdir(parents=True)
    rows = []
    for index, ident, _model, raw, request_hash in prepared:
        path = destination / f"{index}.json"
        path.write_bytes(raw)
        rows.append({"index": index, "id": ident,
                     "request_sha256": request_hash,
                     "output_sha256": _sha(raw), "output_bytes": len(raw)})
    manifest = {"schema": "nl-hir-validated-generation-seal-v2",
                "denominator": len(rows), "api_calls": 0,
                "validation": "exact envelope and public build_hir construction validation; no translation/solver",
                "cases": rows}
    _dump(destination / "manifest.json", manifest)
    with tarfile.open(destination / "validated-outputs.tar.gz", "w:gz") as archive:
        archive.add(destination / "manifest.json", arcname="manifest.json")
        for index, *_rest in prepared:
            archive.add(destination / f"{index}.json", arcname=f"outputs/{index}.json")
    return manifest


def prepare_file(source_file: Path, destination: Path) -> dict:
    """Read a source/context JSON package and write generation requests."""
    if destination.exists():
        raise BatchPackageError(f"refusing to overwrite existing request package: {destination}")
    source_package = json.loads(source_file.read_text(encoding="utf-8"))
    cases = source_package.get("cases") if isinstance(source_package, dict) else None
    package = build_request_package(cases)
    destination.mkdir(parents=True)
    _dump(destination / "requests.json", package)
    _dump(destination / "hir-schema.json", hir_schema())
    _dump(destination / "operator-catalog.json", hir_api())
    manifest = {"schema": "nl-hir-generation-package-v2",
                "source_package_sha256": _sha(source_file.read_bytes()),
                "requests_sha256": _sha((destination / "requests.json").read_bytes()),
                "hir_schema_sha256": _sha(_canonical(hir_schema())),
                "operator_catalog_sha256": _sha(_canonical(hir_api())),
                "denominator": package["denominator"], "api_calls": 0,
                "cases": [{"index": index, "id": request["id"],
                           "source_sha256": request["source_sha256"],
                           "request_sha256": _sha(_canonical(request))}
                          for index, request in enumerate(package["requests"])]}
    _dump(destination / "manifest.json", manifest)
    return manifest


def seal_file(requests_file: Path, output_dir: Path, destination: Path) -> dict:
    """Load JSON response files named by request index and seal after validation."""
    package = json.loads(requests_file.read_text(encoding="utf-8"))
    requests = package.get("requests") if isinstance(package, dict) else None
    if not isinstance(requests, list):
        raise BatchPackageError("request file must contain a requests array")
    outputs = []
    for index in range(len(requests)):
        path = output_dir / f"{index}.json"
        try:
            outputs.append(json.loads(path.read_text(encoding="utf-8")))
        except (OSError, json.JSONDecodeError) as exc:
            raise BatchPackageError(f"cannot read valid JSON output {path}: {exc}") from exc
    return seal_outputs(package, outputs, destination)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    prepare = subparsers.add_parser("prepare", help="package public-schema source requests")
    prepare.add_argument("--source-package", type=Path, required=True)
    prepare.add_argument("--destination", type=Path, required=True)
    seal = subparsers.add_parser("seal", help="validate and freeze model outputs")
    seal.add_argument("--requests", type=Path, required=True)
    seal.add_argument("--outputs", type=Path, required=True)
    seal.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args(argv)
    if args.command == "prepare":
        result = prepare_file(args.source_package, args.destination)
    else:
        result = seal_file(args.requests, args.outputs, args.destination)
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BatchPackageError as exc:
        raise SystemExit(str(exc)) from exc
