"""Live capability views preserve envelopes while retrieving only selected help."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "skills/somtparser-nl-smtlib/scripts"))
import capability_pack as packs
from candidate_protocol import schema_with_source_anchors
from smt_bridge import request_for

SOURCE = "Choose integer x with x >= 4."
CONTEXT = {"x": "unknown integer, not an omitted input"}


def request(route="hir"):
    value = request_for(SOURCE, CONTEXT, "hir" if route == "hybrid" else route)
    if route == "hybrid":
        hir = value["schema"]
        definitions = hir.pop("$defs")
        value["language"] = "hybrid"
        value["schema"] = {
            "$defs": definitions, "type": "object", "additionalProperties": False,
            "required": ["schema", "hir", "smt_constraints"],
            "properties": {"schema": {"const": "somt-nl-hybrid-v1"}, "hir": hir,
                "smt_constraints": {"type": "array", "items": {
                    "type": "object", "required": ["span", "term"],
                    "properties": {"span": {"type": "array", "items": {"type": "integer"}},
                                   "term": {"type": "string"}}, "additionalProperties": False}}},
        }
    value["schema"] = schema_with_source_anchors(value["schema"], route)
    return value


def candidate(expr=None):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=[{"name": "x", "sort": "Int"}], functions=[],
                constraints=[{"expr": {"literal": True, "sort": "Bool"} if expr is None else expr,
                              "span": {"quote": "x >= 4"}}],
                objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])


def valid(value, packet):
    import jsonschema
    jsonschema.Draft202012Validator.check_schema(packet["request"]["schema"])
    validator = jsonschema.Draft202012Validator(packet["request"]["schema"])
    errors = list(validator.iter_errors(value))
    assert not errors, "\n".join(error.message[:300] for error in errors)


@pytest.mark.parametrize("route", ["hir", "smtlib2", "hybrid"])
def test_catalog_combines_live_api_and_document_ids(route):
    native = request(route)
    index = packs.capability_index(route, native)
    names = [item["id"] for item in index]
    assert len(names) == len(set(names))
    assert {"core", "arithmetic", "arrays", "cp.no_overlap", "cp.table", "semantics.core",
            "domain.linear", "domain.cp", "domain.fol", "macros", "template", "repair",
            "dialect.z3", "dialect.optimathsat"} <= set(names)
    assert all(item["description"] and item["kind"] in ("api", "document") for item in index)


@pytest.mark.parametrize("route", ["hir", "smtlib2", "hybrid"])
def test_core_contract_example_compiles_to_its_exact_relation(route):
    import z3
    from ir2smt import get_request, render
    example = packs.materialize_capabilities(route, [], request(route))["request"]["candidate_contract_example"]
    source, model = example["source"], example["candidate"]
    packet = packs.materialize_capabilities(route, [], get_request(source, {}, route))
    valid(model, packet)
    output = render(source, model, route=route)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(output["code"])), z3.Int("u") == 2))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("route", ["hir", "hybrid"])
def test_small_views_preserve_complete_envelope_context_and_root_refs(route):
    native = request(route)
    before = deepcopy(native)
    packet = packs.materialize_capabilities(route, ["arithmetic", "bool"], native)
    selected = packet["request"]
    assert selected["request_profile"] == "capability-view"
    assert native == before
    for key in ("source", "source_sha256", "context", "language"):
        assert selected[key] == native[key]
    old = native["schema"]["properties"]["hir"] if route == "hybrid" else native["schema"]
    new = selected["schema"]["properties"]["hir"] if route == "hybrid" else selected["schema"]
    assert old["required"] == new["required"]
    assert set(old["properties"]) == set(new["properties"])
    assert "constructor_api" not in new
    assert len(packs.canonical(selected)) < len(packs.canonical(native)) * 0.5
    value = candidate({"op": "ge", "args": [{"var": "x"}, {"literal": 4, "sort": "Int"}]})
    if route == "hybrid":
        value = {"schema": "somt-nl-hybrid-v1", "hir": value,
                 "smt_constraints": [{"span": {"quote": "x >= 4"}, "term": "(>= x 4)"}]}
    valid(value, packet)


def test_core_is_implicit_and_other_capabilities_are_not():
    packet = packs.materialize_capabilities("hir", [], request())
    assert packet["loaded"] == ["core"]
    valid(candidate(), packet)
    serialized = packs.canonical(packet["request"])
    assert "no_overlap" not in serialized and "bvadd" not in serialized
    assert "cp_vector" not in packet["request"]["schema"]["$defs"]


def test_later_lookup_adds_selected_capabilities_without_loading_all():
    native = request()
    initial = packs.materialize_capabilities("hir", ["arithmetic"], native)
    extended = packs.materialize_capabilities("hir", initial["loaded"] + ["cp.table"], native)
    assert set(extended["loaded"]) == {"core", "arithmetic", "cp.table"}
    assert set(extended["request"]["loaded_constructor_api"]["cp_constructors"]["constructors"]) == {"table"}
    assert "no_overlap" not in packs.canonical(extended["request"])
    assert "add" in extended["request"]["loaded_constructor_api"]["operations"]
    valid(candidate({"cp": "table", "items": [{"var": "x"}], "tuples": [[4]], "positive": True}), extended)


@pytest.mark.parametrize("capability, expr, declaration", [
    ("bitvectors", {"op": "eq", "args": [{"op": "bvadd", "args": [{"var": "x"}, {"literal": "#x01", "sort": {"BitVec": 8}}]},
                                             {"literal": "#x05", "sort": {"BitVec": 8}}]}, {"name": "x", "sort": {"BitVec": 8}}),
    ("quantifiers", {"quantifier": "forall", "binders": [{"name": "y", "sort": "Bool"}], "body": {"op": "eq", "args": [{"var": "y"}, {"var": "y"}]}}, {"name": "x", "sort": "Int"}),
    ("folds", {"fold": "forall", "var": "i", "range": [0, 3], "body": {"literal": True, "sort": "Bool"}}, {"name": "x", "sort": "Int"}),
    ("arrays", {"op": "eq", "args": [{"at": "x", "indices": [{"literal": 0, "sort": "Int"}]}, {"literal": 4, "sort": "Int"}]}, {"name": "x", "sort": {"Array": ["Int", "Int"]}}),
    ("strings", {"op": "eq", "args": [{"op": "str.len", "args": [{"var": "x"}]}, {"literal": 4, "sort": "Int"}]}, {"name": "x", "sort": "String"}),
])
def test_capability_view_is_not_a_claim_of_native_unsupported(capability, expr, declaration):
    import jsonschema
    native = request()
    value = candidate(expr)
    value["declarations"] = [declaration]
    core = packs.materialize_capabilities("hir", [], native)
    assert list(jsonschema.Draft202012Validator(core["request"]["schema"]).iter_errors(value))
    selected = packs.materialize_capabilities("hir", [capability], native)
    valid(value, selected)
    assert selected["request"]["capability_view"]["native_support_unchanged"] is True


@pytest.mark.parametrize("route", ["hir", "smtlib2", "hybrid"])
def test_documents_are_materialized_only_when_requested_and_hashed(route):
    native = request(route)
    packet = packs.materialize_capabilities(route, ["template", "semantics.core"], native)
    documents = packet["request"]["loaded_resources"]
    assert [item["id"] for item in documents] == ["semantics.core", "template"]
    for item in documents:
        assert item["sha256"] == hashlib.sha256(item["text"].encode()).hexdigest()
    assert "Repair" not in " ".join(item["text"] for item in documents)
    assert packs.materialize_capabilities(route, [], native)["request"]["loaded_resources"] == []


def test_direct_smt_route_retains_its_envelope_and_does_not_require_hir_json():
    native = request("smtlib2")
    packet = packs.materialize_capabilities("smtlib2", ["arithmetic", "cp.no_overlap"], native)
    assert packet["request"]["schema"] == native["schema"]
    assert "loaded_constructor_api" not in packet["request"]
    assert "arithmetic" in packet["request"]["loaded_smt_syntax"]
    assert "not SMT-LIB primitives" in packet["request"]["cp_reference_boundary"]
    assert set(packet["request"]["cp_semantic_reference"]["constructors"]) == {"no_overlap"}


def test_unknown_ids_never_trigger_automatic_broadening():
    native = request()
    before = deepcopy(native)
    with pytest.raises(ValueError, match="unknown capability IDs: all-theories, cp.imaginary"):
        packs.materialize_capabilities("hir", ["cp.imaginary", "all-theories"], native)
    assert native == before
    with pytest.raises(TypeError):
        packs.materialize_capabilities("hir", "arithmetic", native)


def test_packets_are_deterministic_and_hashes_bind_source_context_resources():
    native = request()
    first = packs.materialize_capabilities("hir", ["arithmetic", "bool", "arithmetic"], native)
    second = packs.materialize_capabilities("hir", ["bool", "arithmetic"], native)
    assert first == second
    unsigned = {key: value for key, value in first.items() if key != "packet_sha256"}
    assert first["packet_sha256"] == packs.digest(unsigned)
    changed = deepcopy(native)
    changed["context"]["x"] = "different source convention"
    assert packs.materialize_capabilities("hir", ["arithmetic", "bool"], changed)["packet_sha256"] != first["packet_sha256"]


def test_live_cp_catalog_change_is_visible_without_handwritten_schema_copy():
    native = request()
    cp = native["schema"]["constructor_api"]["cp_constructors"]["constructors"]
    del cp["no_overlap"]
    assert "cp.no_overlap" not in {item["id"] for item in packs.capability_index("hir", native)}
    with pytest.raises(ValueError, match="unknown capability"):
        packs.materialize_capabilities("hir", ["cp.no_overlap"], native)


def test_every_document_id_points_to_existing_resource_and_theory_views_are_valid_schemas():
    import jsonschema
    native = request()
    for identifier in packs.DOCUMENTS:
        packet = packs.materialize_capabilities("hir", [identifier], native)
        assert packet["request"]["loaded_resources"][0]["text"].strip()
    for identifier in packs.DESCRIPTIONS:
        packet = packs.materialize_capabilities("hir", [identifier], native)
        jsonschema.Draft202012Validator.check_schema(packet["request"]["schema"])


def test_cli_index_and_read_are_machine_readable(tmp_path, capsys):
    path = tmp_path / "request.json"
    path.write_text(json.dumps(request()), encoding="utf-8")
    assert packs.main(["index", "--route", "hir", "--request", str(path)]) == 0
    index = json.loads(capsys.readouterr().out)
    assert "cp.no_overlap" in {item["id"] for item in index}
    assert packs.main(["read", "--route", "hir", "--request", str(path),
                       "--ids", "core", "domain.cp", "cp.no_overlap"]) == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet["loaded"] == ["core", "cp.no_overlap", "domain.cp"]
    assert packet["request"]["source"] == SOURCE
    assert packs.main(["read", "--route", "hir", "--request", str(path), "--ids", "fake"]) == 2
    assert json.loads(capsys.readouterr().err)["status"] == "capability-error"
