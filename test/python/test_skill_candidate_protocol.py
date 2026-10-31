"""Exact anchors and schema feedback preserve candidate semantics and evidence."""
from copy import deepcopy
import builtins
import importlib.util
from pathlib import Path
import sys

import pytest

SCRIPTS = Path(__file__).resolve().parents[2] / "skills/somtparser-nl-smtlib/scripts"
sys.path.insert(0, str(SCRIPTS))
import candidate_protocol as protocol


def model():
    return {
        "schema": "somt-hir-model-v1", "language": "hir", "decision": "satisfiability",
        "declarations": [{"name": "x", "sort": "Int"}], "functions": [],
        "constraints": [{"span": {"quote": "x >= 4"},
                         "expr": {"op": "ge", "args": [{"var": "x"}, {"literal": 4, "sort": "Int"}]}}],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }


def test_unicode_offsets_and_immutable_evidence():
    source = "中文🙂，x >= 4；结束"
    original = model()
    before = deepcopy(original)
    result, ledger = protocol.resolve_source_spans(original, source, "hir")
    assert original == before
    assert result["constraints"][0]["span"] == [4, 10]
    assert source[4:10] == "x >= 4"
    assert ledger == [{"path": "/constraints/0/span", "rule": "exact-source-quote",
                       "before": {"quote": "x >= 4"}, "after": [4, 10]}]
    result["constraints"][0]["expr"]["args"][0]["var"] = "other"
    ledger[0]["after"][0] = 100
    assert original == before
    assert result["constraints"][0]["span"] == [4, 10]


def test_repeated_quote_needs_explicit_zero_based_occurrence():
    source = "中文x >= 4；x >= 4"
    value = model()
    with pytest.raises(protocol.SourceAnchorError, match="quote repeats") as caught:
        protocol.resolve_source_spans(value, source, "hir")
    assert caught.value.pointer == "/constraints/0/span"
    value["constraints"][0]["span"]["occurrence"] = 1
    result, _ = protocol.resolve_source_spans(value, source, "hir")
    assert result["constraints"][0]["span"] == [9, 15]


def test_overlapping_occurrences_are_explicit():
    value = model()
    value["constraints"][0]["span"] = {"quote": "aa", "occurrence": 1}
    result, _ = protocol.resolve_source_spans(value, "aaa", "hir")
    assert result["constraints"][0]["span"] == [1, 3]


@pytest.mark.parametrize("anchor, message", [
    ({"quote": ""}, "nonempty"),
    ({"quote": 4}, "nonempty"),
    ({"quote": "missing"}, "does not occur"),
    ({"quote": "x >= 4", "occurrence": True}, "nonnegative integer"),
    ({"quote": "x >= 4", "occurrence": 1.0}, "nonnegative integer"),
    ({"quote": "x >= 4", "occurrence": -1}, "nonnegative integer"),
    ({"quote": "x >= 4", "occurrence": None}, "nonnegative integer"),
    ({"quote": "x >= 4", "occurrence": 1}, "out of range"),
    ({"quote": "x >= 4", "unapproved": "x"}, "optional occurrence only"),
    ({"start": 0, "end": 6}, "optional occurrence only"),
])
def test_invalid_anchors_are_rejected_without_inference(anchor, message):
    value = model()
    value["constraints"][0]["span"] = anchor
    before = deepcopy(value)
    with pytest.raises(protocol.SourceAnchorError, match=message):
        protocol.resolve_source_spans(value, "x >= 4", "hir")
    assert value == before


def test_quote_matching_does_not_normalize_unicode_or_whitespace():
    value = model()
    value["constraints"][0]["span"] = {"quote": "é"}
    with pytest.raises(protocol.SourceAnchorError, match="does not occur"):
        protocol.resolve_source_spans(value, "e\u0301", "hir")


@pytest.mark.parametrize("span", [[-1, 900], [True, False], [1], None, "x >= 4"])
def test_non_anchor_spans_remain_for_native_validation(span):
    value = model()
    value["constraints"][0]["span"] = span
    result, ledger = protocol.resolve_source_spans(value, "x >= 4", "hir")
    assert result == value and ledger == []


def test_all_permitted_hir_link_positions_and_literal_data():
    value = model()
    entry = {"span": {"quote": "x >= 4"}}
    value.update(functions=[deepcopy(entry)], objectives=[deepcopy(entry)],
                 soft_constraints=[deepcopy(entry)], goal=deepcopy(entry))
    untouched = {"span": {"quote": "not in source"}, "quote": "not in source",
                 "macro": "not a macro", "nested": [deepcopy(entry)]}
    value["data"] = deepcopy(untouched)
    value["declarations"][0]["span"] = {"quote": "not in source"}
    value["constraints"][0]["expr"]["span"] = {"quote": "not in source"}
    result, ledger = protocol.resolve_source_spans(value, "x >= 4", "hir")
    assert {row["path"] for row in ledger} == {
        "/constraints/0/span", "/soft_constraints/0/span", "/objectives/0/span",
        "/functions/0/span", "/goal/span"}
    assert result["data"] == untouched
    assert result["declarations"] == value["declarations"]
    assert result["constraints"][0]["expr"] == value["constraints"][0]["expr"]


def test_direct_links_only():
    value = {"links": [{"span": {"quote": "x >= 4"}, "fragment": "(>= x 4)"}],
             "program": "literal text", "data": {"span": {"quote": "missing"}}}
    result, ledger = protocol.resolve_source_spans(value, "x >= 4", "smtlib2")
    assert result["links"] == [{"span": [0, 6], "fragment": "(>= x 4)"}]
    assert result["data"] == value["data"]
    assert ledger[0]["path"] == "/links/0/span"


def test_hybrid_resolves_hir_goal_and_extension_spans():
    hir = model()
    hir["goal"] = deepcopy(hir["constraints"][0])
    value = {"schema": "somt-nl-hybrid-v1", "hir": hir,
             "smt_constraints": [{"span": {"quote": "x >= 4"}, "term": "(>= x 4)"}]}
    result, ledger = protocol.resolve_source_spans(value, "x >= 4", "hybrid")
    assert result["hir"]["goal"]["span"] == [0, 6]
    assert result["smt_constraints"][0]["span"] == [0, 6]
    assert {item["path"] for item in ledger} == {
        "/hir/goal/span", "/hir/constraints/0/span", "/smt_constraints/0/span"}


def test_augmentation_preserves_root_refs_and_unrelated_data_contract():
    jsonschema = pytest.importorskip("jsonschema")
    span = {"type": "array", "items": {"type": "integer"}, "minItems": 2, "maxItems": 2}
    entry = {"type": "object", "properties": {"span": {"$ref": "#/$defs/span"},
             "expr": {"$ref": "#/$defs/expr"}}, "required": ["span", "expr"]}
    schema = {"$defs": {"span": span, "expr": {"type": "boolean"}, "entry": entry},
              "type": "object", "properties": {
                  "hir": {"type": "object", "properties": {
                      "constraints": {"type": "array", "items": {"$ref": "#/$defs/entry"}},
                      "goal": {"oneOf": [{"type": "null"}, {"$ref": "#/$defs/entry"}]},
                      "data": {"type": "object", "properties": {"span": span}}}},
                  "smt_constraints": {"type": "array", "items": {
                      "type": "object", "properties": {"span": span}}}}}
    before = deepcopy(schema)
    augmented = protocol.schema_with_source_anchors(schema, "hybrid")
    assert schema == before and augmented["$defs"] == before["$defs"]
    assert augmented["properties"]["hir"]["properties"]["data"] == before["properties"]["hir"]["properties"]["data"]
    value = {"hir": {"constraints": [{"span": {"quote": "ok"}, "expr": True}],
                     "goal": {"span": {"quote": "ok", "occurrence": 0}, "expr": False}},
             "smt_constraints": [{"span": {"quote": "ok"}}]}
    jsonschema.validate(value, augmented)
    value["hir"]["constraints"][0]["expr"] = "wrong"
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(value, augmented)


def test_live_schema_allows_only_source_positions_and_is_idempotent():
    pytest.importorskip("jsonschema")
    from somtparser.hir import hir_schema
    schema = hir_schema()
    before = deepcopy(schema)
    augmented = protocol.schema_with_source_anchors(schema, "hir")
    assert protocol.schema_with_source_anchors(augmented, "hir") == augmented
    assert protocol.schema_diagnostics(model(), augmented) == []
    assert schema == before
    value = model()
    value["declarations"][0]["span"] = {"quote": "x >= 4"}
    diagnostics = protocol.schema_diagnostics(value, augmented)
    assert any(item["pointer"] == "/declarations/0/span" for item in diagnostics)


def test_schema_feedback_collects_missing_illegal_fields_and_fake_operator():
    pytest.importorskip("jsonschema")
    from somtparser.hir import hir_schema
    value = model()
    value.pop("decision")
    value.pop("functions")
    value["declarations"][0]["span"] = [0, 6]
    value["constraints"][0]["expr"] = {"op": "var", "args": ["x"]}
    before = deepcopy(value)
    diagnostics = protocol.schema_diagnostics(value, protocol.schema_with_source_anchors(hir_schema(), "hir"))
    pointers = {entry["pointer"] for entry in diagnostics}
    assert {"/decision", "/functions", "/declarations/0/span", "/constraints/0/expr/op"} <= pointers
    assert any("variable reference" in entry["message"] for entry in diagnostics)
    assert all("schema_pointer" in entry for entry in diagnostics)
    assert value == before


def test_schema_diagnostics_are_bounded_and_sorted_with_json_pointer_escaping():
    pytest.importorskip("jsonschema")
    schema = {"type": "object", "required": ["z", "a/b", "a~b", "c"]}
    result = protocol.schema_diagnostics({}, schema, limit=2)
    assert len(result) == 2
    assert [item["pointer"] for item in result] == ["/a~0b", "/a~1b"]
    assert result[-1]["additional_diagnostics_omitted"] == 2
    with pytest.raises(ValueError):
        protocol.schema_diagnostics({}, schema, limit=True)


def test_optional_validator_absence_is_not_a_pass(monkeypatch):
    monkeypatch.setitem(sys.modules, "jsonschema", None)
    result = protocol.schema_diagnostics({}, {})
    assert result[0]["code"] == "SCHEMA_VALIDATOR_UNAVAILABLE"
    assert result[0]["severity"] == "warning"


def test_anchor_preprocessing_needs_only_stdlib(monkeypatch):
    original_import = builtins.__import__

    def guarded_import(name, *args, **kwargs):
        if name.split(".")[0] in ("somtparser", "z3", "jsonschema", "subprocess"):
            raise AssertionError("anchor preprocessing imported " + name)
        return original_import(name, *args, **kwargs)

    monkeypatch.setattr(builtins, "__import__", guarded_import)
    spec = importlib.util.spec_from_file_location("protocol_isolated", SCRIPTS / "candidate_protocol.py")
    isolated = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(isolated)
    result, ledger = isolated.resolve_source_spans(model(), "x >= 4", "hir")
    assert result["constraints"][0]["span"] == [0, 6] and len(ledger) == 1
