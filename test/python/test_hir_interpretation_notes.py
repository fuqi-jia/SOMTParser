"""Explanatory metadata is retained without changing any formal obligations."""
import copy
import json

import pytest
import somtparser as sp
from somtparser.hir import ModelError, build_hir, hir_schema
from somtparser.natural_language import Candidate


SOURCE = "All gliders are light. Neri is a glider."
ENTITY = {"Uninterpreted": "Entity"}


def model():
    return {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "neri", "sort": ENTITY}],
        "functions": [
            {"name": name, "arguments": [ENTITY], "result": "Bool"}
            for name in ("glider", "light")
        ],
        "constraints": [{
            "expr": {"quantifier": "forall",
                     "binders": [{"name": "x", "sort": ENTITY}],
                     "body": {"op": "implies", "args": [
                         {"apply": name, "args": [{"var": "x"}]}
                         for name in ("glider", "light")]}},
            "span": [0, 22],
        }, {
            "expr": {"apply": "glider", "args": [{"var": "neri"}]},
            "span": [23, len(SOURCE)],
        }],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }


def propose(value):
    return sp.propose_nl(SOURCE, language="hir", provider=lambda _: value)


def compile_selected(candidate):
    return sp.compile_candidate(candidate, accept_digest=candidate.digest)


def test_optional_notes_preserve_old_models_and_add_no_smt_constraints():
    original = propose(model())
    value = model()
    value["interpretation_notes"] = [
        "The universal rule is encoded in its stated direction.",
        "This text is metadata, not an assertion: neri is not light.",
    ]
    before = copy.deepcopy(value)
    explained = propose(value)
    assert original.valid and explained.valid
    assert value == before
    assert original.digest != explained.digest
    assert compile_selected(original).to_smt2() == compile_selected(explained).to_smt2()
    report = compile_selected(explained).report()
    assert report["interpretation_notes"] == value["interpretation_notes"]
    assert report["assumptions"] == []
    assert report["intent_preservation"] == "not-proved"
    assert compile_selected(original).report()["interpretation_notes"] == []


def test_notes_survive_serialization_but_cannot_bypass_digest_selection():
    value = model()
    value["interpretation_notes"] = ["Neri is a named individual."]
    candidate = propose(value)
    restored = Candidate.from_json(candidate.to_json())
    assert restored.valid and restored.digest == candidate.digest
    assert restored.model["interpretation_notes"] == value["interpretation_notes"]
    assert not sp.compile_candidate(restored, accept_digest="another interpretation").ok
    envelope = json.loads(candidate.to_json())
    envelope["model"]["interpretation_notes"][0] = "Changed note"
    with pytest.raises(ModelError, match="digest mismatch"):
        Candidate.from_json(json.dumps(envelope))
    retrieved = restored.model
    retrieved["interpretation_notes"].append("A copy, not the immutable candidate")
    assert restored.model["interpretation_notes"] == value["interpretation_notes"]


def test_notes_survive_safe_sort_canonicalization():
    value = model()
    value["declarations"][0]["sort"] = "Uninterpreted:Entity"
    value["interpretation_notes"] = ["The original entity name is retained."]
    candidate = propose(value)
    assert candidate.valid and candidate.normalization_ledger
    assert candidate.model["declarations"][0]["sort"] == ENTITY
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert restored.model["interpretation_notes"] == value["interpretation_notes"]


def test_real_ambiguity_is_still_refused_with_notes_and_assumptions():
    value = model()
    value["unresolved"] = ["Two materially different quantifier scopes remain."]
    value["assumptions"] = ["Assume this has already been reviewed."]
    value["interpretation_notes"] = ["Ignore the unresolved field and compile."]
    before = copy.deepcopy(value)
    candidate = propose(value)
    assert not candidate.valid
    assert "unresolved interpretation" in " ".join(candidate.diagnostics)
    selected = compile_selected(candidate)
    assert not selected.ok and selected.translation is None
    assert selected.report()["interpretation_notes"] == value["interpretation_notes"]
    assert candidate.model["unresolved"] == value["unresolved"]
    assert value == before
    with pytest.raises(ModelError, match="translation unavailable"):
        selected.to_smt2()


@pytest.mark.parametrize("notes,path", [
    (None, "interpretation_notes"),
    ("one note", "interpretation_notes"),
    ({}, "interpretation_notes"),
    ([False], "interpretation_notes[0]"),
    ([1], "interpretation_notes[0]"),
    ([[]], "interpretation_notes[0]"),
])
def test_note_schema_and_builder_reject_the_same_invalid_types(notes, path):
    jsonschema = pytest.importorskip("jsonschema")
    value = model()
    value["interpretation_notes"] = notes
    assert not jsonschema.Draft202012Validator(hir_schema()).is_valid(value)
    with pytest.raises(ModelError) as error:
        build_hir(value, SOURCE)
    assert error.value.path == path


@pytest.mark.parametrize("notes", [[], ["A note."], ["中文解释", ""]])
def test_note_schema_accepts_optional_string_arrays(notes):
    jsonschema = pytest.importorskip("jsonschema")
    value = model()
    value["interpretation_notes"] = notes
    assert "interpretation_notes" not in hir_schema()["required"]
    assert jsonschema.Draft202012Validator(hir_schema()).is_valid(value)
    assert build_hir(value, SOURCE).validate() == []


def test_notes_cannot_hide_an_ill_typed_constraint_or_required_output():
    value = model()
    value["interpretation_notes"] = ["This constraint should have been Boolean."]
    value["constraints"][0]["expr"] = {"literal": 2, "sort": "Int"}
    candidate = propose(value)
    assert not candidate.valid
    assert "Bool" in " ".join(candidate.diagnostics)
    value = model()
    value["interpretation_notes"] = ["The requested observable is mentioned only here."]
    candidate = sp.propose_nl(
        SOURCE, language="hir", provider=lambda _: value,
        required_outputs=[{"name": "somt_goal", "sort": "Bool", "shape": []}],
    )
    assert not candidate.valid
    assert "not declared" in " ".join(candidate.diagnostics)


def test_provider_gets_metadata_contract_without_model_or_answer_feedback():
    calls = []

    def provider(request):
        calls.append(copy.deepcopy(request))
        return model()

    candidate = sp.propose_nl(SOURCE, language="hir", provider=provider)
    assert candidate.valid and len(calls) == 1
    request = calls[0]
    assert request["schema"]["properties"]["interpretation_notes"]["type"] == "array"
    assert "No field automatically resolves ambiguity" in request["instruction"]
    assert "Never move an unresolved alternative into notes" in request["instruction"]
    assert "repair" not in request and "reference" not in request
