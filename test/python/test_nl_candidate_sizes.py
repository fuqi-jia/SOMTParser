"""Candidates survive saving/loading without changing their interpretation."""
import json
import pytest
import somtparser as sp
from somtparser.natural_language import Candidate, ModelError, MAX_MODEL_JSON, MAX_ENVELOPE_JSON


def model():
    return dict(schema='somt-hir-model-v1',language='hir',decision='satisfiability',
                declarations=[],functions=[],constraints=[],objectives=[],
                objective_order='single',goal=None,assumptions=[],unresolved=[])


def test_large_semantic_metadata_and_legacy_indentation_roundtrip():
    raw=model()
    raw['assumptions']=['Explicit convention '+str(i)+': '+'x'*70 for i in range(14000)]
    candidate=sp.propose_nl('x',language='hir',provider=lambda request:raw)
    assert candidate.valid
    assert len(candidate.model_json)>1048576
    saved=candidate.to_json()
    assert '\n' not in saved
    for text in [saved,json.dumps(json.loads(saved),indent=8)]:
        restored=Candidate.from_json(text)
        assert restored.valid and restored.digest==candidate.digest
        assert restored.model==candidate.model


def test_loading_checks_component_budget_after_envelope_decoding():
    raw=model();candidate=sp.propose_nl('x',language='hir',provider=lambda request:raw)
    payload=json.loads(candidate.to_json())
    payload['model']['assumptions']=['x'*MAX_MODEL_JSON]
    # Hash integrity remains checked before candidate compilation.
    with pytest.raises(ModelError,match='digest mismatch'):
        Candidate.from_json(json.dumps(payload))
    # A provider returns the model only; context is attached by propose_nl.
    payload['model'].pop('context',None)
    with pytest.raises(ModelError,match='16 Mi-character'):
        sp.propose_nl('x',language='hir',provider=lambda request:payload['model'])


def test_envelope_wire_budget_and_duplicate_fields_still_checked():
    with pytest.raises(ModelError,match='48 Mi-character'):
        Candidate.from_json(' '*(MAX_ENVELOPE_JSON+1))
    with pytest.raises(ModelError,match='duplicate JSON field'):
        Candidate.from_json('{"schema":1,"schema":2}')
