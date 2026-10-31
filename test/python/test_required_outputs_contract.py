"""Optional caller-owned HIR output signatures; no benchmark inference."""
import copy

import pytest
import somtparser as sp
from somtparser.natural_language import Candidate, ModelError


SOURCE = "Choose a Boolean vector x with two entries."
OUTPUTS = [{"name": "x", "sort": "Bool", "shape": [2]}]


def model(shape=(2,), sort="Bool"):
    return dict(
        schema="somt-hir-model-v1",
        language="hir",
        decision="satisfiability",
        declarations=[{"name": "x", "sort": sort, "shape": list(shape)}],
        functions=[], constraints=[], objectives=[], objective_order="single",
        goal=None, assumptions=[], unresolved=[],
    )


def test_required_outputs_are_sent_checked_and_round_trip():
    seen = []

    def provider(request):
        seen.append(copy.deepcopy(request))
        return model()

    candidate = sp.propose_nl(
        SOURCE, language="hir", provider=provider, required_outputs=OUTPUTS
    )
    assert candidate.valid, candidate.diagnostics
    assert seen[0]["required_outputs"] == OUTPUTS
    assert candidate.required_outputs == OUTPUTS
    restored = Candidate.from_json(candidate.to_json())
    assert restored.valid
    assert restored.required_outputs == OUTPUTS
    assert restored.digest == candidate.digest


def test_direct_and_restored_contract_survives_acceptance_and_compile():
    from somtparser.natural_language import _canonical

    direct = Candidate(
        SOURCE, _canonical(model()), "manual", (),
        required_outputs_json=_canonical(OUTPUTS),
    )
    for candidate in (direct, Candidate.from_json(direct.to_json())):
        selected = sp.compile_candidate(candidate, accept_digest=candidate.digest)
        assert selected.ok, selected.diagnostics
        assert selected.candidate.required_outputs == OUTPUTS
        assert selected.candidate.digest == candidate.digest


def test_forged_candidate_without_diagnostics_is_rejected_against_contract():
    from somtparser.natural_language import _canonical

    forged = Candidate(
        SOURCE, _canonical(model(shape=(3,))), "manual", (),
        required_outputs_json=_canonical(OUTPUTS),
    )
    assert forged.valid
    selected = sp.compile_candidate(forged, accept_digest=forged.digest)
    assert not selected.ok
    assert selected.candidate.required_outputs == OUTPUTS
    assert any("required output 'x' has shape [3]; expected [2]" in diagnostic
               for diagnostic in selected.diagnostics)


def test_contract_normalization_is_detached_from_caller_nested_sort():
    from somtparser.natural_language import _normalize_required_outputs

    contract = [{"name": "x", "sort": {"Array": ["Int", {"BitVec": 2}]}, "shape": [2]}]
    normalized = _normalize_required_outputs(contract)
    contract[0]["sort"]["Array"][1]["BitVec"] = 3
    assert normalized[0]["sort"] == {"Array": ["Int", {"BitVec": 2}]}


def test_mismatch_is_diagnostic_without_rewriting_candidate_and_repair_sees_contract():
    calls = []

    def provider(request):
        calls.append(copy.deepcopy(request))
        if "repair" not in request:
            return model(shape=(3,), sort="Int")
        assert request["required_outputs"] == OUTPUTS
        assert request["repair"]["previous_candidate"]["declarations"][0] == {
            "name": "x", "sort": "Int", "shape": [3]
        }
        return model()

    trace = sp.propose_nl_with_repair(
        SOURCE, provider=provider, language="hir", required_outputs=OUTPUTS,
        max_attempts=2,
    )
    first, repaired = trace.attempts
    assert not first.valid
    assert first.model["declarations"][0]["shape"] == [3]
    assert first.model["declarations"][0]["sort"] == "Int"
    assert any("required output 'x' has shape [3]; expected [2]" in d
               for d in first.diagnostics)
    assert any("required output 'x' has sort 'Int'; expected 'Bool'" in d
               for d in first.diagnostics)
    assert repaired.valid
    assert calls[1]["required_outputs"] == OUTPUTS
    assert first.digest != repaired.digest


def test_omitted_contract_preserves_provider_request_shape():
    seen = []

    def provider(request):
        seen.append(request)
        return model()

    candidate = sp.propose_nl(SOURCE, language="hir", provider=provider)
    assert candidate.valid
    assert "required_outputs" not in seen[0]
    assert candidate.required_outputs == []
    assert "required_outputs" not in Candidate.from_json(candidate.to_json()).to_json()


@pytest.mark.parametrize("contract", [
    [{"name": "x", "sort": "Bool", "shape": [True]}],
    [{"name": "x", "sort": "Bool", "shape": [2]},
     {"name": "x", "sort": "Int", "shape": []}],
    [{"name": "x", "sort": "Bool"}],
])
def test_malformed_contract_is_rejected(contract):
    with pytest.raises(ModelError):
        sp.propose_nl(SOURCE, language="hir", provider=lambda _: model(),
                      required_outputs=contract)


def test_required_outputs_are_hir_only():
    with pytest.raises(ModelError, match="only for HIR"):
        sp.propose_nl(SOURCE, language="typed", provider=lambda _: model(),
                      required_outputs=OUTPUTS)
