"""Explicit, opt-in size policies retain safe defaults and full validation."""
import pytest
import somtparser as sp
from somtparser.natural_language import Candidate, ModelError


def test_default_source_limit_stays_in_force():
    source = "x" * (128 * 1024 + 1)
    with pytest.raises(ModelError, match="configured character limit"):
        sp.propose_nl(source, provider=lambda request: {})


def test_explicit_source_budget_flows_through_propose_reload_and_compile():
    seed = sp.propose_nl("Let x be an integer between 0 and 10.\nx is at least 3.\nMinimize x.\n")
    source = "x" * (128 * 1024 + 1)
    limits = sp.CandidateSizeLimits(max_source_chars=len(source))
    candidate = sp.propose_nl(source, provider=lambda request: seed.model, size_limits=limits)
    assert candidate.valid
    with pytest.raises(ModelError, match="pass them explicitly"):
        Candidate.from_json(candidate.to_json())
    restored = Candidate.from_json(candidate.to_json(), size_limits=limits)
    assert restored.size_limits == limits
    result = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert result.ok, result.diagnostics
    assert "(minimize nl_s0)" in result.to_smt2()


def test_model_budget_is_explicit_and_default_is_unchanged():
    seed = sp.propose_nl("Let x be an integer between 0 and 10.\nx is at least 3.\nMinimize x.\n")
    model = seed.model
    model["assumptions"].append("x" * 4096)
    source = seed.source
    with pytest.raises(ModelError, match="candidate JSON exceeds"):
        sp.propose_nl(source, provider=lambda request: model,
                      size_limits=sp.CandidateSizeLimits(max_model_json_chars=1024))
    limits = sp.CandidateSizeLimits(max_model_json_chars=8192)
    candidate = sp.propose_nl(source, provider=lambda request: model, size_limits=limits)
    assert candidate.valid
    restored = Candidate.from_json(candidate.to_json(), size_limits=limits)
    assert restored.valid
    assert sp.compile_candidate(restored, accept_digest=restored.digest).ok


def test_invalid_size_policy_is_rejected():
    for value in (0, -1, True, 1.5):
        with pytest.raises(ModelError, match="positive integer or None"):
            sp.CandidateSizeLimits(max_source_chars=value)


def test_explicit_budget_overrides_caller_context_without_changing_it():
    from somtparser.construction_limits import construction_limits, current_construction_limits
    source = "Let x be an integer between 0 and 10.\nx is at least 3.\nMinimize x.\n"
    seed = sp.propose_nl(source)
    with construction_limits(max_source_chars=8):
        with pytest.raises(ModelError, match="character limit"):
            sp.propose_nl(source, provider=lambda request: seed.model)
        policy = sp.CandidateSizeLimits(max_source_chars=len(source))
        candidate = sp.propose_nl(source, provider=lambda request: seed.model, size_limits=policy)
        assert candidate.valid
        assert current_construction_limits().max_source_chars == 8
        assert sp.compile_candidate(candidate, accept_digest=candidate.digest).ok
    assert candidate.size_limits == policy


def test_context_budget_and_explicit_policy_remain_separate_after_roundtrip():
    from somtparser.construction_limits import construction_limits
    source = "Let x be an integer between 0 and 10.\nx is at least 3.\nMinimize x.\n"
    seed = sp.propose_nl(source)
    with construction_limits(max_source_chars=8):
        policy = sp.CandidateSizeLimits(max_source_chars=len(source))
        candidate = sp.propose_nl(source, provider=lambda request: seed.model, size_limits=policy)
        serialized = candidate.to_json()
        # Serialized nondefault policy is a request for explicit caller
        # authorization, never permission to raise the current context budget.
        with pytest.raises(ModelError, match="pass them explicitly"):
            Candidate.from_json(serialized)
        restored = Candidate.from_json(serialized, size_limits=policy)
        assert restored.digest == candidate.digest
        assert sp.compile_candidate(restored, accept_digest=restored.digest).ok
