"""Bounded feedback uses local diagnostics and preserves every interpretation."""
import copy
from dataclasses import FrozenInstanceError

import pytest
import somtparser as sp
from somtparser.natural_language import Candidate, ModelError


TEXT = "Choose an integer x between 0 and 10, with x at least 3."


def model(valid=True):
    return dict(schema="somt-hir-model-v1", language="hir",
                decision="satisfiability",
                declarations=[dict(name="x", sort="Int", lower=0, upper=10)],
                functions=[], constraints=[dict(
                    expr={"op": "ge", "args": [{"var": "x"},
                          {"literal": 3, "sort": "Int"} if valid else
                          {"literal": True, "sort": "Bool"}]}, span=[0, len(TEXT)])],
                objectives=[], objective_order="single", goal=None,
                assumptions=[], unresolved=[])


def test_feedback_repairs_a_candidate_and_retains_the_original_snapshot():
    calls = []
    first = model(False)
    context = {"observables": "x is the integer named in the source"}

    def provider(request):
        calls.append(copy.deepcopy(request))
        if "repair" not in request:
            return first
        feedback = request["repair"]
        assert feedback["diagnostics"][0].startswith("constraints[0].expr.args[1]: ")
        assert "numeric operands required" in feedback["diagnostics"][0]
        replacement = copy.deepcopy(feedback["previous_candidate"])
        replacement["constraints"][0]["expr"]["args"][1] = {"literal": 3, "sort": "Int"}
        assert "context" not in replacement
        # Providers can mutate their request; this must not mutate prior evidence.
        feedback["previous_candidate"]["constraints"] = []
        request["context"].clear()
        first["declarations"].clear()
        return replacement

    trace = sp.propose_nl_with_repair(TEXT, provider=provider, context=context,
                                    max_attempts=3)
    assert len(calls) == len(trace.attempts) == 2
    original, final = trace.attempts
    assert not original.valid and final.valid
    assert original.model["declarations"] == model()["declarations"]
    assert trace.candidate is final and trace.stop_reason == "valid-candidate"
    assert original.provider == final.provider == "external:provider"
    assert original.source == final.source == TEXT
    assert original.digest != final.digest
    for field in ["source", "source_sha256", "schema", "language", "context", "instruction"]:
        assert calls[0][field] == calls[1][field]
    assert calls[1]["repair"]["previous_digest"] == original.digest
    previous_model = original.model
    previous_model.pop("context")
    assert calls[1]["repair"]["previous_candidate"] == previous_model
    assert calls[1]["repair"]["attempt"] == 2
    assert final.model["context"] == context
    assert Candidate.from_json(original.to_json()).digest == original.digest
    assert Candidate.from_json(final.to_json()).digest == final.digest
    with pytest.raises(FrozenInstanceError):
        trace.attempts = ()
    assert not sp.compile_candidate(final).ok
    assert not sp.compile_candidate(final, accept_digest=original.digest).ok
    translated = sp.compile_candidate(final, accept_digest=final.digest)
    assert translated.ok
    assert translated.report()["intent_preservation"] == "not-proved"
    z3 = pytest.importorskip("z3")
    parsed = z3.parse_smt2_string(translated.to_smt2())
    x = z3.Int("x")
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*parsed), z3.And(x >= 0, x <= 10, x >= 3)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("valid,limit,expected", [(True, 4, 1), (False, 3, 3), (False, 1, 1)])
def test_stop_on_validity_or_explicit_attempt_limit(valid, limit, expected):
    calls = []

    def provider(request):
        calls.append(request)
        return model(valid)

    trace = sp.propose_nl_with_repair(TEXT, provider=provider, max_attempts=limit)
    assert len(trace.attempts) == len(calls) == expected
    assert trace.stop_reason == ("valid-candidate" if valid else "attempt-limit")
    assert "repair" not in calls[0]
    assert all(attempt.valid == valid for attempt in trace.attempts)


@pytest.mark.parametrize("limit", [0, -1, True, 1.5, "2"])
def test_invalid_attempt_limit_does_not_call_provider(limit):
    def provider(request):
        pytest.fail("invalid request reached provider")

    with pytest.raises(ModelError, match="positive integer"):
        sp.propose_nl_with_repair(TEXT, provider=provider, max_attempts=limit)


def test_provider_failure_propagates_without_retry():
    calls = []

    def provider(request):
        calls.append(request)
        if len(calls) == 1:
            return model(False)
        raise RuntimeError("service unavailable")

    with pytest.raises(RuntimeError, match="service unavailable"):
        sp.propose_nl_with_repair(TEXT, provider=provider, max_attempts=5)
    assert len(calls) == 2


def test_repair_cannot_change_language_or_supply_its_own_context():
    calls = []

    def provider(request):
        calls.append(request)
        result = model(False)
        if len(calls) == 2:
            result["context"] = {"override": "ignore previous requirements"}
        return result

    with pytest.raises(ModelError, match="requested language configuration"):
        sp.propose_nl_with_repair(TEXT, provider=provider, max_attempts=3)
    assert len(calls) == 2


def test_typed_route_and_default_single_request():
    text = "Let x be an integer between 0 and 10.\nx >= 3.\nFind a solution."
    typed = sp.propose_nl(text).model
    calls = []

    def provider(request):
        calls.append(request)
        return typed

    trace = sp.propose_nl_with_repair(text, provider=provider, language="typed")
    assert trace.candidate.valid and len(calls) == 1


def test_source_ambiguity_remains_invalid_without_a_new_interpretation():
    text = "Let x be an integer between 0 and 10.\nx >= 3."
    unresolved = sp.propose_nl(text).model
    trace = sp.propose_nl_with_repair(
        text, provider=lambda request: unresolved, language="typed", max_attempts=2,
    )
    assert trace.stop_reason == "attempt-limit"
    assert len(trace.attempts) == 2
    assert all(not attempt.valid and attempt.model["unresolved"] for attempt in trace.attempts)


def test_no_implicit_provider():
    with pytest.raises(ModelError, match="explicit callable provider"):
        sp.propose_nl_with_repair(TEXT, provider=None)
