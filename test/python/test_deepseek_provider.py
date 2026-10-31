"""Offline contract tests: no network or real credentials needed."""
import io
import hashlib
import json
from urllib import error

import pytest
import somtparser as sp
from somtparser.deepseek import DeepSeekError, DeepSeekProvider, _NoRedirect
from somtparser.natural_language import Candidate, _canonical, main

TEXT = "Let x be an integer between 0 and 10.\nx >= 3.\nMinimize x."
KEY = "test-only-credential-not-valid"


def reply(model=None, finish="stop", content=None):
    return json.dumps(
        {
            "model": "test-returned-model",
            "choices": [
                {
                    "finish_reason": finish,
                    "message": {
                        "content": content if content is not None else json.dumps(model)
                    },
                }
            ],
            "usage": {"prompt_tokens": 20, "completion_tokens": 30, "total_tokens": 50},
        }
    ).encode()


def transport(monkeypatch, response):
    calls = []

    class Opener:
        def open(self, req, timeout):
            calls.append((req, timeout))
            if isinstance(response, Exception):
                raise response
            return io.BytesIO(response)

    monkeypatch.setattr(
        "somtparser.deepseek.request.build_opener", lambda *args: Opener()
    )
    return calls


def test_review_required_and_provenance_survives_snapshot(monkeypatch):
    calls = transport(monkeypatch, reply(sp.propose_nl(TEXT).model))
    provider = DeepSeekProvider(api_key=KEY, model="test-model")
    pending = sp.translate_nl(TEXT, provider=provider)
    assert not pending.ok and pending.acceptance == "pending"
    candidate = Candidate.from_json(pending.candidate.to_json())
    assert sp.compile_candidate(candidate, accept_digest=candidate.digest).ok
    assert len(calls) == 1
    req, timeout = calls[0]
    assert req.full_url == "https://api.deepseek.com/chat/completions"
    assert req.get_header("Authorization") == "Bearer " + KEY
    body = json.loads(req.data)
    assert body["response_format"] == {"type": "json_object"}
    assert body["thinking"] == {"type": "disabled"}
    assert body["temperature"] == 0 and body["stream"] is False
    assert timeout == 60
    user = json.loads(body["messages"][1]["content"])
    assert user["source"] == TEXT and user["source_line_spans"][0][0] == 0
    assert KEY not in req.data.decode()
    assert KEY not in repr(provider) + candidate.to_json() + json.dumps(
        provider.last_metadata
    )
    record = json.loads(
        candidate.model["assumptions"][-1].removeprefix("Provider execution record: ")
    )
    assert record["returned_model"] == "test-returned-model"
    assert record["requested_model"] == "test-model"
    assert record["usage"]["total_tokens"] == 50
    assert record["prompt_version"] == "somt-deepseek-proposal-v1"
    assert record["thinking"] == "disabled"


def test_hir_prompt_version_and_contextual_constructor_contract(monkeypatch):
    model = dict(
        schema="somt-hir-model-v1",
        language="hir",
        decision="satisfiability",
        declarations=[],
        functions=[],
        constraints=[],
        objectives=[],
        objective_order="single",
        goal=None,
        assumptions=[],
        unresolved=[],
    )
    calls = transport(monkeypatch, reply(model))
    provider = DeepSeekProvider(api_key=KEY, model="test-model")
    candidate = sp.propose_nl(
        "Find a solution.", language="hir", context={}, provider=provider
    )
    assert candidate.valid
    metadata = json.loads(
        candidate.model["assumptions"][-1].removeprefix(
            "Provider execution record: "
        )
    )
    assert metadata["prompt_version"] == "somt-deepseek-hir-v16"
    assert len(calls) == 1
    body = json.loads(calls[0][0].data)
    system = body["messages"][0]["content"]
    for required in [
        '"Uninterpreted":"Entity"',
        '"quantifier":"exists"',
        "JSON Int literals and bounds are integers",
        "share one global name namespace",
        "Declare each context-named observable exactly once",
        "keep the model field goal null",
        "Different directions",
        "add channeling constraints",
        "Never remove an unresolved item solely to make builder validation pass",
        "optional interpretation_notes string array",
        "Never move an unresolved alternative into notes",
        "Never put a variable reference, another literal node, or a computed expression",
        "An ite condition must be Bool",
        "A sum of Real terms is Real",
        "a sum of Int terms is Int",
        "never ge/le on Bool",
        '"op":"all_different","args":[{"var":"array_name"}]',
        "indexes only the final axis",
        "requires the Boolean field positive",
        "every source domain, data row, independent constraint",
        "Do not leave an item out because its encoding is lengthy",
        "encode the alternatives with OR",
        "existentially selected branch",
        "Keep requirements that apply to all choices outside that disjunction",
        "known optimum or target bound is a hard constraint",
        "Distinguish maximal",
    ]:
        assert required in system
    # The same contract reaches non-DeepSeek providers through propose_nl's
    # provider request, and does not demand a dummy explicit objective for soft costs.
    instruction = json.loads(body["messages"][1]["content"])["instruction"]
    assert "encode the alternatives with OR" in instruction
    assert "known optimum or target bound is a hard constraint" in instruction
    assert "optimization has at least one objective or soft constraint" in instruction
    assert "closest to a target, minimize its absolute deviation" in instruction
    assert "including non-optimal ones" in instruction
    assert "A requested number of distinct values is a distinct count" in instruction
    assert "channel it to the required outputs explicitly" in instruction


def test_required_outputs_contract_is_in_actual_deepseek_user_message(monkeypatch):
    hir_model = dict(
        schema="somt-hir-model-v1", language="hir", decision="satisfiability",
        declarations=[{"name": "x", "sort": "Bool", "shape": [2]}],
        functions=[], constraints=[], objectives=[], objective_order="single",
        goal=None, assumptions=[], unresolved=[],
    )
    outputs = [{"name": "x", "sort": "Bool", "shape": [2]}]
    calls = transport(monkeypatch, reply(hir_model))
    provider = DeepSeekProvider(api_key=KEY, model="test-model")
    candidate = sp.propose_nl(
        "Find a two-element Boolean vector x.", language="hir", context={},
        required_outputs=outputs, provider=provider,
    )
    assert candidate.valid
    body = json.loads(calls[0][0].data)
    user = json.loads(body["messages"][1]["content"])
    assert user["required_outputs"] == outputs


def test_repair_feedback_reaches_http_body_without_network(monkeypatch):
    typed = sp.propose_nl(TEXT).model
    typed["constraints"][0]["expr"] = {"var": "missing"}
    calls = transport(monkeypatch, reply(typed))
    trace = sp.propose_nl_with_repair(
        TEXT, language="typed", max_attempts=2,
        provider=DeepSeekProvider(api_key=KEY, model="test-model"),
    )
    assert len(calls) == 2 and trace.stop_reason == "attempt-limit"
    users = [json.loads(json.loads(req.data)["messages"][1]["content"])
             for req, _ in calls]
    assert "repair" not in users[0]
    assert users[1]["repair"]["previous_digest"] == trace.attempts[0].digest
    assert users[1]["repair"]["diagnostics"] == list(trace.attempts[0].diagnostics)
    assert users[1]["source"] == users[0]["source"] == TEXT
    assert KEY not in json.dumps(users)


def test_hir_repair_feedback_covers_array_and_table_schema():
    source = "Find distinct values in a 2 by 2 integer array."
    base = dict(
        schema="somt-hir-model-v1",
        language="hir",
        decision="satisfiability",
        declarations=[dict(name="grid", sort="Int", shape=[2, 2], lower=1, upper=4)],
        functions=[],
        objectives=[],
        objective_order="single",
        goal=None,
        assumptions=[],
        unresolved=[],
    )
    malformed = dict(base, constraints=[dict(
        expr={"cp": "all_different", "items": {"array": "grid", "length": 4}},
        span=[0, len(source)],
    )])
    corrected = dict(base, constraints=[dict(
        expr={"op": "all_different", "args": [{"var": "grid"}]},
        span=[0, len(source)],
    )])
    requests = []

    def provider(request):
        requests.append(request)
        return malformed if len(requests) == 1 else corrected

    trace = sp.propose_nl_with_repair(
        source, language="hir", max_attempts=2, provider=provider
    )
    assert trace.candidate.valid
    assert len(requests) == 2
    repair = requests[1]["repair"]["instruction"]
    assert "native HIR all_different" in repair
    assert "final axis" in repair
    assert "required positive Boolean" in repair
    assert "audit each source domain, data row, independent constraint" in repair


@pytest.mark.parametrize("status", [301, 401, 402, 403, 429, 500])
def test_http_failure_sanitized_and_not_retried(monkeypatch, status):
    exc = error.HTTPError(
        "https://api.deepseek.com/chat/completions",
        status,
        KEY,
        {},
        io.BytesIO(KEY.encode()),
    )
    calls = transport(monkeypatch, exc)
    provider = DeepSeekProvider(api_key=KEY)
    with pytest.raises(DeepSeekError) as caught:
        sp.propose_nl(TEXT, provider=provider)
    assert KEY not in str(caught.value)
    assert str(status) in str(caught.value)
    assert len(calls) == 1 and provider.last_metadata is None


@pytest.mark.parametrize(
    "response",
    [
        reply(content=""),
        reply(content="not JSON"),
        reply(content='{"assumptions":[],"assumptions":[]}'),
        reply(sp.propose_nl(TEXT).model, finish="length"),
        reply(sp.propose_nl(TEXT).model, finish="content_filter"),
        b"{}",
        b"\xff",
        b"x" * (2 * 1024 * 1024 + 1),
        error.URLError(KEY),
        TimeoutError(KEY),
    ],
)
def test_incomplete_invalid_or_failed_response_is_rejected(monkeypatch, response):
    calls = transport(monkeypatch, response)
    provider = DeepSeekProvider(api_key=KEY)
    with pytest.raises(DeepSeekError) as caught:
        sp.propose_nl(TEXT, provider=provider)
    assert KEY not in str(caught.value)
    assert len(calls) == 1


@pytest.mark.parametrize(
    ("finish", "content"),
    [("stop", "not JSON"), ("length", '{"schema":"incomplete"')],
)
def test_billed_invalid_json_and_length_responses_keep_usage(monkeypatch, finish, content):
    calls = transport(monkeypatch, reply(finish=finish, content=content))
    provider = DeepSeekProvider(api_key=KEY, model="billing-test-model")
    with pytest.raises(DeepSeekError):
        sp.propose_nl(TEXT, provider=provider)

    metadata = provider.last_metadata
    assert len(calls) == 1
    assert metadata["requested_model"] == "billing-test-model"
    assert metadata["returned_model"] == "test-returned-model"
    assert metadata["usage"] == {
        "prompt_tokens": 20, "completion_tokens": 30, "total_tokens": 50,
    }
    assert metadata["request_sha256"] == hashlib.sha256(
        _canonical(provider.last_request).encode()
    ).hexdigest()
    assert metadata["response_content_sha256"] == hashlib.sha256(content.encode()).hexdigest()
    assert provider.last_response_content == content


def test_bad_semantics_cannot_compile(monkeypatch):
    model = sp.propose_nl(TEXT).model
    model["constraints"][0]["expr"] = {"var": "nonexistent"}
    transport(monkeypatch, reply(model))
    candidate = sp.propose_nl(TEXT, provider=DeepSeekProvider(api_key=KEY))
    assert not candidate.valid
    assert not sp.compile_candidate(candidate, accept_digest=candidate.digest).ok


def test_ambiguity_stays_unresolved(monkeypatch):
    model = sp.propose_nl(TEXT).model
    model["unresolved"] = ["What is the quantifier domain?"]
    transport(monkeypatch, reply(model))
    candidate = sp.propose_nl(TEXT, provider=DeepSeekProvider(api_key=KEY))
    assert "quantifier domain" in candidate.diagnostics[0]
    assert not sp.compile_candidate(candidate, accept_digest=candidate.digest).ok


def test_credentials_environment_and_cli(monkeypatch, tmp_path, capsys):
    monkeypatch.delenv("DEEPSEEK_API_KEY", raising=False)
    source = tmp_path / "source.txt"
    source.write_text(TEXT)
    assert main(["propose", str(source), "--provider", "deepseek"]) == 1
    assert capsys.readouterr().out == ""
    monkeypatch.setenv("DEEPSEEK_API_KEY", KEY)
    monkeypatch.setenv("DEEPSEEK_MODEL", "test-model")
    transport(monkeypatch, reply(sp.propose_nl(TEXT).model))
    assert main(["propose", str(source), "--provider", "deepseek"]) == 0
    stdout = capsys.readouterr().out
    assert Candidate.from_json(stdout).valid
    assert KEY not in stdout


def test_redirect_is_not_followed():
    assert (
        _NoRedirect().redirect_request(
            None, None, 302, "redirect", {}, "https://other.example"
        )
        is None
    )


@pytest.mark.parametrize(
    "kwargs",
    [
        {"api_key": ""},
        {"api_key": "secret\nvalue"},
        {"timeout": 0},
        {"timeout": float("nan")},
        {"max_tokens": 99999},
    ],
)
def test_invalid_configuration(kwargs):
    options = {"api_key": KEY, **kwargs}
    with pytest.raises(DeepSeekError):
        DeepSeekProvider(**options)
