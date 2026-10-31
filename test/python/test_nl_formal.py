import json

import pytest
import somtparser as sp
from somtparser.natural_language import Candidate
from somtparser._nl_model import ModelError
from somtparser.deepseek import DeepSeekProvider

TEXT = "Select the largest number of disjoint sets."


def proposal(program, language="minizinc", decision="optimization"):
    return dict(
        schema="somt-nl-formal-v1",
        language=language,
        program=program,
        decision=decision,
        assumptions=[],
        unresolved=[],
        links=[dict(span=[0, len(TEXT)], fragment=program)],
    )


def candidate(model, **kwargs):
    return sp.propose_nl(
        TEXT, provider=lambda request: model, language=model["language"], **kwargs
    )


@pytest.mark.parametrize(
    "language,program",
    [
        (
            "minizinc",
            "array[1..3] of var 0..1: x; constraint x[1] + x[2] <= 1; solve maximize sum(i in 1..3)(x[i]);",
        ),
        ("lp", "Maximize\n obj: x\nSubject To\n c: x <= 3\nBounds\n x >= 0\nEnd"),
        (
            "xcsp3",
            '<instance format="XCSP3" type="COP"><variables><var id="x">0..3</var></variables><objectives><maximize>x</maximize></objectives></instance>',
        ),
        (
            "smtlib2",
            "(declare-const x Int)(assert (and (>= x 0) (<= x 3)))(maximize x)(check-sat)",
        ),
    ],
)
def test_routes_preserve_selection_and_objective(language, program):
    c = candidate(proposal(program, language), context={"domain": "finite example"})
    assert c.valid
    assert not sp.compile_candidate(c).ok
    restored = Candidate.from_json(c.to_json())
    t = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert t.ok, t.diagnostics
    assert "maximize" in t.to_smt2()
    assert t.report()["language_configuration"] == language
    assert t.interpret_solver_answer("sat")["optimality"] == "not-established"
    with pytest.raises(ModelError, match="projection"):
        t.project_assignment({})


@pytest.mark.parametrize(
    "language,program",
    [
        ("minizinc", 'include "/tmp/model.mzn"; solve satisfy;'),
        ("smtlib2", '(set-option :regular-output-channel "/tmp/log") (check-sat)'),
        ("xcsp3", '<!DOCTYPE instance SYSTEM "file:///tmp/input"><instance/>'),
    ],
)
def test_closed_input(language, program):
    c = candidate(proposal(program, language, "satisfiability"))
    assert not c.valid
    assert not sp.compile_candidate(c, accept_digest=c.digest).ok


def test_decision_mismatch_and_ambiguity():
    m = proposal("var 0..1: x; solve satisfy;")
    c = candidate(m)
    t = sp.compile_candidate(c, accept_digest=c.digest)
    assert not t.ok and "objectives disagree" in t.diagnostics[0]
    m["unresolved"] = ["Missing universe"]
    assert not candidate(m).valid


def test_context_bound_and_not_changed_by_provider():
    def provider(request):
        request["context"]["domain"] = "integer"
        return proposal("var 0..1: x; solve maximize x;")

    c = sp.propose_nl(
        TEXT, language="minizinc", context={"domain": "real"}, provider=provider
    )
    assert c.model["context"] == {"domain": "real"}
    envelope = json.loads(c.to_json())
    envelope["model"]["context"]["domain"] = "integer"
    with pytest.raises(ModelError, match="digest mismatch"):
        Candidate.from_json(json.dumps(envelope))


def test_route_cannot_change_and_unavailable_languages_refuse():
    with pytest.raises(ModelError, match="configuration"):
        sp.propose_nl(
            TEXT, language="lp", provider=lambda r: proposal("solve satisfy;")
        )
    with pytest.raises(ModelError, match="configuration"):
        sp.propose_nl(TEXT, language="python", provider=lambda r: {})


def test_formal_deepseek_protocol(monkeypatch):
    from test_deepseek_provider import reply, transport, KEY

    calls = transport(monkeypatch, reply(proposal("var 0..1: x; solve maximize x;")))
    c = sp.propose_nl(
        TEXT,
        language="minizinc",
        context={"domain": "binary"},
        provider=DeepSeekProvider(api_key=KEY),
    )
    assert c.valid
    body = json.loads(calls[0][0].data)
    payload = json.loads(body["messages"][1]["content"])
    assert payload["context"] == {"domain": "binary"}
    assert payload["language"] == "minizinc"
    assert "somt-deepseek-formal-v4" in c.to_json()
    assert KEY not in c.to_json()
