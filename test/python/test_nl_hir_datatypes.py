"""NL proposal path for native HIR datatypes, with a deterministic provider."""
import hashlib
import json
import shutil
import subprocess

import pytest
import somtparser as sp
from somtparser.hir import HirBuilder, ModelError
from somtparser.natural_language import Candidate


def var(name):
    return {"var": name}


def lit(value, sort):
    return {"literal": value, "sort": sort}


def op(operator, *args):
    return {"op": operator, "args": list(args)}


def dt_ctor(name, sort, *args):
    return {"dt_constructor": name, "sort": sort, "args": list(args)}


def dt_sel(name, sort, value):
    return {"dt_selector": name, "sort": sort, "value": value}


def cvc5_status(script):
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for the independent datatype oracle")
    if "(check-sat)" not in script:
        script += "\n(check-sat)\n"
    result = subprocess.run(
        [executable, "--lang=smt2", "--tlimit=5000"],
        input=script,
        text=True,
        capture_output=True,
        timeout=10,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    answers = [line for line in result.stdout.splitlines()
               if line in {"sat", "unsat", "unknown"}]
    assert len(answers) == 1 and answers[0] != "unknown", result.stdout + result.stderr
    return answers[0]


def list_candidate(source, *, contradict=False):
    list_int = {"Datatype": {"name": "List", "args": ["Int"]}}
    xs = var("xs")
    # These aliases intentionally occur inside the constructor's field args.
    singleton = dt_ctor(
        "cons",
        list_int,
        lit("+007", {"sort": "Int"}),
        dt_ctor("nil", list_int),
    )
    constraints = [{"eq": [xs, singleton]}]
    head_is_seven = op("eq", dt_sel("head", "Int", xs), lit(7, "Int"))
    if contradict:
        # Do not also assert the expected head relation in this candidate:
        # UNSAT follows from the constructor base fact plus its negation.
        constraints.append(op("not", head_is_seven))
    else:
        constraints.append(head_is_seven)
    constraints.append(
        op("eq", {"dt_tester": "cons", "value": xs}, lit(True, "Bool"))
    )
    return {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "datatypes": [
            {
                "name": "List",
                "params": ["T"],
                "constructors": [
                    {"name": "nil", "fields": []},
                    {
                        "name": "cons",
                        "fields": [
                            {"name": "head", "sort": {"Parameter": "T"}},
                            {
                                "name": "tail",
                                "sort": {"Datatype": {
                                    "name": "List", "args": [{"Parameter": "T"}]
                                }},
                            },
                        ],
                    },
                ],
            }
        ],
        "declarations": [{"name": "xs", "sort": list_int}],
        "functions": [],
        "constraints": [
            {"expr": expr, "span": [0, len(source)]}
            for expr in constraints
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


def propose_with_catalog(source, model):
    requests = []

    def deterministic_provider(request):
        requests.append(request)
        return model

    candidate = sp.propose_nl(
        source, language="hir", provider=deterministic_provider
    )
    assert len(requests) == 1
    request = requests[0]
    assert request["source_sha256"] == hashlib.sha256(source.encode("utf-8")).hexdigest()
    schema = request["schema"]
    assert "datatypes" in schema["properties"]
    api = schema["constructor_api"]
    assert "datatype_declaration" in api["constructors"]
    assert api["constructors"]["datatype_constructor"]["dt_constructor"] == "declared constructor"
    assert api["constructors"]["datatype_selector"]["dt_selector"] == "declared selector"
    return candidate


def test_nl_hir_datatype_proposal_snapshot_compile_and_independent_oracle():
    source = "xs is the one-element integer list whose only value is 7."
    raw = list_candidate(source)
    raw_before = json.loads(json.dumps(raw))
    candidate = propose_with_catalog(source, raw)
    assert candidate.valid, candidate.diagnostics
    assert raw == raw_before
    assert candidate.source == source
    assert candidate.normalization_ledger
    assert any(
        item["rule"] == "exact-Int-decimal-spelling"
        and "/constraints/0/expr/args/1/args/0" in item["path"]
        for item in candidate.normalization_ledger
    )
    assert any(
        item["rule"] == "singleton-operator-object"
        for item in candidate.normalization_ledger
    )

    # Selection binds compilation to the immutable source/model snapshot.
    assert not sp.compile_candidate(candidate).ok
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    translated = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert translated.ok, translated.diagnostics
    assert translated.report()["candidate_digest"] == restored.digest
    assert cvc5_status(translated.to_smt2()) == "sat"

    tampered = json.loads(candidate.to_json())
    tampered["source"] += " changed"
    with pytest.raises(ModelError, match="digest mismatch"):
        Candidate.from_json(json.dumps(tampered))


def test_nl_hir_datatype_contrary_relation_is_independently_unsat():
    source = (
        "xs is the one-element integer list whose only value is 7, "
        "and its head is not 7."
    )
    candidate = propose_with_catalog(source, list_candidate(source, contradict=True))
    assert candidate.valid, candidate.diagnostics
    translated = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert translated.ok, translated.diagnostics
    assert cvc5_status(translated.to_smt2()) == "unsat"


def test_direct_api_distinguishes_inductive_and_coinductive_self_cycles():
    inductive = HirBuilder()
    with pytest.raises(ModelError, match="not well-founded"):
        inductive.declare_datatype(
            {
                "name": "InductiveLoop",
                "constructors": [
                    {"name": "stepI", "fields": [
                        {"name": "nextI", "sort": {"Datatype": "InductiveLoop"}}
                    ]}
                ],
            }
        )

    def stream_builder():
        builder = HirBuilder()
        stream_sort = {"Datatype": "CoStream"}
        builder.declare_datatype(
            {
                "name": "CoStream",
                "coinductive": True,
                "constructors": [
                    {"name": "stepC", "fields": [
                        {"name": "headC", "sort": "Int"},
                        {"name": "tailC", "sort": stream_sort},
                    ]}
                ],
            }
        )
        builder.declare("s", stream_sort)
        builder.constrain(
            op("eq", var("s"), dt_ctor("stepC", stream_sort, lit(7, "Int"), var("s")))
        )
        return builder, stream_sort

    coinductive, stream_sort = stream_builder()
    coinductive.constrain(
        op("eq", dt_sel("headC", "Int", var("s")), lit(7, "Int"))
    )
    translated = coinductive.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    assert cvc5_status(translated.to_smt2()) == "sat"

    contrary, _ = stream_builder()
    contrary.constrain(
        op("not", op("eq", dt_sel("headC", "Int", var("s")), lit(7, "Int")))
    )
    translated = contrary.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    assert cvc5_status(translated.to_smt2()) == "unsat"
