from copy import deepcopy
import hashlib
import json
import pytest
import z3
import somtparser as sp
from somtparser.hir_canonical import canonicalize_hir
from somtparser.hir_cp import build_cp_hir
from somtparser.natural_language import Candidate, ModelError
from test_hir_cp import model, lit, op


def test_exact_integer_spelling_and_ledger():
    raw = model(
        op("eq", {"var": "x"}, {"literal": "+0012", "sort": "Int"}),
        [dict(name="x", sort="Int", lower="-0", upper="12")],
    )
    fixed, ledger = canonicalize_hir(raw)
    assert fixed["declarations"][0]["lower"] == 0
    assert fixed["constraints"][0]["expr"]["args"][1]["literal"] == 12
    assert raw["declarations"][0]["lower"] == "-0"
    assert len(ledger) == 3
    t = build_cp_hir(fixed, "x").translate()
    assert t.ok
    s = z3.Solver()
    s.add(z3.parse_smt2_string(t.to_smt2()), z3.Int("x") != 12)
    assert s.check() == z3.unsat
    again, changes = canonicalize_hir(fixed)
    assert again == fixed and not changes


@pytest.mark.parametrize("value", ["1.5", "1/1", "1x", "true", "", True, 1.5])
def test_no_guessing_noninteger_spelling(value):
    raw = model(op("eq", lit(1), {"literal": value, "sort": "Int"}))
    fixed, _ = canonicalize_hir(raw)
    assert fixed["constraints"][0]["expr"]["args"][1]["literal"] == value


def test_real_literals_source_spans_and_unresolved_unchanged():
    raw = model(
        op("eq", {"literal": "1", "sort": "Real"}, {"literal": "1", "sort": "Real"})
    )
    raw["unresolved"] = ["unit unknown"]
    raw["constraints"][0]["span"] = ["0", "1"]
    fixed, ledger = canonicalize_hir(raw)
    assert fixed == raw and not ledger


def test_numeric_sort_wrappers_only_normalize_at_sort_positions():
    raw = model(op("eq", lit(1), lit(1)))
    raw["functions"] = [
        dict(
            name="f",
            arguments=[{"sort": "Int"}, {"sort": "Real"}],
            result="Bool",
        )
    ]
    raw["constraints"][0]["expr"] = {
        "quantifier": "forall",
        "binders": [{"name": "r", "sort": {"sort": "Real"}}],
        "body": {
            "op": "eq",
            "args": [
                {"var": "r"},
                {"literal": "0", "sort": {"sort": "Real"}},
            ],
        },
    }
    fixed, ledger = canonicalize_hir(raw)
    assert fixed["functions"][0]["arguments"] == ["Int", "Real"]
    assert fixed["constraints"][0]["expr"]["binders"][0]["sort"] == "Real"
    assert fixed["constraints"][0]["expr"]["body"]["args"][1]["sort"] == "Real"
    assert len(ledger) == 4
    again, changes = canonicalize_hir(fixed)
    assert again == fixed and not changes


def test_nl_hir_proposal_canonicalizes_before_selection_and_preserves_ledger():
    source = "Alice was born in 1995."
    raw = {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [
            {"name": "alice", "sort": {"Uninterpreted": "Entity"}},
            {"name": "somt_goal", "sort": "Bool"},
        ],
        "functions": [
            {
                "name": "born_in_year",
                "arguments": [{"Uninterpreted": "Entity"}, {"sort": "Int"}],
                "result": "Bool",
            }
        ],
        "constraints": [
            {
                "expr": {
                    "apply": "born_in_year",
                    "args": [
                        {"var": "alice"},
                        {"literal": "1995", "sort": "Int"},
                    ],
                },
                "span": [0, len(source)],
            }
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }
    original = deepcopy(raw)
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert candidate.valid, candidate.diagnostics
    assert raw == original
    assert candidate.model["functions"][0]["arguments"] == [
        {"Uninterpreted": "Entity"},
        "Int",
    ]
    assert candidate.model["constraints"][0]["expr"]["args"][1]["literal"] == 1995
    assert len(candidate.normalization_ledger) == 2

    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert restored.normalization_ledger == candidate.normalization_ledger
    fixed, changes = canonicalize_hir(restored.model)
    assert fixed == restored.model and not changes

    translated = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert translated.ok, translated.diagnostics
    assert translated.report()["candidate_digest"] == restored.digest
    assert translated.report()["normalization_ledger"] == candidate.normalization_ledger
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2()))
    entity = z3.DeclareSort("Entity")
    alice = z3.Const("alice", entity)
    born_in_year = z3.Function("born_in_year", entity, z3.IntSort(), z3.BoolSort())
    solver = z3.Solver()
    solver.add(z3.Xor(actual, born_in_year(alice, 1995)))
    assert solver.check() == z3.unsat

    changed_model = json.loads(candidate.to_json())
    changed_model["model"]["constraints"][0]["expr"]["args"][1]["literal"] = "1995"
    with pytest.raises(ModelError, match="digest"):
        Candidate.from_json(json.dumps(changed_model))
    changed_ledger = json.loads(candidate.to_json())
    changed_ledger["normalization_ledger"][0]["after"] = "Real"
    with pytest.raises(ModelError, match="digest"):
        Candidate.from_json(json.dumps(changed_ledger))


def test_legacy_hir_candidate_load_does_not_normalize_its_model():
    source = "x equals 1."
    raw = {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "x", "sort": "Int"}],
        "functions": [],
        "constraints": [
            {
                "expr": {
                    "op": "eq",
                    "args": [{"var": "x"}, {"literal": "1", "sort": "Int"}],
                },
                "span": [0, len(source)],
            }
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }
    payload = {"source": source, "model": raw, "provider": "old-provider"}
    digest = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    envelope = {
        "schema": "somt-nl-candidate-v1",
        "source": source,
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "model": raw,
        "provider": "old-provider",
        "digest": digest,
    }
    restored = Candidate.from_json(json.dumps(envelope))
    assert restored.digest == digest
    assert not restored.valid
    assert restored.model["constraints"][0]["expr"]["args"][1]["literal"] == "1"


@pytest.mark.parametrize("value", [True, 1.5])
def test_nl_hir_proposal_does_not_coerce_bool_or_fractional_int(value):
    source = "x equals a value."
    raw = {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "x", "sort": "Int"}],
        "functions": [],
        "constraints": [
            {
                "expr": {
                    "op": "eq",
                    "args": [
                        {"var": "x"},
                        {"literal": value, "sort": "Int"},
                    ],
                },
                "span": [0, len(source)],
            }
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert not candidate.valid
    assert "expected an exact integer" in candidate.diagnostics[0]
    assert candidate.model["constraints"][0]["expr"]["args"][1]["literal"] == value
    assert not candidate.normalization_ledger


def test_explicit_quantifier_and_aggregate_aliases():
    e = {
        "op": "forall",
        "binders": [dict(name="i", sort="Int")],
        "body": op("eq", {"var": "i"}, {"var": "i"}),
    }
    fixed, ledger = canonicalize_hir(model(e))
    assert ledger and build_cp_hir(fixed, "x").translate().ok
    e = op("eq", {"op": "max", "args": [lit(2), lit(4)]}, lit(4))
    fixed, ledger = canonicalize_hir(model(e))
    assert ledger and build_cp_hir(fixed, "x").translate().ok
    fixed, _ = canonicalize_hir(
        model(op("eq", {"op": "sum", "args": [lit(0), lit(0)]}, lit(0)))
    )
    assert build_cp_hir(fixed, "x").translate().ok
