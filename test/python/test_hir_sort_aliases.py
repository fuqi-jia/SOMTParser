"""Exact, audited normalization of explicit uninterpreted-sort aliases."""
from _public_relation import public_relation
from copy import deepcopy
import hashlib
import json

import pytest
import z3

import somtparser as sp
from somtparser.hir_canonical import canonicalize_hir
from somtparser.natural_language import Candidate, ModelError


def _model():
    source = "Open entities satisfy the relation constraints."
    alias = "Uninterpreted:Person"
    lower_alias = "Uninterpreted:person"
    return source, {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [
            {"name": "alice", "sort": alias},
            {"name": "bob", "sort": alias},
            {"name": "lower_person", "sort": lower_alias},
            {
                "name": "box",
                "sort": {
                    "Array": [alias, {"Array": [lower_alias, "Int"]}],
                },
            },
        ],
        "functions": [
            {"name": "likes", "arguments": [alias, alias], "result": "Bool"},
            {"name": "near", "arguments": [lower_alias, lower_alias], "result": "Bool"},
            {
                "name": "nested_array_fn",
                "arguments": [{"Array": [alias, lower_alias]}],
                "result": {"Array": ["Int", alias]},
            },
        ],
        "constraints": [
            {
                "expr": {
                    "and": [
                        {
                            "quantifier": "forall",
                            "binders": [{"name": "x", "sort": alias}],
                            "body": {
                                "quantifier": "exists",
                                "binders": [{"name": "y", "sort": alias}],
                                "body": {
                                    "apply": "likes",
                                    "args": [{"var": "x"}, {"var": "y"}],
                                },
                            },
                        },
                        {
                            "quantifier": "exists",
                            "binders": [{"name": "p", "sort": lower_alias}],
                            "body": {
                                "apply": "near",
                                "args": [{"var": "p"}, {"var": "lower_person"}],
                            },
                        },
                        {
                            "eq": [
                                {
                                    "at": "box",
                                    "indices": [
                                        {"var": "alice"},
                                        {"var": "lower_person"},
                                    ],
                                },
                                {"literal": 7, "sort": "Int"},
                            ]
                        },
                        {"distinct": [{"var": "alice"}, {"var": "bob"}]},
                        {
                            "quantifier": "exists",
                            "binders": [{"name": "extra", "sort": alias}],
                            "body": {
                                "distinct": [
                                    {"var": "extra"},
                                    {"var": "alice"},
                                    {"var": "bob"},
                                ]
                            },
                        },
                    ]
                },
                "span": [0, len(source)],
            }
        ],
        "objectives": [],
        "assumptions": [],
        "unresolved": [],
        "goal": None,
        "objective_order": "single",
        # Sort-like text outside type positions is data and must stay literal.
        "context": {"note": "Uninterpreted:Context", "sort": "Uninterpreted:NoType"},
    }


def _propose(source, raw):
    context = raw.get("context", {})
    response = {key: value for key, value in raw.items() if key != "context"}
    return sp.propose_nl(
        source,
        language="hir",
        context=context,
        provider=lambda _request: response,
    )


def _replay(raw, ledger):
    result = deepcopy(raw)
    for entry in ledger:
        assert set(entry) == {"path", "rule", "before", "after"}
        path = [part.replace("~1", "/").replace("~0", "~")
                for part in entry["path"].split("/")[1:]]
        parent = result
        for part in path[:-1]:
            parent = parent[int(part)] if isinstance(parent, list) else parent[part]
        key = path[-1]
        current = parent[int(key)] if isinstance(parent, list) else parent[key]
        assert current == entry["before"]
        if isinstance(parent, list):
            parent[int(key)] = deepcopy(entry["after"])
        else:
            parent[key] = deepcopy(entry["after"])
    return result


def test_explicit_uninterpreted_aliases_preserve_open_sort_relation():
    source, raw = _model()
    original = deepcopy(raw)
    candidate = _propose(source, raw)
    assert candidate.valid, candidate.diagnostics
    assert raw == original

    normalized = candidate.model
    person = {"Uninterpreted": "Person"}
    lower_person = {"Uninterpreted": "person"}
    assert normalized["declarations"][0]["sort"] == person
    assert normalized["declarations"][2]["sort"] == lower_person
    assert normalized["declarations"][3]["sort"] == {
        "Array": [person, {"Array": [lower_person, "Int"]}],
    }
    assert normalized["functions"][0]["arguments"] == [person, person]
    assert normalized["functions"][0]["result"] == "Bool"
    assert normalized["functions"][2]["arguments"] == [
        {"Array": [person, lower_person]}
    ]
    assert normalized["functions"][2]["result"] == {
        "Array": ["Int", person]
    }
    assert normalized["context"] == raw["context"]
    assert _replay(raw, candidate.normalization_ledger) == normalized
    assert {entry["rule"] for entry in candidate.normalization_ledger} == {
        "explicit-uninterpreted-sort-alias", "singleton-operator-object",
    }

    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert restored.model == normalized
    translated = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert translated.ok, translated.diagnostics
    assert restored.model == normalized

    # Independent Z3 declarations keep case-distinct open sorts and do not
    # close the domain to the constants named in the candidate.
    actual = public_relation(translated)
    person_sort = z3.DeclareSort("Person")
    lower_sort = z3.DeclareSort("person")
    alice = z3.Const("alice", person_sort)
    bob = z3.Const("bob", person_sort)
    low = z3.Const("lower_person", lower_sort)
    box = z3.Const(
        "box",
        z3.ArraySort(person_sort, z3.ArraySort(lower_sort, z3.IntSort())),
    )
    likes = z3.Function("likes", person_sort, person_sort, z3.BoolSort())
    near = z3.Function("near", lower_sort, lower_sort, z3.BoolSort())
    x, y = z3.Consts("x y", person_sort)
    p = z3.Const("p", lower_sort)
    extra = z3.Const("extra", person_sort)
    expected = z3.And(
        z3.ForAll([x], z3.Exists([y], likes(x, y))),
        z3.Exists([p], near(p, low)),
        z3.Select(z3.Select(box, alice), low) == 7,
        alice != bob,
        z3.Exists([extra], z3.And(extra != alice, extra != bob)),
    )
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(actual)
    assert solver.check() == z3.sat

    again, ledger = canonicalize_hir(normalized)
    assert again == normalized and ledger == []

    tampered_model = json.loads(candidate.to_json())
    tampered_model["model"]["declarations"][0]["sort"] = "Uninterpreted:person"
    with pytest.raises(ModelError, match="digest"):
        Candidate.from_json(json.dumps(tampered_model))
    tampered_ledger = json.loads(candidate.to_json())
    tampered_ledger["normalization_ledger"][0]["after"] = {
        "Uninterpreted": "person"
    }
    with pytest.raises(ModelError, match="digest"):
        Candidate.from_json(json.dumps(tampered_ledger))


def test_only_explicit_valid_sort_aliases_are_normalized():
    _, raw = _model()
    raw["declarations"].extend(
        [
            {"name": "plain", "sort": "Person"},
            {"name": "underscore", "sort": "Uninterpreted_Person"},
            {"name": "empty", "sort": "Uninterpreted:"},
            {"name": "reserved", "sort": "Uninterpreted:and"},
            {"name": "bad_identifier", "sort": "Uninterpreted:Person Type"},
            {"name": "too_long", "sort": "Uninterpreted:" + "A" * 129},
            {"name": "signature", "sort": "Uninterpreted:Person->Bool"},
            {
                "name": "malformed_array",
                "sort": {"Array": ["Uninterpreted:Hidden"]},
            },
            {
                "name": "extra_array_key",
                "sort": {"Array": ["Uninterpreted:Hidden", "Int"], "extra": 1},
            },
        ]
    )
    fixed, ledger = canonicalize_hir(raw)
    declarations = fixed["declarations"]
    assert declarations[4]["sort"] == "Person"
    assert declarations[5]["sort"] == "Uninterpreted_Person"
    assert declarations[6]["sort"] == "Uninterpreted:"
    assert declarations[7]["sort"] == "Uninterpreted:and"
    assert declarations[8]["sort"] == "Uninterpreted:Person Type"
    assert declarations[9]["sort"] == "Uninterpreted:" + "A" * 129
    assert declarations[10]["sort"] == "Uninterpreted:Person->Bool"
    assert declarations[11]["sort"] == {"Array": ["Uninterpreted:Hidden"]}
    assert declarations[12]["sort"] == {
        "Array": ["Uninterpreted:Hidden", "Int"], "extra": 1
    }
    assert raw["declarations"][0]["sort"] == "Uninterpreted:Person"
    assert not any("context" in entry["path"] for entry in ledger)


def test_alias_candidate_envelope_load_and_compile_do_not_recanonicalize():
    source, raw = _model()
    candidate = _propose(source, raw)
    envelope = json.loads(candidate.to_json())
    envelope["model"]["declarations"][0]["sort"] = "Uninterpreted:Person"
    payload = {
        "source": envelope["source"],
        "model": envelope["model"],
        "provider": envelope["provider"],
        "normalization_ledger": envelope["normalization_ledger"],
    }
    envelope["digest"] = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    loaded = Candidate.from_json(json.dumps(envelope))
    assert loaded.model["declarations"][0]["sort"] == "Uninterpreted:Person"
    assert not loaded.valid
    compiled = sp.compile_candidate(loaded, accept_digest=loaded.digest)
    assert not compiled.ok
    assert loaded.model["declarations"][0]["sort"] == "Uninterpreted:Person"
