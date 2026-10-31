"""Indexed variable aliases retain complete array relations and audit trails."""
from copy import deepcopy

import pytest
import z3
import somtparser as sp
from somtparser.hir_provider_forms import adapt_provider_forms


def model(expression, declarations=None):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=declarations or [], functions=[],
                constraints=[dict(expr=expression, span=[0, 4])],
                objectives=[], objective_order="single", goal=None,
                assumptions=[], unresolved=[])


def replay(original, ledger):
    result = deepcopy(original)
    for entry in ledger:
        parts = [x.replace("~1", "/").replace("~0", "~") for x in entry["path"].split("/")[1:]]
        parent = result
        for name in parts[:-1]:
            parent = parent[int(name)] if isinstance(parent, list) else parent[name]
        key = int(parts[-1]) if isinstance(parent, list) else parts[-1]
        assert parent[key] == entry["before"]
        parent[key] = deepcopy(entry["after"])
    return result


def test_public_pipeline_preserves_nested_array_access_and_full_relation():
    raw = model({"op": "eq", "args": [
        {"var": "grid", "indices": [{"literal": 1}, {"var": "index"}]}, {"literal": 7}]},
        [{"name": "grid", "sort": {"Array": ["Int", {"Array": ["Int", "Int"]}]}},
         {"name": "index", "sort": "Int"}])
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert raw == original and replay(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])
    candidate = sp.propose_nl("grid", language="hir", provider=lambda request: raw)
    assert candidate.valid, candidate.diagnostics
    translation = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert translation.ok, translation.diagnostics
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(translation.to_smt2(), ctx=context))
    integer = z3.IntSort(ctx=context)
    grid = z3.Array("grid", integer, z3.ArraySort(integer, integer))
    index = z3.Int("index", ctx=context)
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, grid[1][index] == 7))
    assert proof.check() == z3.unsat


def test_aliases_in_quantified_body_do_not_change_binder_identity():
    raw = model({"quantifier": "forall", "binders": [{"name": "i", "sort": "Int"}],
                 "body": {"op": "eq", "args": [{"var": "a", "indices": [{"var": "i"}]},
                                                  {"var": "i"}]}},
                [{"name": "a", "sort": {"Array": ["Int", "Int"]}}])
    candidate = sp.propose_nl("test", language="hir", provider=lambda request: raw)
    assert candidate.valid, candidate.diagnostics
    translation = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(translation.to_smt2(), ctx=context))
    a = z3.Array("a", z3.IntSort(ctx=context), z3.IntSort(ctx=context))
    i = z3.Int("i", ctx=context)
    proof = z3.Solver(ctx=context)
    proof.add(z3.Xor(actual, z3.ForAll([i], a[i] == i)))
    assert proof.check() == z3.unsat


@pytest.mark.parametrize("value,sort", [(1, "Int"), (True, "Bool")])
def test_unsorted_exact_literal_and_opaque_data_are_kept_distinct(value, sort):
    raw = model({"literal": value})
    raw["data"] = {"opaque": {"literal": value}}
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted["constraints"][0]["expr"] == {"literal": value, "sort": sort}
    assert adapted["data"] == raw["data"]
    assert replay(raw, ledger) == adapted


@pytest.mark.parametrize("expression", [
    {"var": "a", "indices": []},
    {"var": "a", "indices": 0},
    {"var": "a", "indices": [0], "default": 0},
    {"var": 3, "indices": [0]},
    {"literal": "1"},
    {"literal": 1.0},
    {"literal": 1, "unit": "minute"},
])
def test_ambiguous_or_extended_records_are_not_guessed(expression):
    raw = model(expression)
    assert adapt_provider_forms(raw) == (raw, [])


def test_missing_declaration_remains_a_real_candidate_error():
    raw = model({"op": "eq", "args": [{"var": "missing", "indices": [0]}, 1]})
    candidate = sp.propose_nl("test", language="hir", provider=lambda request: raw)
    assert not candidate.valid
    assert any("missing" in str(error) for error in candidate.diagnostics)
