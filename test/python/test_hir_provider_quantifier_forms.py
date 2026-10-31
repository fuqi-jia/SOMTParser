"""Quantifier aliases must expose their bodies to provider-form normalization.

The tag used to change only after the singleton-operator pass, leaving nested
provider operators unvisited. Redundant matching op/quantifier tags occurred
in archived generations too. Check quantifier scope and negative polarity,
composition with existing exact numerals, and replay of the complete ledger.
"""
from _public_relation import public_relation
from copy import deepcopy

import pytest
import z3

import somtparser as sp
from somtparser.hir import build_hir
from somtparser.hir_canonical import canonicalize_hir
from somtparser.hir_provider_forms import adapt_provider_forms
from somtparser.natural_language import Candidate
from test_hir_provider_forms import assert_same, model, replay_ledger


def normalized(raw):
    before = deepcopy(raw)
    adapted, ledger = canonicalize_hir(raw)
    assert raw == before
    assert replay_ledger(raw, ledger) == adapted
    assert canonicalize_hir(adapted) == (adapted, [])
    return adapted, ledger


def formula(raw):
    adapted, _ = normalized(raw)
    result = build_hir(adapted, "x" * 12).translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return public_relation(result)


@pytest.mark.parametrize("kind", ["forall", "exists"])
@pytest.mark.parametrize("form", ["tagged", "redundant", "named"])
@pytest.mark.parametrize("negated", [False, True])
def test_quantifier_aliases_preserve_shadowing_and_negative_polarity(kind, form, negated):
    domain = {"and": [{"ge": [{"var": "x"}, {"literal": "0", "sort": "Int"}]},
                       {"le": [{"var": "x"}, {"literal": "2", "sort": "Int"}]}]}
    comparison = {"lt" if kind == "forall" else "ge": [{"var": "x"}, {"var": "y"}]}
    expr = {"op": kind, "binders": [{"name": "x", "sort": {"sort": "Int"}}],
            "body": {"implies" if kind == "forall" else "and": [domain, comparison]}}
    if form == "redundant":
        expr["quantifier"] = kind
    elif form == "named":
        expr = {kind: expr["binders"], "body": expr["body"]}
    if negated:
        expr = {"not": [expr]}
    raw = model(expr)
    raw["declarations"] = [{"name": "x", "sort": "Int"}, {"name": "y", "sort": "Int"}]
    raw["constraints"].append({"expr": {"eq": [{"var": "x"}, {"literal": "42", "sort": "Int"}]}, "span": [0, 12]})
    expected = z3.Int("y") >= 3 if kind == "forall" else z3.Int("y") <= 2
    assert_same(formula(raw), z3.And(z3.Int("x") == 42, z3.Not(expected) if negated else expected))


@pytest.mark.parametrize("expr", [
    {"op": "forall", "quantifier": "exists", "binders": [{"name": "i", "sort": "Int"}], "body": {"and": []}},
    {"op": "forall", "binders": [], "body": {"and": []}},
    {"op": "forall", "binders": [{"name": "i"}], "body": {"and": []}},
    {"op": "forall", "binders": [{"name": "i", "sort": "Int"}], "body": "true"},
    {"op": "forall", "binders": [{"name": "i", "sort": "Int"}], "body": {"and": []}, "extra": 1},
    {"op": "forall", "args": [{"literal": "1", "sort": "Int"}]},
    {"forall": [], "body": {"and": []}},
    {"forall": [{"name": "i", "sort": "Int"}], "exists": [], "body": {"and": []}},
])
def test_conflicting_or_malformed_quantifiers_are_not_guessed(expr):
    raw = model(expr)
    assert adapt_provider_forms(raw) == (raw, [])


def test_nested_aliases_and_unbounded_universe_survive_candidate_roundtrip():
    raw = model({"op": "forall", "binders": [{"name": "x", "sort": "Int"}], "body": {
        "op": "exists", "quantifier": "exists", "binders": [{"name": "y", "sort": "Int"}],
        "body": {"eq": [{"var": "y"}, {"add": [{"var": "x"}, {"literal": "1", "sort": "Int"}]}]}}})
    raw.pop("context")
    candidate = sp.propose_nl("x" * 12, language="hir", provider=lambda _: raw)
    assert candidate.valid, candidate.diagnostics
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert restored.normalization_ledger == candidate.normalization_ledger
    # No implicit finite bounds: every integer has a strictly larger successor.
    assert_same(formula(raw), z3.BoolVal(True))
    translated = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert translated.ok, translated.diagnostics
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(translated.to_smt2()))
    assert solver.check() == z3.sat


def test_missing_names_and_unresolved_interpretations_are_still_rejected():
    raw = model({"op": "exists", "binders": [{"name": "i", "sort": "Int"}],
                 "body": {"eq": [{"var": "i"}, {"var": "capacity"}]}})
    adapted, ledger = normalized(raw)
    assert ledger
    with pytest.raises(ValueError, match="capacity"):
        build_hir(adapted, "x" * 12)
    raw["unresolved"] = ["capacity unspecified"]
    adapted, _ = normalized(raw)
    assert adapted["unresolved"] == raw["unresolved"]
    with pytest.raises(ValueError, match="unresolved interpretation"):
        build_hir(adapted, "x" * 12)


def test_unary_objects_compose_under_quantifiers_and_double_negation():
    raw = model({"forall": [{"name": "x", "sort": "Int"}], "body": {
        "not": {"not": {"implies": [
            {"ge": [{"var": "x"}, {"literal": 0, "sort": "Int"}]},
            {"gt": [{"add": [{"var": "x"}, {"literal": 1, "sort": "Int"}]},
                     {"literal": 0, "sort": "Int"}]}]}}}})
    assert_same(formula(raw), z3.BoolVal(True))
    raw = model({"eq": [{"bvnot": {"var": "b"}}, {"literal": "#x00", "sort": {"BitVec": 8}}]})
    raw["declarations"] = [{"name": "b", "sort": {"BitVec": 8}}]
    assert_same(formula(raw), z3.BitVec("b", 8) == 255)


@pytest.mark.parametrize("expr", [{"not": "true"}, {"not": [True, False]},
    {"implies": {"left": {"literal": True, "sort": "Bool"}, "right": {"literal": False, "sort": "Bool"}}},
    {"sub": {"literal": 1, "sort": "Int"}}])
def test_unary_rule_does_not_guess_nonunary_or_ambiguous_operands(expr):
    raw = model(expr)
    assert adapt_provider_forms(raw) == (raw, [])


@pytest.mark.parametrize("text", ["true", "false"])
def test_explicit_boolean_spelling_retains_truth_value_and_ledger(text):
    raw = model({"eq": [{"var": "p"}, {"literal": text, "sort": "Bool"}]})
    raw["declarations"] = [{"name": "p", "sort": "Bool"}]
    assert_same(formula(raw), z3.Bool("p") == (text == "true"))
    adapted, ledger = normalized(raw)
    assert any(row["rule"] == "exact-Bool-literal-spelling" for row in ledger)


@pytest.mark.parametrize("value", ["True", "FALSE", "1", 1, 0, " true", "false "])
def test_boolean_alias_never_uses_python_truthiness(value):
    raw = model({"literal": value, "sort": "Bool"})
    assert canonicalize_hir(raw) == (raw, [])
