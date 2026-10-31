"""JSON preferences preserve the hard relation and each complete group cost."""
from copy import deepcopy
import json

import jsonschema
import pytest
import z3

import somtparser as sp
from somtparser.hir import HirBuilder, ModelError, build_hir, hir_schema
from somtparser.hir_canonical import canonicalize_hir
from somtparser.hir_cp import CpProvider, expand_cp_model
from somtparser.natural_language import Candidate


SOURCE = "Prefer p and q; charge a penalty for every unsatisfied preference."


def var(name):
    return {"var": name}


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def soft(expr, weight="1", group=""):
    return dict(expr=expr, weight=weight, group=group, span=[0, len(SOURCE)])


def model(preferences=None):
    return dict(schema="somt-hir-model-v1", language="hir", decision="optimization",
                declarations=[dict(name="p", sort="Bool"), dict(name="q", sort="Bool")],
                functions=[], constraints=[], soft_constraints=preferences or [soft(var("p"))],
                objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])


def compile_model(raw, route="direct"):
    before = deepcopy(raw)
    if route in ("provider", "cp-provider"):
        provider = lambda request: deepcopy(raw)
        if route == "cp-provider":
            provider = CpProvider(provider)
        candidate = sp.propose_nl(SOURCE, language="hir", provider=provider)
        assert candidate.valid, candidate.diagnostics
        result = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    else:
        result = build_hir(expand_cp_model(raw) if route == "expanded" else raw, SOURCE).translate()
    assert raw == before
    assert result.ok, result.diagnostic_items
    text = result.to_smt2() if route in ("provider", "cp-provider") else result.to_smt2(sp.OmtDialect.Z3)
    optimizer = z3.Optimize()
    optimizer.from_string(text)
    return optimizer, text


def assert_vector(optimizer, hard, costs):
    proof = z3.Solver()
    proof.add(z3.Xor(z3.And(*optimizer.assertions()), hard))
    assert proof.check() == z3.unsat
    assert len(optimizer.objectives()) == len(costs)
    for actual, expected in zip(optimizer.objectives(), costs):
        proof = z3.Solver()
        proof.add(actual != expected)
        assert proof.check() == z3.unsat


@pytest.mark.parametrize("route", ["direct", "expanded", "provider", "cp-provider"])
def test_exact_weights_duplicates_and_unsplit_conjunction_across_routes(route):
    weight = 10**90 + 9007199254740993
    raw = model([soft(var("p"), str(weight)), soft(var("p"), "0007"),
                 soft(op("and", var("p"), var("q")), "11")])
    raw["constraints"] = [dict(expr=op("or", var("p"), var("q")), span=[0, len(SOURCE)])]
    jsonschema.validate(raw, hir_schema())
    optimizer, text = compile_model(raw, route)
    p, q = z3.Bools("p q")
    cost = (weight + 7) * z3.If(p, 0, 1) + 11 * z3.If(z3.And(p, q), 0, 1)
    assert_vector(optimizer, z3.Or(p, q), [cost])
    assert str(weight) in text and text.count("(assert-soft") == 3


@pytest.mark.parametrize("sense", ["minimize", "maximize"])
def test_group_identity_order_then_explicit_objective(sense):
    raw = model([soft(var("p"), "2", "z_first"), soft(var("q"), "3", "|z_first|"),
                 soft(op("not", var("p")), "7", "a_second"), soft(var("q"), "11")])
    raw["declarations"].append(dict(name="x", sort="Int"))
    raw["objectives"] = [dict(expr=var("x"), sense=sense, span=[0, len(SOURCE)])]
    with pytest.raises(ModelError):
        build_hir(raw, SOURCE)
    raw["objective_order"] = "lexicographic"
    optimizer, text = compile_model(raw)
    p, q = z3.Bools("p q")
    assert_vector(optimizer, z3.BoolVal(True), [z3.If(p, 0, 2) + z3.If(q, 0, 3),
                  z3.If(p, 7, 0), z3.If(q, 0, 11), z3.Int("x") * (-1 if sense == "maximize" else 1)])
    assert ":opt.priority lex" in text


@pytest.mark.parametrize("route", ["direct", "expanded", "provider", "cp-provider"])
def test_cp_relation_inside_one_soft_item_is_not_a_hard_constraint(route):
    raw = model([soft({"cp": "no_overlap", "starts": [var("a"), var("b")],
                       "durations": [2, 3]}, "13")])
    raw["declarations"] = [dict(name="a", sort="Int"), dict(name="b", sort="Int")]
    optimizer, _ = compile_model(raw, route)
    a, b = z3.Ints("a b")
    assert_vector(optimizer, z3.BoolVal(True), [z3.If(z3.Or(a + 2 <= b, b + 3 <= a), 0, 13)])


def test_helper_discovered_only_in_soft_expression_precedes_its_use():
    folded = {"fold": "sum", "var": "i", "range": [0, 12],
              "body": {"at": "values", "indices": [var("i")]}}
    raw = model([soft(op("eq", folded, lit(3)), "17")])
    raw["declarations"] = [dict(name="values", sort="Int", shape=[12])]
    builder = build_hir(raw, SOURCE)
    assert builder._sum_template_cache
    result = builder.translate()
    assert result.ok, result.diagnostic_items
    optimizer = z3.Optimize()
    optimizer.from_string(result.to_smt2(sp.OmtDialect.Z3))
    values = z3.Array("values", z3.IntSort(), z3.IntSort())
    assert_vector(optimizer, z3.BoolVal(True), [z3.If(z3.Sum([values[i] for i in range(12)]) == 3, 0, 17)])


def test_provider_normalization_only_changes_expression_and_digest_covers_preferences():
    raw = model([soft({"and": [var("p"), var("q")]}, "0007", "cost"),
                 soft(var("q"), "13", "next")])
    raw["objective_order"] = "lexicographic"
    before = deepcopy(raw)
    normalized, ledger = canonicalize_hir(raw)
    assert raw == before and ledger
    assert all(row["path"].startswith("/soft_constraints/0/expr") for row in ledger)
    assert [{k: v for k, v in item.items() if k != "expr"} for item in normalized["soft_constraints"]] == [
        {k: v for k, v in item.items() if k != "expr"} for item in raw["soft_constraints"]]
    proposal = sp.propose_nl(SOURCE, language="hir", provider=lambda request: raw)
    assert proposal.valid, proposal.diagnostics
    restored = Candidate.from_json(proposal.to_json())
    assert restored.digest == proposal.digest
    # The provider owns the normalized expression; the caller supplies the
    # envelope context, including its default empty object.
    assert restored.model == dict(normalized, context={})
    compiled = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert compiled.ok, compiled.diagnostics
    assert compiled.report()["source_links"]["soft_constraints"] == normalized["soft_constraints"]
    for change in ("weight", "group", "span", "expr", "order", "duplicate"):
        envelope = json.loads(proposal.to_json())
        items = envelope["model"]["soft_constraints"]
        if change == "order":
            items.reverse()
        elif change == "duplicate":
            items.append(deepcopy(items[0]))
        else:
            items[0][change] = {"weight": "9", "group": "elsewhere", "span": [1, len(SOURCE)],
                                "expr": var("q")}[change]
        with pytest.raises(ModelError, match="digest"):
            Candidate.from_json(json.dumps(envelope))


@pytest.mark.parametrize("weight", [0, 1, 1.5, True, None, "", "0", "000", "-1", "+1", "1/2", "1.0",
                                    "1e3", "１", "١", "1\n", " 1", "1 "])
def test_schema_and_builder_reject_inexact_or_nonpositive_weights(weight):
    raw = model([soft(var("p"), weight)])
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(raw, hir_schema())
    with pytest.raises(ModelError) as error:
        build_hir(raw, SOURCE)
    assert error.value.path == "soft_constraints[0].weight"


@pytest.mark.parametrize("expr,path", [
    (lit(1), "soft_constraints[0].expr"),
    (var("missing"), "soft_constraints[0].expr"),
])
def test_soft_expression_diagnostic_keeps_source_span(expr, path):
    raw = model([soft(expr)])
    proposal = sp.propose_nl(SOURCE, language="hir", provider=lambda request: raw)
    assert not proposal.valid
    detail, = proposal.diagnostic_details
    assert detail["json_pointer"] == "/" + path.replace("[0]", "/0").replace(".", "/")
    assert detail["source_span"] == [0, len(SOURCE)]


@pytest.mark.parametrize("group", [None, 1, "a b", "|unclosed", "(assert false)", "a\n"])
def test_invalid_group_is_refused(group):
    with pytest.raises(ModelError):
        build_hir(model([soft(var("p"), group=group)]), SOURCE)


@pytest.mark.parametrize("defect", ["missing-group", "unknown-field", "invalid-span", "not-list", "wrong-decision"])
def test_malformed_soft_item_cannot_be_dropped_or_made_hard(defect):
    raw = model()
    if defect == "missing-group":
        del raw["soft_constraints"][0]["group"]
    elif defect == "unknown-field":
        raw["soft_constraints"][0]["unknown"] = True
    elif defect == "invalid-span":
        raw["soft_constraints"][0]["span"] = [0, len(SOURCE) + 1]
    elif defect == "not-list":
        raw["soft_constraints"] = {}
    else:
        raw["decision"] = "satisfiability"
    with pytest.raises(ModelError):
        build_hir(raw, SOURCE)


@pytest.mark.parametrize("present", [False, True])
def test_legacy_model_and_empty_soft_list_have_no_objectives(present):
    raw = model()
    raw["decision"] = "satisfiability"
    raw.pop("soft_constraints")
    if present:
        raw["soft_constraints"] = []
    optimizer, _ = compile_model(raw)
    assert_vector(optimizer, z3.BoolVal(True), [])


def test_public_builder_constructs_one_weighted_preference():
    builder = HirBuilder()
    builder.declare("p", "Bool")
    builder.soft_constrain(var("p"), "23", source_path="preference.expr")
    result = builder.translate()
    assert result.ok, result.diagnostic_items
    optimizer = z3.Optimize()
    optimizer.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert_vector(optimizer, z3.BoolVal(True), [z3.If(z3.Bool("p"), 0, 23)])


def test_weight_larger_than_python_integer_conversion_limit_stays_text():
    weight = "9" * 5000
    raw = model([soft(var("p"), weight)])
    jsonschema.validate(raw, hir_schema())
    optimizer, text = compile_model(raw)
    assert weight in text
    assert_vector(optimizer, z3.BoolVal(True), [z3.If(z3.Bool("p"), z3.IntVal(0), z3.IntVal(weight))])


def test_single_objective_cannot_silently_enable_multiple_group_priorities():
    raw = model([soft(var("p"), "1", "first"), soft(var("q"), "2", "second")])
    with pytest.raises(ModelError):
        build_hir(raw, SOURCE)
    raw["objective_order"] = "lexicographic"
    optimizer, _ = compile_model(raw)
    assert_vector(optimizer, z3.BoolVal(True), [z3.If(z3.Bool("p"), 0, 1), z3.If(z3.Bool("q"), 0, 2)])
