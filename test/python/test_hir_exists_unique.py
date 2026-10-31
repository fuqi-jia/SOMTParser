"""Unique existence is tuple uniqueness with capture-free lexical scope."""
from _public_relation import public_relation
from copy import deepcopy
import json
import shutil
import subprocess

import pytest
import z3

import somtparser as sp
from somtparser.hir import HirBuilder, ModelError, hir_api, hir_schema
from somtparser.hir_canonical import canonicalize_hir
from somtparser.natural_language import Candidate
from test_hir_provider_forms import model, replay_ledger


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def quantified(kind, binders, body):
    return {"quantifier": kind, "binders": [
        {"name": name, "sort": sort} for name, sort in binders], "body": body}


def unique(body, binders=(("x", "Int"),)):
    return quantified("exists_unique", binders, body)


def formula(expr, builder=None):
    builder = HirBuilder() if builder is None else builder
    builder.constrain(expr)
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return public_relation(result)


def same(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("body,expected", [
    (lit(False, "Bool"), False),
    (op("eq", var("x"), lit(7)), True),
    (op("or", op("eq", var("x"), lit(0)), op("eq", var("x"), lit(1))), False),
    (lit(True, "Bool"), False),
])
@pytest.mark.parametrize("negated", [False, True])
def test_zero_one_multiple_and_infinite_solutions(body, expected, negated):
    expression = unique(body)
    if negated:
        expression = op("not", expression)
    same(formula(expression), z3.BoolVal(expected != negated))


@pytest.mark.parametrize("rows", [[], [(False, True)], [(False, False), (True, True)],
                                  [(False, False), (False, True)],
                                  [(False, False), (False, True), (True, False), (True, True)]])
def test_simultaneous_tuple_uniqueness_against_finite_relation(rows):
    body = op("or", *(op("and", op("eq", var("x"), lit(x, "Bool")),
                         op("eq", var("y"), lit(y, "Bool"))) for x, y in rows))
    same(formula(unique(body, (("x", "Bool"), ("y", "Bool")))), z3.BoolVal(len(rows) == 1))


def test_outer_binder_and_unbounded_successor():
    expression = quantified("forall", (("x", "Int"),),
        unique(op("eq", var("y"), op("add", var("x"), lit(1))), (("y", "Int"),)))
    same(formula(expression), z3.BoolVal(True))


def test_nested_shadowing_and_later_user_names_are_not_captured():
    builder = HirBuilder()
    body = op("and", op("eq", var("x"), lit(3)),
              unique(op("eq", var("x"), lit(9))))
    builder.constrain(unique(body))
    # These legal names resemble generated binders and are declared afterwards.
    for name in ["x", "somt_hir_bound_1", "somt_hir_bound_2"]:
        builder.declare(name, "Int")
        builder.constrain(op("eq", var(name), lit(42)))
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = public_relation(result)
    same(actual, z3.And(*[z3.Int(n) == 42 for n in ["x", "somt_hir_bound_1", "somt_hir_bound_2"]]))


def test_nested_unique_body_keeps_outer_tuple_dependency():
    # A finite relation gives x=0 exactly one y, x=1 two y's, and every
    # remaining x zero y's. Thus exactly one x has exactly one such y.
    inner = unique(op("or",
        op("and", op("eq", var("x"), lit(0)), op("eq", var("y"), lit(0))),
        op("and", op("eq", var("x"), lit(1)),
           op("or", op("eq", var("y"), lit(1)), op("eq", var("y"), lit(-1))))),
        (("y", "Int"),))
    same(formula(unique(inner)), z3.BoolVal(True))


def test_unique_shadowing_inside_fold_and_fold_inside_unique():
    builder = HirBuilder()
    builder.data = {"values": [3, 5]}
    lookup = {"data": "values", "indices": [var("i")], "default": lit(-1)}
    body = op("eq", var("x"), {"fold": "sum", "var": "i", "range": [0, 2], "body": lookup})
    folded = {"fold": "forall", "var": "x", "range": [0, 2], "body": unique(body)}
    same(formula(folded, builder), z3.BoolVal(True))


def test_fold_memoization_does_not_reuse_first_unique_binder():
    # A quantifier inside each finite iteration must not be treated as its
    # shadowed concrete fold value, and the two copies have distinct bindings.
    body = op("and", op("eq", var("i"), lit(7)),
        op("eq", {"fold": "sum", "var": "j", "range": [0, 2],
                  "body": op("add", var("i"), var("j"))}, lit(15)))
    expr = {"fold": "forall", "var": "i", "range": [0, 2],
            "body": unique(body, (("i", "Int"),))}
    same(formula(expr), z3.BoolVal(True))


def test_nonzero_guard_facts_do_not_capture_shadowed_unique_binder():
    builder = HirBuilder()
    builder.declare("d", "Int")
    unguarded = unique(op("eq", op("mod_euclid", lit(7), var("d")), lit(0)), (("d", "Int"),))
    with pytest.raises(ModelError, match="nonzero"):
        builder.expr(op("implies", op("ne", var("d"), lit(0)), unguarded))
    guarded = unique(op("and", op("eq", var("d"), lit(7)),
        op("eq", op("mod_euclid", lit(7), var("d")), lit(0))), (("d", "Int"),))
    same(formula(guarded), z3.BoolVal(True))


@pytest.mark.parametrize("sort", ["Bool", "Int", "Real", "String", {"BitVec": 3},
    {"FloatingPoint": [3, 5]}, {"Array": ["Int", "Bool"]}, {"Uninterpreted": "Entity"}])
def test_singleton_uniqueness_for_native_sorts(sort):
    builder = HirBuilder()
    builder.declare("target", sort)
    same(formula(unique(op("eq", var("x"), var("target")), (("x", sort),)), builder), z3.BoolVal(True))


@pytest.mark.parametrize("sort", [{"Set": "Bool"}, {"Tuple": ["Bool", {"BitVec": 2}]},
                                   {"Tuple": []}, {"Datatype": "Choice"}])
def test_container_and_datatype_binders_use_the_same_exact_equality(sort):
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for native container binder semantics")
    builder = HirBuilder()
    builder.declare_datatypes([{"name": "Choice", "constructors": [
        {"name": "first", "fields": []}, {"name": "second", "fields": []}]}])
    builder.declare("target", sort)
    builder.constrain(op("not", unique(op("eq", var("x"), var("target")), (("x", sort),))))
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(sp.OmtDialect.SmtLib2025)
    if "(check-sat)" not in script:
        script += "\n(check-sat)\n"
    checked = subprocess.run([executable, "--lang=smt2", "--tlimit=10000"],
                             input=script, capture_output=True, text=True, timeout=15)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout.strip() == "unsat", checked.stdout + checked.stderr


def test_open_universe_size_is_not_assumed_by_unique_true():
    sort = {"Uninterpreted": "Entity"}
    expression = formula(unique(lit(True, "Bool"), (("x", sort),)))
    for assertion in [expression, z3.Not(expression)]:
        solver = z3.Solver()
        solver.set(timeout=10000)
        solver.add(assertion)
        assert solver.check() == z3.sat


@pytest.mark.parametrize("binders,body,diagnostic", [
    ([], lit(True, "Bool"), "invalid quantifier"),
    ([("x", "Int"), ("x", "Int")], lit(True, "Bool"), "duplicate binder"),
    ([("x", "Int")], var("missing"), "undeclared variable"),
    ([("x", "Int")], lit(1), "Bool|bool|boolean"),
])
def test_invalid_unique_expressions_are_rejected(binders, body, diagnostic):
    with pytest.raises((ModelError, ValueError), match=diagnostic):
        builder = HirBuilder()
        builder.constrain(unique(body, binders))
        builder.validate()


@pytest.mark.parametrize("form", ["canonical", "tagged", "redundant", "named"])
def test_unique_public_schema_aliases_and_candidate_ledger(form):
    expression = unique({"eq": [var("x"), {"literal": "7", "sort": {"sort": "Int"}}]})
    if form == "tagged":
        expression["op"] = expression.pop("quantifier")
    elif form == "redundant":
        expression["op"] = expression["quantifier"]
    elif form == "named":
        expression = {"exists_unique": expression["binders"], "body": expression["body"]}
    raw = model(expression)
    raw.pop("context")
    before = deepcopy(raw)
    normalized, ledger = canonicalize_hir(raw)
    assert raw == before
    assert replay_ledger(raw, ledger) == normalized
    assert canonicalize_hir(normalized) == (normalized, [])
    assert "exists_unique" in hir_api()["constructors"]["quantifier"]["quantifier"]
    assert "exists_unique" in json.dumps(hir_schema())
    candidate = sp.propose_nl("x" * 12, language="hir", provider=lambda _: raw)
    assert candidate.valid, candidate.diagnostics
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert restored.normalization_ledger == candidate.normalization_ledger
    translated = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert translated.ok, translated.diagnostics
    same(public_relation(translated), z3.BoolVal(True))


def test_nested_unique_expansion_obeys_construction_budget():
    expression = op("eq", var("x"), lit(7))
    for _ in range(20):
        expression = unique(expression)
    with pytest.raises(ModelError, match="construction budget"):
        HirBuilder().expr(expression)
