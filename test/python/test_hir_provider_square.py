from copy import deepcopy

import pytest
import z3

from somtparser.hir import HirBuilder
from somtparser.hir_provider_forms import adapt_provider_forms
from test_hir_provider_forms import model, replay_ledger


def square(base, exponent=2):
    return {"op": "pow", "args": [base, {"literal": exponent, "sort": "Int"}]}


@pytest.mark.parametrize("sort", ["Int", "Real"])
def test_exact_square_rewrite_preserves_complete_relation_and_ledger(sort):
    raw = model({"op": "eq", "args": [square({"var": "x"}), {
        "literal": "9" if sort == "Real" else 9, "sort": sort,
    }]})
    raw["declarations"] = [{"name": "x", "sort": sort}]
    original = deepcopy(raw)

    adapted, ledger = adapt_provider_forms(raw)

    expected = {"op": "eq", "args": [
        {"op": "mul", "args": [{"var": "x"}, {"var": "x"}]},
        {"literal": "9" if sort == "Real" else 9, "sort": sort},
    ]}
    assert raw == original
    assert adapted["constraints"][0]["expr"] == expected
    assert ledger[0] == {
        "path": "/constraints/0/expr/args/0",
        "rule": "exact-square-to-multiplication",
        "before": square({"var": "x"}),
        "after": expected["args"][0],
    }
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])

    def compile_relation(expr, ctx):
        builder = HirBuilder()
        builder.declare("x", sort)
        builder.constrain(expr)
        translated = builder.translate()
        assert translated.ok, [d.message for d in translated.diagnostic_items]
        return z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=ctx))

    ctx = z3.Context()
    actual = compile_relation(adapted["constraints"][0]["expr"], ctx)
    x = z3.Int("x", ctx=ctx) if sort == "Int" else z3.Real("x", ctx=ctx)
    explicit_square = x * x == z3.IntVal(9, ctx=ctx) if sort == "Int" else x * x == z3.RealVal(9, ctx=ctx)
    solver = z3.Solver(ctx=ctx)
    solver.add(z3.Xor(actual, explicit_square, ctx=ctx))
    assert solver.check() == z3.unsat


def test_square_rewrite_visits_quantifier_body_and_keeps_binder():
    raw = model({
        "quantifier": "forall",
        "binders": [{"name": "i", "sort": "Int"}],
        "body": {"op": "ge", "args": [square({"var": "i"}), {
            "literal": 0, "sort": "Int",
        }]},
    })

    adapted, ledger = adapt_provider_forms(raw)

    assert adapted["constraints"][0]["expr"] == {
        "quantifier": "forall",
        "binders": [{"name": "i", "sort": "Int"}],
        "body": {"op": "ge", "args": [
            {"op": "mul", "args": [{"var": "i"}, {"var": "i"}]},
            {"literal": 0, "sort": "Int"},
        ]},
    }
    assert any(entry["rule"] == "exact-square-to-multiplication" for entry in ledger)
    assert replay_ledger(raw, ledger) == adapted


def test_square_shaped_opaque_data_is_not_visited():
    opaque = square({"var": "x"})
    raw = model({"op": "eq", "args": [{"var": "x"}, {
        "literal": 0, "sort": "Int",
    }]})
    raw["data"] = {"opaque": opaque}
    raw["context"] = {"opaque": opaque}

    adapted, ledger = adapt_provider_forms(raw)

    assert adapted["data"] == raw["data"]
    assert adapted["context"] == raw["context"]
    assert not ledger


@pytest.mark.parametrize("candidate", [
    square({"var": "x"}, 0),
    square({"var": "x"}, 1),
    square({"var": "x"}, -2),
    {"op": "pow", "args": [{"var": "x"}, {"literal": 2, "sort": "Real"}]},
    {"op": "pow", "args": [{"var": "x"}, {"literal": "2", "sort": "Int"}]},
    {"op": "pow", "args": [{"var": "x"}, {"literal": True, "sort": "Int"}]},
    {"op": "pow", "args": [{"var": "x"}, {"literal": 2, "sort": "Int"}], "extra": 1},
    {"pow": [{"var": "x"}, {"literal": 2, "sort": "Int"}]},
])
def test_only_exact_canonical_int_square_is_rewritten(candidate):
    raw = model(candidate)
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted == raw
    assert ledger == []


def test_explicit_user_pow_function_keeps_its_declared_meaning():
    raw = model(square({"var": "x"}))
    raw["declarations"] = [{"name": "x", "sort": "Int"}]
    raw["functions"] = [{"name": "pow", "arguments": ["Int", "Int"], "result": "Int"}]

    adapted, ledger = adapt_provider_forms(raw)

    assert adapted["constraints"][0]["expr"] == {
        "apply": "pow",
        "args": [{"var": "x"}, {"literal": 2, "sort": "Int"}],
    }
    assert any(entry["rule"] == "declared-function-op-tag" for entry in ledger)
    assert not any(entry["rule"] == "exact-square-to-multiplication" for entry in ledger)
    assert replay_ledger(raw, ledger) == adapted


@pytest.mark.parametrize("sort", ["Int", "Real"])
def test_large_indexed_square_fold_survives_candidate_snapshot_and_compilation(sort):
    import somtparser as sp
    from somtparser.construction_limits import construction_limits
    from somtparser.natural_language import Candidate

    raw = model({"finite_fold": {
        "fold": "forall", "var": "i", "range": [0, 25600],
        "body": {"op": "eq", "args": [
            square({"var": "a", "indices": [{"var": "i"}]}),
            {"literal": "9" if sort == "Real" else 9, "sort": sort},
        ]},
    }})
    raw["declarations"] = [{"name": "a", "sort": {"Array": ["Int", sort]}}]
    raw.pop("context")
    with construction_limits(max_finite_elements=None):
        candidate = sp.propose_nl("square array", language="hir", provider=lambda request: raw)
        assert candidate.valid, candidate.diagnostics
        restored = Candidate.from_json(candidate.to_json())
        assert restored.digest == candidate.digest
        result = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert result.ok, result.diagnostics

    ctx = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(), ctx=ctx))
    element_sort = z3.IntSort(ctx) if sort == "Int" else z3.RealSort(ctx)
    array = z3.Array("a", z3.IntSort(ctx), element_sort)
    index = z3.Int("source_index", ctx=ctx)
    cell = z3.Select(array, index)
    expected = z3.ForAll(index, z3.Implies(
        z3.And(index >= 0, index < 25600), cell * cell == 9))
    proof = z3.Solver(ctx=ctx)
    proof.add(z3.Xor(actual, expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()
