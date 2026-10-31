"""Source-grounded capacity and Boolean-expression checks on native HIR."""
import pytest

import somtparser as sp
from somtparser import natural_language
from somtparser.hir import build_hir

z3 = pytest.importorskip("z3")

# Exact source phrases and instance values relevant to this relation; the test
# intentionally does not model the unrelated production/demand requirements.
SOURCE = (
    "Because each variation is identical in dimension, we know in advance exactly how many items can be printed "
    "on each mother sheet of board. Decide which variations, and how many copies of each, to include on each template. "
    'Instance data: {"n_slots": 42, "n_var": 30}'
)


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def at(name, index):
    return {"at": name, "indices": [lit(index)]}


def capacity_model():
    return {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "layout", "sort": "Int", "shape": [30]}],
        "functions": [],
        "constraints": [
            {"expr": {"op": "ge", "args": [at("layout", i), lit(0)]}, "span": [0, len(SOURCE)]}
            for i in range(30)
        ] + [
            {"expr": {"op": "le", "args": [
                {"fold": "sum", "var": "v", "range": [0, 30],
                 "body": {"at": "layout", "indices": [{"var": "v"}]}},
                lit(42),
            ]}, "span": [0, len(SOURCE)]}
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


def test_real_hir_provider_route_appends_shared_guidance_and_translates():
    captured = {}

    def provider(request):
        captured.update(request)
        return capacity_model()

    candidate = sp.propose_nl(SOURCE, language="hir", provider=provider)
    assert candidate.valid, candidate.diagnostics
    assert captured["source"] == SOURCE
    assert captured["language"] == "hir"
    # Verifies the current builder's actual provider path uses its shared
    # source-relation guidance, rather than only testing the string constant.
    assert captured["instruction"].endswith(natural_language._SOURCE_RELATION_GUIDANCE)
    translated = build_hir(candidate.model, SOURCE).translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]


def test_capacity_subrelation_allows_slack_and_cell_value_above_index_count():
    translated = build_hir(capacity_model(), SOURCE).translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    formula = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    layout = z3.Array("layout", z3.IntSort(context), z3.IntSort(context))

    def possible(values):
        solver = z3.Solver(ctx=context)
        solver.set(timeout=5000)
        solver.add(formula)
        solver.add(*[z3.Select(layout, i) == value for i, value in enumerate(values)])
        result = solver.check()
        assert result != z3.unknown, solver.reason_unknown()
        return result == z3.sat

    def row(first, second=0):
        return [first, second] + [0] * 28

    # n_var=30 gives thirty indices; it is not a value cap of 30.
    assert possible(row(31))
    # “Can be printed” is a capacity; the source does not require a full sheet.
    assert possible(row(1))
    assert possible(row(0))
    assert not possible(row(43))
    assert not possible(row(-1))


def test_direct_boolean_implication_avoids_invalid_numeric_comparison():
    model = {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [
            {"name": "production", "sort": "Int", "shape": [1]},
            {"name": "template_used", "sort": "Bool", "shape": [1]},
        ],
        "functions": [],
        "constraints": [{"expr": {"op": "implies", "args": [
            {"op": "gt", "args": [at("production", 0), lit(0)]},
            at("template_used", 0),
        ]}, "span": [0, 1]}],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }
    translated = build_hir(model, "If production is positive, the template is used.").translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    formula = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    production = z3.Array("production", z3.IntSort(context), z3.IntSort(context))
    used = z3.Array("template_used", z3.IntSort(context), z3.BoolSort(context))
    for amount, is_used, expected in [(1, False, False), (1, True, True), (0, False, True)]:
        solver = z3.Solver(ctx=context)
        solver.set(timeout=5000)
        solver.add(formula, z3.Select(production, 0) == amount,
                   z3.Select(used, 0) == is_used)
        result = solver.check()
        assert result != z3.unknown, solver.reason_unknown()
        assert (result == z3.sat) is expected
