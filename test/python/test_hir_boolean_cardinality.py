"""Boolean CP cardinality constructors use linear-size HIR counts."""
import itertools

import pytest
z3 = pytest.importorskip("z3")

from somtparser._nl_model import ModelError
from somtparser.hir import HirBuilder, build_hir, hir_api
from somtparser.hir_cp import expand_cp_expression, expand_cp_model


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(operator, *args):
    return {"op": operator, "args": list(args)}


def model(expr, declarations=(), source="x"):
    return {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": list(declarations),
        "functions": [],
        "constraints": [{"expr": expr, "span": [0, len(source)]}],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


def translated_relation(candidate):
    result = build_hir(candidate, "x").translate()
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def matches_assignments(formula, variables, assignments, expected):
    solver = z3.Solver()
    for values, want in zip(assignments, expected):
        solver.push()
        solver.add(formula)
        solver.add(*[variable == value for variable, value in zip(variables, values)])
        assert (solver.check() == z3.sat) is want, (values, want)
        solver.pop()


def test_count_true_matches_position_count_and_preserves_repeats():
    candidate = model(
        op(
            "eq",
            {"cp": "count_true", "items": [var("a"), var("b"), var("a")]},
            var("n"),
        ),
        [
            {"name": "a", "sort": "Bool"},
            {"name": "b", "sort": "Bool"},
            {"name": "n", "sort": "Int"},
        ],
    )
    formula = translated_relation(candidate)
    assignments, expected = [], []
    for a, b in itertools.product([False, True], repeat=2):
        for count in range(4):
            assignments.append((a, b, count))
            expected.append(count == 2 * int(a) + int(b))
    matches_assignments(
        formula,
        [z3.Bool("a"), z3.Bool("b"), z3.Int("n")],
        assignments,
        expected,
    )


def test_at_most_one_matches_pairwise_exclusion_including_repeated_positions():
    names = ["a", "b", "c"]
    candidate = model(
        op(
            "eq",
            {"cp": "at_most_one", "items": [var("a"), var("b"), var("a"), var("c")]},
            var("answer"),
        ),
        [{"name": name, "sort": "Bool"} for name in names]
        + [{"name": "answer", "sort": "Bool"}],
    )
    formula = translated_relation(candidate)
    assignments, expected = [], []
    for bits in itertools.product([False, True], repeat=len(names)):
        a, b, c = bits
        pairwise = not (
            (a and b) or (a and a) or (a and c)
            or (b and a) or (b and c) or (a and c)
        )
        for answer in [False, True]:
            assignments.append(bits + (answer,))
            expected.append(answer is pairwise)
    matches_assignments(
        formula,
        [z3.Bool(name) for name in names] + [z3.Bool("answer")],
        assignments,
        expected,
    )


def test_boolean_cardinality_expansion_is_linear_and_preserves_spans():
    names = [f"b{i}" for i in range(64)]
    expanded = expand_cp_expression(
        {"cp": "at_most_one", "items": [var(name) for name in names]}
    )
    assert expanded["op"] == "le"
    count = expanded["args"][0]
    assert count["op"] == "count"
    assert len(count["args"]) == len(names)
    assert count["args"] == [var(name) for name in names]
    assert expanded["args"][1] == lit(1)

    raw = model(
        {"cp": "count_true", "items": [var("b")]},
        [{"name": "b", "sort": "Bool"}],
        source="b is Boolean",
    )
    raw["constraints"][0]["span"] = [2, 12]
    expanded_model = expand_cp_model(raw)
    assert expanded_model["constraints"][0]["span"] == [2, 12]


def test_empty_boolean_cardinality_has_exact_identities_and_catalog_entries():
    assert expand_cp_expression({"cp": "count_true", "items": []}) == lit(0)
    assert expand_cp_expression({"cp": "at_most_one", "items": []}) == lit(True, "Bool")
    catalog = hir_api()["cp_constructors"]["constructors"]
    assert catalog["count_true"]["items"].startswith("Bool vector")
    assert catalog["at_most_one"]["items"].startswith("Bool vector")


@pytest.mark.parametrize("kind", ["count_true", "at_most_one"])
@pytest.mark.parametrize("sort", ["Int", "Real"])
def test_boolean_cardinality_rejects_non_bool_items(kind, sort):
    builder = HirBuilder()
    builder.declare("x", sort)
    with pytest.raises(ModelError, match="Boolean operands required"):
        builder.expr({"cp": kind, "items": [var("x")]})


@pytest.mark.parametrize("kind", ["count_true", "at_most_one"])
@pytest.mark.parametrize("value", [0, 1])
def test_boolean_cardinality_rejects_int_indicator_literals(kind, value):
    with pytest.raises(ModelError, match="Boolean operands required"):
        HirBuilder().expr({"cp": kind, "items": [lit(value, "Int")]})


@pytest.mark.parametrize("kind", ["count_true", "at_most_one"])
def test_boolean_cardinality_reuses_vector_limit(kind):
    items = [lit(True, "Bool")] * 1001
    with pytest.raises(ModelError, match="CP vector exceeds 1000 elements"):
        expand_cp_expression({"cp": kind, "items": items})


def test_boolean_array_vector_keeps_exact_bool_element_sort():
    builder = HirBuilder()
    builder.declare("flags", "Bool", shape=[3])
    expression = builder.expr(
        {"cp": "count_true", "items": {"array": "flags", "length": 3}}
    )
    assert repr(expression.sort) == "Int"

    builder = HirBuilder()
    builder.declare("values", "Int", shape=[3])
    with pytest.raises(ModelError, match="Boolean operands required"):
        builder.expr(
            {"cp": "count_true", "items": {"array": "values", "length": 3}}
        )
