"""Standard HIR CP entry points and finite-cardinality constructor oracles."""
import itertools

import pytest
import z3

import somtparser as sp
from somtparser._nl_model import ModelError
from somtparser.hir import HirBuilder, build_hir, hir_api
from somtparser.hir_cp import (
    CpProvider,
    build_cp_hir,
    expand_cp_expression,
    expand_cp_model,
)


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(operator, *args):
    return {"op": operator, "args": list(args)}


def model(expr, declarations=(), data=None, source="x"):
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
        **({"data": data} if data is not None else {}),
    }


def translated_relation(candidate):
    result = build_hir(candidate, "x").translate()
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def refuses_translation(thunk):
    try:
        return not thunk().ok
    except ModelError:
        return True


def matches_at_assignments(formula, variables, assignments, expected):
    solver = z3.Solver()
    for assignment, want in zip(assignments, expected):
        solver.push()
        solver.add(formula)
        solver.add(*[v == value for v, value in zip(variables, assignment)])
        assert (solver.check() == z3.sat) is want, (assignment, want)
        solver.pop()


def test_standard_hir_catalog_and_candidate_pipeline_accept_cp_macros():
    source = "There are two selected values."
    raw = model(
        op(
            "eq",
            {"cp": "among", "items": [var("x"), var("y")], "values": [1, 1]},
            lit(2),
        ),
        [dict(name="x", sort="Int"), dict(name="y", sort="Int")],
        source=source,
    )
    schema = hir_api()
    assert "among" in schema["cp_constructors"]["constructors"]
    request_schemas = []
    candidate = sp.propose_nl(
        source,
        language="hir",
        provider=lambda request: request_schemas.append(request["schema"]) or raw,
    )
    assert candidate.valid, candidate.diagnostics
    assert "global_cardinality" in request_schemas[0]["constructor_api"]["cp_constructors"]["constructors"]
    assert candidate.model["constraints"][0]["expr"]["args"][0]["cp"] == "among"
    compiled = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert compiled.ok

    # The lower-level checked builder sees the same constructors directly.
    builder = HirBuilder()
    builder.declare("x", "Int")
    assert repr(
        builder.expr({"cp": "among", "items": [var("x")], "values": [0]}).sort
    ) == "Int"


def test_among_matches_exhaustive_finite_set_oracle_and_ignores_duplicate_values():
    names = ["x0", "x1", "x2"]
    declarations = [dict(name=name, sort="Int") for name in names]
    count_name = "observed"
    declarations.append(dict(name=count_name, sort="Int"))
    for number in range(len(names) + 1):
        candidate = model(
            op(
                "eq",
                {
                    "cp": "among",
                    "items": [var(name) for name in names],
                    "values": [1, 1, 2, 2],
                },
                var(count_name),
            ),
            declarations,
        )
        formula = translated_relation(candidate)
        assignments, expected = [], []
        for values in itertools.product(range(-1, 3), repeat=len(names)):
            want = sum(value in {1, 2} for value in values)
            assignments.extend([values + (number,)])
            expected.append(want == number)
        variables = [z3.Int(name) for name in names + [count_name]]
        matches_at_assignments(formula, variables, assignments, expected)


@pytest.mark.parametrize("closed", [False, True])
def test_global_cardinality_matches_exhaustive_open_and_closed_oracles(closed):
    item_names = ["x0", "x1"]
    count_names = ["n0", "n1"]
    declarations = [dict(name=name, sort="Int") for name in item_names + count_names]
    candidate = model(
        {
            "cp": "global_cardinality",
            "items": [var(name) for name in item_names],
            "values": [0, 1],
            "counts": [var(name) for name in count_names],
            "closed": closed,
        },
        declarations,
    )
    formula = translated_relation(candidate)
    assignments, expected = [], []
    for values in itertools.product(range(-1, 3), repeat=2):
        for counts in itertools.product(range(3), repeat=2):
            want = (
                counts[0] == values.count(0)
                and counts[1] == values.count(1)
                and (not closed or all(value in {0, 1} for value in values))
            )
            assignments.append(values + counts)
            expected.append(want)
    variables = [z3.Int(name) for name in item_names + count_names]
    matches_at_assignments(formula, variables, assignments, expected)


def test_empty_cardinality_cases_and_global_cardinality_negation():
    empty_among = model(
        op(
            "eq",
            {"cp": "among", "items": [], "values": []},
            lit(0),
        )
    )
    assert z3.is_true(z3.simplify(translated_relation(empty_among)))

    for closed in [False, True]:
        empty_global = model(
            {
                "cp": "global_cardinality",
                "items": [],
                "values": [],
                "counts": [],
                "closed": closed,
            }
        )
        assert z3.is_true(z3.simplify(translated_relation(empty_global)))

    negated = model(
        op(
            "not",
            {
                "cp": "global_cardinality",
                "items": [var("x")],
                "values": [0],
                "counts": [lit(1)],
                "closed": True,
            },
        ),
        [dict(name="x", sort="Int")],
    )
    formula = translated_relation(negated)
    matches_at_assignments(
        formula,
        [z3.Int("x")],
        [(-1,), (0,), (1,)],
        [True, False, True],
    )


def test_expansion_node_limit_is_shared_and_counting_macros_preflight_growth():
    too_large_expression = {"unrecognized": ["opaque"] * 100001}
    with pytest.raises(ModelError, match="expanded CP model exceeds 100000 JSON nodes"):
        expand_cp_expression(too_large_expression)

    oversized_model = model(
        {"var": "x"}, [dict(name="x", sort="Int")]
    )
    oversized_model["metadata"] = ["opaque"] * 100001
    with pytest.raises(ModelError, match="expanded CP model exceeds 100000 JSON nodes"):
        expand_cp_model(oversized_model)

    quadratic = {
        "cp": "among",
        "items": [var(f"x{i}") for i in range(100)],
        "values": list(range(1000)),
    }
    with pytest.raises(ModelError, match="expansion estimate exceeds"):
        expand_cp_expression(quadratic)


@pytest.mark.parametrize("closed", [False, True])
def test_native_cardinality_accepts_competition_sized_vectors(closed):
    size, classes = 200, 26
    assigned = [i % classes for i in range(size)]
    expression = {
        "cp": "global_cardinality",
        "items": {"array": "sequence", "length": size},
        "values": list(range(classes)),
        "counts": [lit(assigned.count(value)) for value in range(classes)],
        "closed": closed,
    }
    # This valid input used to fail before HIR construction because every
    # array access was copied into thousands of JSON equality/ITE trees.
    with pytest.raises(ModelError, match="expansion estimate exceeds"):
        expand_cp_expression(expression)
    relation = translated_relation(model(
        expression, [dict(name="sequence", sort="Int", shape=[size])]
    ))
    sequence = z3.Array("sequence", z3.IntSort(), z3.IntSort())
    witness = z3.K(z3.IntSort(), 0)
    for index, value in enumerate(assigned):
        witness = z3.Store(witness, index, value)
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(relation, sequence == witness)
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(relation, sequence == z3.Store(witness, 0, classes + 1))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("sort", ["Bool", "Real"])
@pytest.mark.parametrize("kind", ["among", "global_cardinality"])
def test_finite_cardinality_requires_exact_int_operands_even_when_vacuous(sort, kind):
    builder = HirBuilder()
    builder.declare("x", sort)
    expression = (
        {"cp": "among", "items": [var("x")], "values": []}
        if kind == "among"
        else {
            "cp": "global_cardinality",
            "items": [var("x")],
            "values": [],
            "counts": [],
            "closed": False,
        }
    )
    with pytest.raises(ModelError, match="exact sort Int"):
        builder.expr(expression)


@pytest.mark.parametrize("sort", ["Bool", "Real"])
@pytest.mark.parametrize("path", ["standard", "nested", "legacy", "provider"])
def test_exact_int_guards_survive_all_standard_and_legacy_expansion_paths(sort, path):
    declaration = [dict(name="x", sort=sort)]
    if path == "nested":
        cp_expr = {
            "cp": "sum",
            "items": [
                {"cp": "among", "items": [var("x")], "values": []}
            ],
        }
        expression = op("eq", cp_expr, lit(0))
    elif path == "legacy":
        expression = {
            "cp": "global_cardinality",
            "items": [var("x")],
            "values": [],
            "counts": [],
            "closed": False,
        }
    else:
        expression = op(
            "eq",
            {"cp": "among", "items": [var("x")], "values": []},
            lit(0),
        )
    candidate = model(expression, declaration)

    if path == "legacy":
        assert refuses_translation(lambda: build_cp_hir(candidate, "x").translate())
    elif path == "provider":
        provider = CpProvider(lambda _request: candidate)
        proposed = sp.propose_nl("x", language="hir", provider=provider)
        assert not proposed.valid
    else:
        assert refuses_translation(lambda: build_hir(candidate, "x").translate())


def test_global_cardinality_requires_distinct_values_and_typed_counts():
    with pytest.raises(ModelError, match="values must be distinct"):
        from somtparser.hir_cp import expand_cp_expression

        expand_cp_expression(
            {
                "cp": "global_cardinality",
                "items": [],
                "values": [2, 2],
                "counts": [lit(0), lit(0)],
                "closed": True,
            }
        )
    builder = HirBuilder()
    builder.declare("x", "Int")
    builder.declare("b", "Bool")
    with pytest.raises(ModelError, match="exact sort Int"):
        builder.expr(
            {
                "cp": "global_cardinality",
                "items": [var("x")],
                "values": [0],
                "counts": [var("b")],
                "closed": False,
            }
        )


def test_data_lookup_checks_empty_table_rank_and_index_sort():
    source = "x"
    valid = model(
        op(
            "eq",
            {"data": "empty", "indices": [lit(4)], "default": lit(7)},
            lit(7),
        ),
        [dict(name="i", sort="Int")],
        data={"empty": []},
        source=source,
    )
    assert z3.is_true(z3.simplify(translated_relation(valid)))

    bad_index = model(
        op(
            "eq",
            {"data": "empty", "indices": [var("flag")], "default": lit(7)},
            lit(7),
        ),
        [dict(name="flag", sort="Bool")],
        data={"empty": []},
        source=source,
    )
    with pytest.raises(ModelError, match="indices must have sort Int"):
        build_hir(bad_index, source)

    bad_rank = model(
        op(
            "eq",
            {
                "data": "empty",
                "indices": [lit(0), lit(0)],
                "default": lit(7),
            },
            lit(7),
        ),
        data={"empty": []},
        source=source,
    )
    with pytest.raises(ModelError, match="index count does not match table rank"):
        build_hir(bad_rank, source)


def test_data_lookup_checks_rectangular_rank_and_default_leaf_sort():
    def candidate(table, default):
        return model(
            op(
                "eq",
                {
                    "data": "table",
                    "indices": [lit(0), lit(0)],
                    "default": default,
                },
                default,
            ),
            data={"table": table},
        )

    with pytest.raises(ModelError, match="rectangular and have uniform rank"):
        build_hir(candidate([[1], [2, 3]], lit(0)), "x")
    with pytest.raises(ModelError, match="default sort does not match table leaves"):
        build_hir(candidate([[1]], lit("0", "Real")), "x")
