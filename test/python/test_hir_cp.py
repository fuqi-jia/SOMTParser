"""CP constructor contracts checked against independent finite predicates."""
import itertools
import pytest
import z3
import somtparser as sp
from somtparser.hir_cp import build_cp_hir, expand_cp_model, CpProvider, cp_api
from somtparser._nl_model import ModelError


def lit(n):
    return {"literal": n, "sort": "Int"}


def var(n):
    return {"var": n}


def op(n, *args):
    return {"op": n, "args": list(args)}


def model(expr, declarations=()):
    return dict(
        schema="somt-hir-model-v1",
        language="hir",
        decision="satisfiability",
        declarations=list(declarations),
        functions=[],
        constraints=[dict(expr=expr, span=[0, 1])],
        objectives=[],
        objective_order="single",
        goal=None,
        assumptions=[],
        unresolved=[],
    )


def formula(expr, declarations=()):
    t = build_cp_hir(model(expr, declarations), "x").translate()
    assert t.ok, [d.message for d in t.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(t.to_smt2()))


def truth(expr, expected):
    f = formula(expr)
    s = z3.Solver()
    s.set(timeout=5000)
    s.add(f)
    assert s.check() == (z3.sat if expected else z3.unsat)


def test_circuit_and_its_negation_all_functions():
    for successors in itertools.product(range(3), repeat=3):
        node = 0
        seen = set()
        for _ in range(3):
            seen.add(node)
            node = successors[node]
        expected = len(seen) == 3 and node == 0
        e = {"cp": "circuit", "successors": [lit(x) for x in successors]}
        truth(e, expected)
        truth(op("not", e), not expected)
    truth({"cp": "circuit", "successors": [lit(0)]}, True)


def test_regular_nondeterminism_empty_word_and_negation():
    transitions = [[0, 0, 0], [0, 0, 1], [1, 1, 2], [2, 0, 2]]
    for n in range(4):
        for word in itertools.product(range(2), repeat=n):
            states = {0}
            for symbol in word:
                states = {c for a, b, c in transitions if a in states and b == symbol}
            expected = 2 in states
            e = {
                "cp": "regular",
                "items": [lit(x) for x in word],
                "start": 0,
                "finals": [2],
                "transitions": transitions,
            }
            truth(e, expected)
            truth(op("not", e), not expected)
    truth(
        {"cp": "regular", "items": [], "start": 7, "finals": [7], "transitions": []},
        True,
    )


def test_cumulative_matches_time_grid_including_zero_duration():
    for starts in itertools.product(range(-1, 2), repeat=2):
        for durations in itertools.product(range(3), repeat=2):
            demands = [1, 2]
            capacity = 2
            expected = all(
                sum(
                    demands[i]
                    for i in range(2)
                    if starts[i] <= t < starts[i] + durations[i]
                )
                <= capacity
                for t in range(-1, 4)
            )
            truth(
                {
                    "cp": "cumulative",
                    "starts": [lit(v) for v in starts],
                    "durations": list(durations),
                    "demands": demands,
                    "capacity": lit(capacity),
                },
                expected,
            )
    truth(
        {
            "cp": "cumulative",
            "starts": [],
            "durations": [],
            "demands": [],
            "capacity": lit(-1),
        },
        False,
    )


def test_nonoverlap_lex_table_and_total_element():
    truth({"cp": "no_overlap", "starts": [lit(0), lit(1)], "durations": [3, 0]}, True)
    truth({"cp": "no_overlap", "starts": [lit(0), lit(1)], "durations": [3, 1]}, False)
    for a, b in itertools.product(itertools.product(range(2), repeat=2), repeat=2):
        for strict in [False, True]:
            truth(
                {
                    "cp": "lex",
                    "left": [lit(v) for v in a],
                    "right": [lit(v) for v in b],
                    "strict": strict,
                },
                a < b if strict else a <= b,
            )
    truth(
        {
            "cp": "table",
            "items": [lit(1), lit(2)],
            "tuples": [[1, 2]],
            "positive": True,
        },
        True,
    )
    truth(
        {
            "cp": "table",
            "items": [lit(1), lit(2)],
            "tuples": [[1, 2]],
            "positive": False,
        },
        False,
    )
    truth(
        op(
            "eq",
            {
                "cp": "element",
                "items": [lit(4), lit(7)],
                "index": lit(-1),
                "default": lit(99),
            },
            lit(99),
        ),
        True,
    )


def test_min_max_abs_sum_and_vector_access():
    for values in itertools.product(range(-1, 2), repeat=3):
        for kind, expected in [
            ("minimum", min(values)),
            ("maximum", max(values)),
            ("sum", sum(values)),
        ]:
            truth(
                op(
                    "eq", {"cp": kind, "items": [lit(v) for v in values]}, lit(expected)
                ),
                True,
            )
    truth(op("eq", {"cp": "abs", "value": lit(-4)}, lit(4)), True)
    e = {"cp": "all_different", "items": {"array": "x", "length": 3}}
    f = formula(e, [dict(name="x", sort="Int", shape=[3], lower=0, upper=2)])
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    s = z3.Solver()
    s.add(f, x[0] == x[1])
    assert s.check() == z3.unsat


def test_multidimensional_cp_vector_diagnostic_and_native_flattening():
    declaration = dict(name="square", sort="Int", shape=[4, 4], lower=1, upper=16)
    malformed = model(
        {"cp": "all_different", "items": {"array": "square", "length": 16}},
        [declaration],
    )
    with pytest.raises(ModelError, match="CP vector descriptor.*final-axis.*native HIR all_different"):
        build_cp_hir(malformed, "x")

    whole_array = model({"op": "all_different", "args": [var("square")]}, [declaration])
    assert build_cp_hir(whole_array, "x").translate().ok

    row = model(
        {"cp": "all_different", "items": {"array": "square", "length": 4,
                                              "prefix": [lit(0)]}},
        [declaration],
    )
    assert build_cp_hir(row, "x").translate().ok



@pytest.mark.parametrize("expression", [
    {"cp": "regular", "items": {"array": "matrix", "length": 2},
     "start": 0, "finals": [0], "transitions": [[0, 0, 0]]},
    {"cp": "cumulative", "starts": {"array": "matrix", "length": 2},
     "durations": [1, 1], "demands": [1, 1], "capacity": lit(2)},
    {"cp": "diffn", "dimensions": 2,
     "positions": [{"array": "matrix", "length": 2}], "sizes": [[1, 1]],
     "nonstrict": False},
    op("eq", {"cp": "among", "items": {"array": "matrix", "length": 2},
               "values": [0]}, lit(0)),
])
def test_native_cp_globals_share_finite_vector_rank_validation(expression):
    with pytest.raises(ModelError, match="CP vector descriptor.*fixed prefix"):
        build_cp_hir(model(expression, [dict(name="matrix", sort="Int", shape=[2, 2])]), "x")


def test_cp_vector_shape_uses_lexical_array_binding():
    inner = {"cp": "all_different", "items": {"array": "a", "length": 3}}
    expression = {"quantifier": "exists",
                  "binders": [{"name": "a", "sort": {"Array": ["Int", "Int"]}}],
                  "body": inner}
    declarations = [dict(name="a", sort="Int", shape=[1, 2], lower=0, upper=1)]
    original = model(expression, declarations)
    # Both construction routes must let the quantified one-dimensional array
    # shadow the unrelated two-dimensional global declaration.
    for candidate in (original, expand_cp_model(original)):
        translated = build_cp_hir(candidate, "x").translate()
        assert translated.ok
        solver = z3.Solver()
        solver.add(z3.parse_smt2_string(translated.to_smt2()))
        assert solver.check() == z3.sat
    # Leaving the quantifier restores the outer declaration's finite rank.
    with pytest.raises(ModelError, match="CP vector descriptor.*fixed prefix"):
        expand_cp_model(model(op("and", expression, inner), declarations))


def test_cp_table_missing_polarity_has_repairable_diagnostic():
    malformed = model({"cp": "table", "items": [lit(1)], "tuples": [[1]]})
    with pytest.raises(ModelError, match="requires the Boolean field 'positive'.*allowed.*forbidden"):
        expand_cp_model(malformed)


def test_constructor_metadata_states_vector_shape_and_table_polarity():
    api = cp_api()
    assert "does not flatten dimensions" in api["vector"]
    assert "prefix fixes every axis before the final axis" in api["vector"]
    polarity = api["constructors"]["table"]["positive"]
    assert "required Boolean" in polarity
    assert "true allows listed tuples" in polarity
    assert "false forbids them" in polarity


def test_fresh_witness_avoids_capture_and_preserves_source_model():
    e = {"cp": "circuit", "successors": [var("somt_cp_witness_1")]}
    m = model(e, [dict(name="somt_cp_witness_1", sort="Int", lower=0, upper=0)])
    expanded = expand_cp_model(m)
    assert "cp" in m["constraints"][0]["expr"]
    assert (
        expanded["constraints"][0]["expr"]["binders"][0]["name"] != "somt_cp_witness_1"
    )
    assert build_cp_hir(m, "x").translate().ok


@pytest.mark.parametrize(
    "e",
    [
        {"cp": "circuit", "successors": []},
        {"cp": "minimum", "items": []},
        {
            "cp": "cumulative",
            "starts": [lit(0)],
            "durations": [-1],
            "demands": [1],
            "capacity": lit(2),
        },
        {"cp": "regular", "items": [], "start": 0, "finals": [True], "transitions": []},
        {"cp": "table", "items": [lit(1)], "tuples": [[1, 2]], "positive": True},
        {"cp": "unknown"},
    ],
)
def test_invalid_cp_data_is_refused(e):
    with pytest.raises(ModelError):
        expand_cp_model(model(e))


def test_provider_supplies_catalog_and_native_pipeline():
    def underlying(request):
        assert "cp_constructor_api" in request["context"]
        return model({"cp": "all_different", "items": [lit(1), lit(2)]})

    provider = CpProvider(underlying)
    c = sp.propose_nl("x", language="hir", provider=provider)
    assert c.valid, c.diagnostics
    t = sp.compile_candidate(c, accept_digest=c.digest)
    assert t.ok
    assert t.report()["formal_translation"]["provenance"]["language_id"] == "hir"
    assert provider.last_cp_model["constraints"][0]["expr"]["cp"] == "all_different"
