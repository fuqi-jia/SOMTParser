"""CP operands remain typed and scoped even when their relation is vacuous."""
from copy import deepcopy

import jsonschema
import pytest
import z3

import somtparser as sp
from somtparser._nl_model import ModelError
from somtparser.hir import HirBuilder, build_hir, hir_schema
from somtparser.hir_cp import CpProvider, expand_cp_expression, expand_cp_model, expand_cp_vector


ROUTES = ("direct", "expanded", "provider")


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def candidate(expr, declarations=()):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=list(declarations), functions=[],
                constraints=[dict(expr=expr, span=[0, 1])], objectives=[],
                objective_order="single", goal=None, assumptions=[], unresolved=[])


def translate(raw, route):
    before = deepcopy(raw)
    try:
        if route == "provider":
            provider = CpProvider(lambda _request: deepcopy(raw))
            proposal = sp.propose_nl("x", language="hir", provider=provider)
            if not proposal.valid:
                raise ModelError(str(proposal.diagnostics))
            result = sp.compile_candidate(proposal, accept_digest=proposal.digest)
        else:
            source = expand_cp_model(raw) if route == "expanded" else raw
            result = build_hir(source, "x").translate()
        assert result.ok, [d.message for d in result.diagnostic_items]
        return z3.And(*z3.parse_smt2_string(result.to_smt2()))
    finally:
        assert raw == before


def prove_same(actual, expected):
    proof = z3.Solver()
    proof.add(z3.Xor(actual, expected))
    assert proof.check() == z3.unsat, proof.reason_unknown()
    witness = z3.Solver()
    witness.add(actual)
    assert witness.check() == z3.sat, witness.reason_unknown()


BAD_CALLS = [
    (op("eq", {"cp": "element", "items": [lit(7)], "index": lit("1/2", "Real"), "default": lit(0)}, lit(0)), []),
    (op("eq", {"cp": "element", "items": [], "index": lit("1/2", "Real"), "default": lit(0)}, lit(0)), []),
    (op("eq", {"cp": "element", "items": [], "index": lit(True, "Bool"), "default": lit(0)}, lit(0)), []),
    (op("eq", {"cp": "element", "items": [], "index": var("missing"), "default": lit(0)}, lit(0)), []),
    ({"cp": "no_overlap", "starts": [var("missing")], "durations": [0]}, []),
    ({"cp": "no_overlap", "starts": [lit("1/2", "Real")], "durations": [0]}, []),
    ({"cp": "no_overlap", "starts": [lit(True, "Bool")], "durations": [0]}, []),
    (op("eq", {"cp": "sum", "items": {"array": "missing", "length": 0}}, lit(0)), []),
    (op("eq", {"cp": "sum", "items": {"array": "a", "length": 0}}, lit(0)), [dict(name="a", sort="Int")]),
    (op("eq", {"cp": "sum", "items": {"array": "a", "length": 0, "prefix": [var("missing")]}}, lit(0)),
     [dict(name="a", sort={"Array": ["Int", {"Array": ["Int", "Int"]}]})]),
    (op("eq", {"cp": "sum", "items": {"array": "a", "length": 0, "prefix": [lit(True, "Bool")]}}, lit(0)),
     [dict(name="a", sort={"Array": ["Int", {"Array": ["Int", "Int"]}]})]),
    (op("eq", {"cp": "sum", "items": {"array": "a", "length": 0}}, lit(0)), [dict(name="a", sort="Int", shape=[2, 0])]),
]


@pytest.mark.parametrize("route", ROUTES)
@pytest.mark.parametrize("expr,declarations", BAD_CALLS)
def test_erased_operands_still_require_their_declared_type_and_scope(route, expr, declarations):
    with pytest.raises((ModelError, ValueError)):
        translate(candidate(expr, declarations), route)


@pytest.mark.parametrize("route", ROUTES)
@pytest.mark.parametrize("kind", ("element", "no_overlap"))
def test_erased_operand_with_correct_outer_sort_still_checks_its_inner_select(route, kind):
    bad = {"at": "a", "indices": [lit(True, "Bool")]}
    expr = (op("eq", {"cp": "element", "items": [], "index": bad, "default": lit(0)}, lit(0))
            if kind == "element" else {"cp": "no_overlap", "starts": [bad], "durations": [0]})
    with pytest.raises((ModelError, ValueError)):
        translate(candidate(expr, [dict(name="a", sort={"Array": ["Int", "Int"]})]), route)


@pytest.mark.parametrize("route", ROUTES)
@pytest.mark.parametrize("kind", ("sum", "count_true", "at_most_one", "among", "global_cardinality", "table", "regular", "cumulative"))
def test_empty_descriptor_is_checked_in_expanded_and_native_paths(route, kind):
    vector = {"array": "missing", "length": 0}
    expressions = {
        "sum": op("eq", {"cp": "sum", "items": vector}, lit(0)),
        "count_true": op("eq", {"cp": "count_true", "items": vector}, lit(0)),
        "at_most_one": {"cp": "at_most_one", "items": vector},
        "among": op("eq", {"cp": "among", "items": vector, "values": []}, lit(0)),
        "global_cardinality": {"cp": "global_cardinality", "items": vector, "values": [], "counts": [], "closed": False},
        "table": {"cp": "table", "items": vector, "tuples": [[]], "positive": True},
        "regular": {"cp": "regular", "items": vector, "start": 0, "finals": [0], "transitions": []},
        "cumulative": {"cp": "cumulative", "starts": vector, "durations": [], "demands": [], "capacity": lit(0)},
    }
    with pytest.raises((ModelError, ValueError)):
        translate(candidate(expressions[kind]), route)


@pytest.mark.parametrize("route", ROUTES)
def test_empty_shaped_array_remains_total_without_a_fabricated_domain_constraint(route):
    element = {"cp": "element", "items": {"array": "a", "length": 0},
               "index": var("i"), "default": var("d")}
    expr = op("and", op("eq", element, var("d")),
              op("eq", {"at": "a", "indices": [lit(0)]}, lit(42)))
    declarations = [dict(name="a", sort="Int", shape=[0]), dict(name="i", sort="Int"), dict(name="d", sort="Int")]
    actual = translate(candidate(expr, declarations), route)
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    prove_same(actual, z3.Select(a, 0) == 42)


@pytest.mark.parametrize("route", ROUTES)
def test_bool_prefix_index_and_nested_element_inside_negation_and_array_index(route):
    element = {"cp": "element", "items": {"array": "a", "length": 2, "prefix": [lit(True, "Bool")]},
               "index": var("i"), "default": var("d")}
    expr = op("not", {"at": "b", "indices": [element]})
    declarations = [dict(name="a", sort={"Array": ["Bool", {"Array": ["Int", "Int"]}]}),
                    dict(name="b", sort={"Array": ["Int", "Bool"]}), dict(name="i", sort="Int"), dict(name="d", sort="Int")]
    actual = translate(candidate(expr, declarations), route)
    a = z3.Array("a", z3.BoolSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    b = z3.Array("b", z3.IntSort(), z3.BoolSort())
    i, d = z3.Ints("i d")
    selected = z3.If(i == 0, z3.Select(z3.Select(a, True), 0), z3.If(i == 1, z3.Select(z3.Select(a, True), 1), d))
    prove_same(actual, z3.Not(z3.Select(b, selected)))


@pytest.mark.parametrize("route", ROUTES)
def test_empty_descriptor_respects_quantified_array_shadowing_and_bool_prefix(route):
    empty = {"cp": "sum", "items": {"array": "a", "length": 0, "prefix": [var("p")]}}
    quantified = {"quantifier": "forall", "binders": [
        dict(name="a", sort={"Array": ["Bool", {"Array": ["Int", "Int"]}]}), dict(name="p", sort="Bool")],
        "body": op("eq", empty, lit(0))}
    expr = op("and", quantified, op("eq", var("a"), lit(7)))
    actual = translate(candidate(expr, [dict(name="a", sort="Int")]), route)
    prove_same(actual, z3.Int("a") == 7)


@pytest.mark.parametrize("route", ROUTES)
def test_zero_duration_start_is_typed_without_adding_any_scheduling_restriction(route):
    relation = {"cp": "no_overlap", "starts": [var("s"), var("t")], "durations": [0, 2]}
    expr = op("and", relation, op("eq", var("s"), lit(-10)), op("eq", var("t"), lit(9)))
    actual = translate(candidate(expr, [dict(name="s", sort="Int"), dict(name="t", sort="Int")]), route)
    s, t = z3.Ints("s t")
    prove_same(actual, z3.And(s == -10, t == 9))


@pytest.mark.parametrize("route", ROUTES)
def test_no_overlap_guard_stays_inside_negation(route):
    relation = {"cp": "no_overlap", "starts": [var("s"), var("t")], "durations": [2, 1]}
    actual = translate(candidate(op("not", relation), [dict(name="s", sort="Int"), dict(name="t", sort="Int")]), route)
    s, t = z3.Ints("s t")
    prove_same(actual, z3.Not(z3.Or(s + 2 <= t, t + 1 <= s)))



@pytest.mark.parametrize("kind", ("element", "no_overlap"))
def test_direct_construction_visits_shared_operands_once_per_call(kind):
    class CountedBuilder(HirBuilder):
        def __init__(self):
            super().__init__()
            self.visits = {}

        def _expr_uncached(self, expr, *args, **kwargs):
            self.visits[id(expr)] = self.visits.get(id(expr), 0) + 1
            return super()._expr_uncached(expr, *args, **kwargs)

    for size in (8, 32, 96):
        builder = CountedBuilder()
        builder.declare("x", "Int")
        shared = op("add", var("x"), lit(1))
        expr = ({"cp": "element", "items": [shared] * size,
                 "index": lit(0), "default": shared}
                if kind == "element" else
                {"cp": "no_overlap", "starts": [shared] * size, "durations": [0] * size})
        result = builder.expr(expr)
        assert builder.visits[id(shared)] == 1
        if kind == "element":
            result = builder._op("eq", [result, result])
        builder.model.constrain(result)
        builder.validate()
        # The guard is check-only and the source subtree traversal stays
        # constant for shared objects; arithmetic relation construction is
        # linear here (no active no_overlap pairs).
        assert builder.nodes <= 8 * size + 32

def test_public_empty_vector_expansion_keeps_its_structural_list_contract():
    assert expand_cp_vector({"array": "unresolved_until_build", "length": 0}) == []
    expanded = expand_cp_expression({"cp": "sum", "items": []})
    builder = HirBuilder()
    builder.declare("result", "Int")
    builder.constrain(op("eq", var("result"), expanded))
    translated = builder.translate(dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    loaded = z3.Optimize()
    loaded.from_string(translated.to_smt2(dialect=sp.OmtDialect.Z3))
    assert len(loaded.objectives()) == 0
    prove_same(z3.And(*loaded.assertions()), z3.Int("result") == 0)


@pytest.mark.parametrize("operator", ("connected", "dconnected"))
def test_graph_schema_does_not_truncate_its_published_operand_limit(operator):
    # No solver or enormous graph lowering: this tests schema and typed source
    # construction at the previously inconsistent boundary (10003 operands).
    n = 10001
    expr = op(operator, lit(n), lit(0), *[lit(True, "Bool") for _ in range(n)])
    raw = candidate(expr)
    validator = jsonschema.Draft202012Validator(hir_schema())
    validator.validate(raw)
    built = build_hir(raw, "x")
    assert not [d for d in built.validate() if d.severity == sp.Severity.ERROR]
    # The wider common schema must not relax the smaller arithmetic arities.
    invalid = candidate(op("eq", op("add", *[lit(0) for _ in range(10001)]), lit(0)))
    assert not validator.is_valid(invalid)
