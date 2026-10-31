"""Independent finite graph semantics for optional-node successor circuits."""
from copy import deepcopy
import itertools

import jsonschema
import pytest
import somtparser as sp
import z3

from somtparser._nl_model import ModelError
from somtparser.hir import build_hir, hir_schema
from somtparser.hir_cp import CpProvider, expand_cp_model


def literal(value, sort="Int"):
    return dict(literal=value, sort=sort)


def call(successors, allow_empty):
    return dict(cp="subcircuit", successors=successors, allow_empty=allow_empty)


def model(expression, declarations=()):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=list(declarations), functions=[],
                constraints=[dict(expr=expression, span=[0, 1])],
                objectives=[], objective_order="single", goal=None,
                assumptions=[], unresolved=[])


def translation(raw, route="direct"):
    if route == "provider":
        candidate = sp.propose_nl("x", language="hir", provider=CpProvider(lambda _: deepcopy(raw)))
        if not candidate.valid:
            raise ModelError(str(candidate.diagnostics))
        translated = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    else:
        translated = build_hir(expand_cp_model(raw) if route == "expanded" else raw, "x").translate()
    if not translated.ok:
        raise ModelError(str(translated.diagnostic_items))
    return translated


def independent(successors, allow_empty):
    n = len(successors)
    if any(x < 0 or x >= n for x in successors) or len(set(successors)) != n:
        return False
    active = {i for i, x in enumerate(successors) if x != i}
    if not active:
        return allow_empty
    start = min(active)
    seen, node = set(), start
    while node not in seen:
        seen.add(node)
        node = successors[node]
    return node == start and seen == active


def check(successors, allow_empty, route="direct"):
    expected = independent(successors, allow_empty)
    expression = call([literal(x) for x in successors], allow_empty)
    for negated in (False, True):
        predicate = dict(op="not", args=[expression]) if negated else expression
        translated = translation(model(predicate), route)
        solver = z3.Solver()
        solver.add(*z3.parse_smt2_string(translated.to_smt2()))
        assert solver.check() == (z3.sat if expected != negated else z3.unsat), (
            successors, allow_empty, route, negated, solver.reason_unknown())


@pytest.mark.parametrize("allow_empty", [False, True])
def test_all_small_successor_functions_and_their_negations(allow_empty):
    for n in range(4):
        for successors in itertools.product(range(n), repeat=n):
            check(successors, allow_empty)
    for successors in [(-1, 0), (2, 0), (1, 0, 3, 2), (0, 2, 3, 1)]:
        check(successors, allow_empty)


@pytest.mark.parametrize("route", ["expanded", "provider"])
@pytest.mark.parametrize("allow_empty", [False, True])
def test_public_routes_preserve_inactive_nodes_and_reject_disjoint_subtours(route, allow_empty):
    for successors in [(), (0,), (0, 1, 2), (0, 2, 1), (1, 0, 3, 2)]:
        check(successors, allow_empty, route)


@pytest.mark.parametrize("route", ["direct", "expanded", "provider"])
@pytest.mark.parametrize("expression,declarations", [
    (dict(cp="subcircuit", successors=[literal(0)]), []),
    (call([literal(0)], 1), []),
    (call([literal(True, "Bool")], True), []),
    (call([literal("0", "Real")], True), []),
    (call([dict(var="missing")], True), []),
    (call(dict(array="missing", length=0), True), []),
    (call(dict(array="x", length=0), True), [dict(name="x", sort="Int")]),
])
def test_invalid_or_erased_operands_are_not_accepted(expression, declarations, route):
    with pytest.raises((ModelError, ValueError)):
        translation(model(expression, declarations), route)


def test_named_operator_schema_and_lexical_witness_scope():
    # The public variable uses the generated-name stem deliberately. An outer
    # quantifier also shadows it; neither may be captured by the local ranks.
    variable = "somt_cp_witness_1"
    expression = {"quantifier": "forall", "binders": [dict(name=variable, sort="Int")],
        "body": dict(op="implies", args=[dict(op="eq", args=[dict(var=variable), literal(1)]),
            dict(op="subcircuit", successors=[dict(var=variable), literal(0), literal(2)], allow_empty=False)])}
    raw = model(expression, [dict(name=variable, sort="Int")])
    jsonschema.validate(raw, hir_schema())
    result = translation(raw)
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
