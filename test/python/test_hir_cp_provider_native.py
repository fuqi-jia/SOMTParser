"""Provider composition must retain the compact, fully checked HIR route."""
from copy import deepcopy
import json

import pytest
import somtparser as sp
import z3

from somtparser.hir_cp import CpProvider


def literal(value):
    return {"literal": value, "sort": "Int"}


def variable(name):
    return {"var": name}


def operation(name, *args):
    return {"op": name, "args": list(args)}


def model(expression, declarations=()):
    return dict(schema="somt-hir-model-v1", language="hir",
                decision="satisfiability", declarations=list(declarations),
                functions=[], constraints=[dict(expr=expression, span=[0, 1])],
                objectives=[], objective_order="single", goal=None,
                assumptions=[], unresolved=[])


def propose(raw):
    provider = CpProvider(lambda request: deepcopy(raw))
    candidate = sp.propose_nl("x", language="hir", provider=provider)
    assert candidate.valid, candidate.diagnostics
    assert provider.last_cp_model == raw
    translated = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert translated.ok, translated.report()
    return translated


def test_provider_large_extremum_does_not_materialize_a_json_tree():
    # This compact call is valid; expanding the balanced ite tree for 512
    # operands exceeds the explicit JSON expansion budget before translation.
    raw = model(operation("eq", {"cp": "minimum",
                "items": [literal(i - 256) for i in range(512)]}, literal(-256)))
    provider = CpProvider(lambda request: raw)
    response = provider(dict(language="hir", context={}, instruction=""))
    assert response == raw
    assert len(json.dumps(response)) < 25000
    response["constraints"][0]["expr"]["args"][0]["items"].clear()
    assert len(provider.last_cp_model["constraints"][0]["expr"]["args"][0]["items"]) == 512
    translated = propose(raw)
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(translated.to_smt2()))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
@pytest.mark.parametrize("negated", [False, True])
def test_provider_extrema_and_element_preserve_full_relation(kind, negated):
    declarations = [dict(name="i", sort="Int", lower=-1, upper=3),
                    dict(name="y", sort="Int", lower=-2, upper=2),
                    dict(name="r", sort="Int")]
    selected = dict(cp="element", items=[literal(4), literal(-3), literal(2)],
                    index=variable("i"), default=literal(7))
    expression = operation("eq", variable("r"),
                           dict(cp=kind, items=[selected, variable("y")]))
    if negated:
        expression = operation("not", expression)
    translated = propose(model(expression, declarations))
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2()))
    i, y, r = z3.Ints("i y r")
    selected_reference = z3.If(i == 0, 4, z3.If(i == 1, -3, z3.If(i == 2, 2, 7)))
    # Characterize the extremum relationally, without reusing its ite encoding.
    side = (z3.And(r <= selected_reference, r <= y) if kind == "minimum"
            else z3.And(r >= selected_reference, r >= y))
    relation = z3.And(side, z3.Or(r == selected_reference, r == y))
    expected = z3.And(i >= -1, i <= 3, y >= -2, y <= 2,
                      z3.Not(relation) if negated else relation)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
