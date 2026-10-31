"""Public unit examples checked against independent relations in original units."""
from copy import deepcopy
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import json
import os

import pytest
import z3
import somtparser as sp
from somtparser.hir import hir_api

MONEY = "linear_money_unit_conversion"
CAVITY = "product_and_area_unit_conversion"
EVIDENCE = Path(os.environ["UNIT_SCALING_EVIDENCE"]) if "UNIT_SCALING_EVIDENCE" in os.environ else None
_QUERY = 0


def record(name, value, *, text=False):
    if EVIDENCE is not None:
        EVIDENCE.mkdir(exist_ok=True)
        (EVIDENCE / name).write_text(value if text else json.dumps(value, indent=2) + "\n")


def public_target(name, *, change=None, suffix="original"):
    pattern = hir_api()["modeling_patterns"][name]
    model = deepcopy(pattern["model"])
    if change is not None:
        change(model)
    requests = []

    def provider(request):
        requests.append(request)
        return deepcopy(model)

    candidate = sp.propose_nl(pattern["source"], language="hir", provider=provider,
                               required_outputs=pattern["required_outputs"])
    assert candidate.valid, candidate.diagnostics
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest, dialect=sp.OmtDialect.Z3)
    assert result.ok, result.diagnostics
    text = result.to_smt2()
    target = z3.Optimize()
    target.from_string(text)
    record(name + "-" + suffix + ".candidate.json", candidate.to_json(), text=True)
    record(name + "-" + suffix + ".request.json", requests[0])
    record(name + "-" + suffix + ".smt2", text, text=True)
    return pattern, z3.And(*target.assertions()), list(target.objectives()), requests[0]


def prove(expected, *formulas):
    global _QUERY
    _QUERY += 1
    solver = z3.Solver()
    solver.set(timeout=0)
    solver.add(*formulas)
    answer = solver.check()
    record(f"proof-{_QUERY:04d}.smt2", solver.to_smt2(), text=True)
    record(f"proof-{_QUERY:04d}.json", dict(expected=str(expected), actual=str(answer),
           solver_timeout_ms=0, witness=str(solver.model()) if answer == z3.sat else None))
    assert answer == expected


def edges():
    values = z3.Array("edges_mm", z3.IntSort(), z3.RealSort())
    return [values[i] for i in range(3)]


def cavity_source_relation():
    # Independent dimensional definition in metres, without copying the HIR's
    # scaled volume constant or pairwise area coefficient.
    u, v, w = [edge / z3.RealVal(1000) for edge in edges()]
    area = 2 * (u * v + u * w + v * w)
    return z3.And(u > 0, v > 0, w > 0, u * v * w == z3.RealVal("7/250"),
                  z3.Real("surface_area_m2") == area), area


def cavity_point(values=(Fraction(10, 3), Fraction(1500), Fraction(5600))):
    return [edge == z3.RealVal(str(value)) for edge, value in zip(edges(), values)]


def test_linear_conversion_preserves_complete_original_dollar_relation():
    _, actual, costs, _ = public_target(MONEY)
    assert costs == []
    invoice, rebate, cents = z3.Reals("invoice_dollars rebate_dollars net_cents")
    expected = invoice - rebate == cents / z3.RealVal(100)
    prove(z3.unsat, z3.Xor(actual, expected))


def test_product_conversion_preserves_complete_metre_relation_and_exact_area_cost():
    _, actual, costs, _ = public_target(CAVITY)
    assert len(costs) == 1
    expected, area = cavity_source_relation()
    prove(z3.unsat, z3.Xor(actual, expected))
    prove(z3.unsat, actual, costs[0] != area)
    prove(z3.sat, actual, *cavity_point())


@pytest.mark.parametrize("invoice,rebate", [
    ("1/300", "0"), ("0", "1/300"), ("-7/3", "5/7"),
    ("0", "0"), ("1000000", "-1000000"), ("-1000000", "1000000"),
])
def test_linear_conversion_keeps_fractional_cents_both_signs_and_no_extra_bounds(invoice, rebate):
    _, actual, _, _ = public_target(MONEY)
    first, second, cents = z3.Reals("invoice_dollars rebate_dollars net_cents")
    expected = 100 * (Fraction(invoice) - Fraction(rebate))
    assignment = [first == z3.RealVal(invoice), second == z3.RealVal(rebate)]
    prove(z3.sat, actual, *assignment, cents == z3.RealVal(str(expected)))
    prove(z3.unsat, actual, *assignment, cents != z3.RealVal(str(expected)))


@pytest.mark.parametrize("scale", ["1", "1/100"])
def test_typed_but_wrong_linear_scales_are_distinguished_not_silently_repaired(scale):
    _, correct, _, _ = public_target(MONEY)

    def change(model):
        model["constraints"][1]["expr"]["args"][1]["args"][0]["literal"] = scale

    _, wrong, _, _ = public_target(MONEY, change=change, suffix="scale-" + scale.replace("/", "_"))
    prove(z3.sat, z3.Xor(correct, wrong))
    invoice, rebate, cents = z3.Reals("invoice_dollars rebate_dollars net_cents")
    point = [invoice == z3.RealVal("1/300"), rebate == 0, cents == z3.RealVal("1/3")]
    prove(z3.sat, correct, *point)
    prove(z3.unsat, wrong, *point)


@pytest.mark.parametrize("wrong_volume", ["28", "28000"])
def test_three_factor_volume_rejects_linear_or_square_scale_mutants(wrong_volume):
    _, correct, _, _ = public_target(CAVITY)

    def change(model):
        model["constraints"][1]["expr"]["args"][1]["literal"] = wrong_volume

    _, wrong, _, _ = public_target(CAVITY, change=change, suffix="volume-" + wrong_volume)
    prove(z3.sat, correct, z3.Not(wrong), *cavity_point())
    prove(z3.unsat, wrong, *cavity_point())


def test_area_definition_uses_square_scale_not_linear_scale():
    _, correct, _, _ = public_target(CAVITY)

    def change(model):
        model["constraints"][3]["expr"]["args"][1]["args"][0]["literal"] = "1/500"

    _, wrong, _, _ = public_target(CAVITY, change=change, suffix="wrong-area-scale")
    prove(z3.sat, correct, z3.Not(wrong), *cavity_point())


def test_equally_ordered_but_wrong_objective_unit_still_changes_pointwise_cost():
    _, correct, correct_cost, _ = public_target(CAVITY)

    def change(model):
        model["objectives"][0]["expr"] = {
            "op": "mul", "args": [{"literal": "1000000", "sort": "Real"},
                                   {"var": "surface_area_m2"}]}

    _, wrong, wrong_cost, _ = public_target(CAVITY, change=change, suffix="square-mm-objective")
    prove(z3.unsat, z3.Xor(correct, wrong))
    prove(z3.sat, correct, correct_cost[0] != wrong_cost[0], *cavity_point())


@pytest.mark.parametrize("name", [MONEY, CAVITY])
def test_whole_minor_unit_domain_is_an_invalid_additional_restriction(name):
    _, actual, _, _ = public_target(name)
    if name == MONEY:
        invoice, rebate, cents = z3.Reals("invoice_dollars rebate_dollars net_cents")
        wrongly_discrete = z3.And(actual, z3.IsInt(cents))
        point = [invoice == z3.RealVal("1/300"), rebate == 0]
    else:
        wrongly_discrete = z3.And(actual, *[z3.IsInt(edge) for edge in edges()])
        point = cavity_point()
    prove(z3.sat, actual, z3.Not(wrongly_discrete), *point)
    prove(z3.unsat, wrongly_discrete, *point)


def test_every_edge_permutation_and_fractional_millimetre_witness_is_retained():
    _, actual, _, _ = public_target(CAVITY)
    for point in permutations((Fraction(10, 3), Fraction(1500), Fraction(5600))):
        prove(z3.sat, actual, *cavity_point(point))


@pytest.mark.parametrize("restriction", ["sorted", "invented-upper-bound"])
def test_unstated_ordering_or_upper_bounds_change_the_complete_relation(restriction):
    _, actual, _, _ = public_target(CAVITY)
    values = edges()
    extra = z3.And(values[0] <= values[1], values[1] <= values[2]) if restriction == "sorted" else z3.And(*[v <= 1000 for v in values])
    point = (Fraction(5600), Fraction(1500), Fraction(10, 3))
    prove(z3.sat, actual, z3.Not(extra), *cavity_point(point))


@pytest.mark.parametrize("name", [MONEY, CAVITY])
def test_public_requests_include_units_guidance_exact_output_contracts_and_complete_spans(name):
    pattern, _, _, request = public_target(name)
    assert request["required_outputs"] == pattern["required_outputs"]
    guidance = hir_api()["semantics"]["source_modeling"]
    assert guidance in request["instruction"]
    fragments = pattern["model"]["constraints"] + pattern["model"]["objectives"]
    assert [pattern["source"][row["span"][0]:row["span"][1]] for row in fragments] == pattern["source"].splitlines()
    assert pattern["model"]["assumptions"] == pattern["model"]["unresolved"] == []


def test_output_contract_refuses_an_integer_substitution_for_real_cents():
    pattern = hir_api()["modeling_patterns"][MONEY]
    model = deepcopy(pattern["model"])
    model["declarations"][-1]["sort"] = "Int"
    candidate = sp.propose_nl(pattern["source"], language="hir", required_outputs=pattern["required_outputs"],
                              provider=lambda _: model)
    assert not candidate.valid
    record("integer-output-refusal.json", dict(valid=candidate.valid, diagnostics=candidate.diagnostics))


def test_output_contract_and_patterns_are_fresh_across_catalog_requests():
    first = hir_api()["modeling_patterns"]
    first[MONEY]["required_outputs"][0]["sort"] = "Int"
    first[CAVITY]["model"]["declarations"][0]["shape"][0] = 1
    fresh = hir_api()["modeling_patterns"]
    assert fresh[MONEY]["required_outputs"][0]["sort"] == "Real"
    assert fresh[CAVITY]["model"]["declarations"][0]["shape"] == [3]
