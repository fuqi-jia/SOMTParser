"""Compile public modeling examples and independently check their conclusions."""
from copy import deepcopy
from pathlib import Path
import sys

import pytest
import z3
import somtparser as sp
from somtparser.hir import hir_api

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from nl_hir_batch import build_request_package


def compile_pattern(name):
    pattern = hir_api()["modeling_patterns"][name]
    requests = []

    def provider(request):
        requests.append(request)
        return deepcopy(pattern["model"])

    candidate = sp.propose_nl(pattern["source"], language="hir", provider=provider)
    assert candidate.valid, candidate.diagnostics
    compiled = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert compiled.ok, compiled.diagnostics
    return pattern, z3.And(*z3.parse_smt2_string(compiled.to_smt2())), requests[0]


def check(formula, *conditions):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(formula, *conditions)
    return solver.check()


@pytest.mark.parametrize("name,positive,negative", [
    ("shared_numeric_attribute", z3.unsat, z3.sat),
    ("universal_without_existence", z3.sat, z3.sat),
    ("explicit_category_membership", z3.sat, z3.unsat),
])
def test_complete_examples_have_the_independent_expected_conclusions(name, positive, negative):
    pattern, formula, _ = compile_pattern(name)
    # Consistency must be established before interpreting a conclusion polarity.
    assert check(formula) == z3.sat
    goal = z3.Bool("somt_goal")
    assert check(formula, goal) == positive
    assert check(formula, z3.Not(goal)) == negative
    assert [pattern["source"][c["span"][0]:c["span"][1]]
            for c in pattern["model"]["constraints"]] == pattern["source"].splitlines()
    assert pattern["model"]["assumptions"] == []
    assert pattern["model"]["unresolved"] == []


def test_numeric_example_preserves_the_complete_real_relation():
    _, actual, _ = compile_pattern("shared_numeric_attribute")
    entity = z3.DeclareSort("Entity")
    rho = z3.Const("rho", entity)
    temperature = z3.Function("temperature", entity, z3.RealSort())
    goal = z3.Bool("somt_goal")
    expected = z3.And(temperature(rho) < 5, goal == (temperature(rho) > 5))
    assert check(z3.Xor(actual, expected)) == z3.unsat
    # Real-valued measurements retain nonintegral witnesses and have no
    # source-unstated lower bound. The strict upper boundary stays excluded.
    assert check(actual, temperature(rho) == z3.RealVal("9/2")) == z3.sat
    assert check(actual, temperature(rho) == -100) == z3.sat
    assert check(actual, temperature(rho) == 5) == z3.unsat


def test_single_and_batch_provider_requests_receive_the_same_modeling_guidance():
    pattern, _, single = compile_pattern("shared_numeric_attribute")
    catalog = hir_api()
    batch = build_request_package([{"id": "independent/example", "source": pattern["source"]}])["requests"][0]
    guidance = catalog["semantics"]["source_modeling"]
    assert guidance in single["instruction"]
    assert guidance in batch["instruction"]
    assert single["schema"]["constructor_api"]["modeling_patterns"] == catalog["modeling_patterns"]
    assert batch["operator_catalog"]["modeling_patterns"] == catalog["modeling_patterns"]


def test_catalog_examples_are_fresh_and_do_not_modify_later_requests():
    original = hir_api()["modeling_patterns"]
    changed = hir_api()["modeling_patterns"]
    changed["shared_numeric_attribute"]["model"]["functions"][0]["result"] = "Bool"
    assert hir_api()["modeling_patterns"] == original


@pytest.mark.parametrize("name", [
    "percentage_of_combined_total", "exact_fraction_of_quantity",
])
def test_numeric_modeling_patterns_preserve_independent_complete_relations(name):
    pattern, actual, _ = compile_pattern(name)
    if name == "percentage_of_combined_total":
        resin, filler = z3.Reals("resin filler")
        expected = z3.And(resin >= 0, filler >= 0, 63*resin >= 37*filler)
    else:
        load, reserve = z3.Reals("load reserve")
        expected = z3.And(load >= 0, 7*reserve == load)
    assert check(z3.Xor(actual, expected)) == z3.unsat
    assert [pattern["source"][c["span"][0]:c["span"][1]]
            for c in pattern["model"]["constraints"]] == pattern["source"].splitlines()
    assert pattern["model"]["assumptions"] == []
    assert pattern["model"]["unresolved"] == []
    assert "somt_goal" not in {d["name"] for d in pattern["model"]["declarations"]}


def test_exact_fraction_example_admits_exact_boundary_and_excludes_rounding():
    _, formula, _ = compile_pattern("exact_fraction_of_quantity")
    load, reserve = z3.Reals("load reserve")
    assert check(formula, load == 1, reserve == z3.RealVal("1/7")) == z3.sat
    assert check(formula, load == 1, reserve == z3.RealVal("0.14285714285714285")) == z3.unsat
    assert check(formula, load == 0, reserve == 0) == z3.sat


@pytest.mark.parametrize("resin_value,filler_value,expected", [
    ("37/100", "63/100", z3.sat),
    ("36/100", "64/100", z3.unsat),
    ("1", "0", z3.sat),
    ("0", "0", z3.sat),
    ("-1", "-2", z3.unsat),
])
def test_percentage_example_uses_total_mass_without_inventing_a_positive_total(
        resin_value, filler_value, expected):
    _, formula, _ = compile_pattern("percentage_of_combined_total")
    resin, filler = z3.Reals("resin filler")
    assert check(formula, resin == z3.RealVal(resin_value),
                 filler == z3.RealVal(filler_value)) == expected


@pytest.mark.parametrize("name,replacement", [
    ("percentage_of_combined_total", "63/100"),
    ("exact_fraction_of_quantity", "0.14285714285714285"),
])
def test_typed_but_wrong_numeric_proposals_are_not_silently_corrected(name, replacement):
    pattern, expected, _ = compile_pattern(name)
    model = deepcopy(pattern["model"])
    model["constraints"][1]["expr"]["args"][1]["args"][0]["literal"] = replacement
    candidate = sp.propose_nl(pattern["source"], language="hir", provider=lambda _request: model)
    assert candidate.valid, candidate.diagnostics
    compiled = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert compiled.ok, compiled.diagnostics
    actual = z3.And(*z3.parse_smt2_string(compiled.to_smt2()))
    # Typed construction cannot certify intent: these mutations change the
    # relation and must remain observable to a semantic checker.
    assert check(z3.Xor(actual, expected)) == z3.sat
