"""Literal schemas reject symbolic Real operands without rewriting a model."""
import copy

import pytest

from somtparser.hir import ModelError, build_hir, hir_schema
from somtparser.natural_language import propose_nl_with_repair

jsonschema = pytest.importorskip("jsonschema")

SOURCE = "Choose a real amount x equal to 3/2."


def model(value, sort="Real"):
    return dict(
        schema="somt-hir-model-v1", language="hir", decision="satisfiability",
        declarations=[], functions=[],
        constraints=[dict(expr={"op": "eq", "args": [
            {"literal": value, "sort": sort},
            {"literal": value, "sort": sort},
        ]}, span=[0, len(SOURCE)])],
        objectives=[], objective_order="single", goal=None,
        assumptions=[], unresolved=[],
    )


@pytest.fixture(scope="module")
def validator():
    schema = hir_schema()
    jsonschema.Draft202012Validator.check_schema(schema)
    return jsonschema.Draft202012Validator(schema)


@pytest.mark.parametrize("value,sort", [
    ("vanilla_scoops", "Real"), ("x", "Real"), ("x+1", "Real"),
    ("2 dollars", "Real"), ("1/0", "Real"), ("1/-2", "Real"),
    ("1e3", "Real"), ("1\n", "Real"), (" 1", "Real"),
    ("NaN", "Real"), (2, "Real"), (True, "Real"),
    (["1"], "Real"), ("1" * 513, "Real"),
    (True, "Int"), ("3", "Int"), (3.5, "Int"),
    (1, "Bool"), ("true", "Bool"),
])
def test_schema_and_builder_refuse_wrong_literal_constructors(validator, value, sort):
    candidate = model(value, sort)
    assert not validator.is_valid(candidate)
    with pytest.raises(ModelError):
        build_hir(candidate, SOURCE)


@pytest.mark.parametrize("value,sort", [
    ("0", "Real"), ("-7", "Real"), ("+3/2", "Real"),
    ("0.125", "Real"), ("1" * 512, "Real"), ("١.٢", "Real"),
    (0, "Int"), (-4, "Int"), (True, "Bool"), (False, "Bool"),
    ("x", "String"), ("3/2", "String"), ("1\n", "String"),
    ("#b01", {"BitVec": 2}),
])
def test_existing_exact_literals_still_build(validator, value, sort):
    candidate = model(value, sort)
    assert validator.is_valid(candidate)
    build_hir(candidate, SOURCE)


def test_real_bounds_and_literals_have_the_same_end_boundary(validator):
    candidate = model("1")
    candidate["declarations"] = [dict(name="x", sort="Real", lower="1\n")]
    assert not validator.is_valid(candidate)
    with pytest.raises(ModelError):
        build_hir(candidate, SOURCE)
    candidate["declarations"][0]["lower"] = "-3/2"
    assert validator.is_valid(candidate)
    build_hir(candidate, SOURCE)


def test_provider_gets_numeric_schema_and_repairs_only_by_explicit_new_proposal():
    bad = model("3/2")
    bad["declarations"] = [dict(name="x", sort="Real")]
    bad["constraints"][0]["expr"]["args"][0] = {"literal": "x", "sort": "Real"}
    original = copy.deepcopy(bad)
    good = copy.deepcopy(bad)
    good["constraints"][0]["expr"]["args"][0] = {"var": "x"}
    requests = []

    def provider(request):
        requests.append(copy.deepcopy(request))
        check = jsonschema.Draft202012Validator(request["schema"])
        assert not check.is_valid(bad)
        assert check.is_valid(good)
        assert '{"var":"name"}' in request["instruction"]
        assert not {"gold", "reference", "reference_model", "solver"} & request.keys()
        if "repair" not in request:
            return bad
        repair = request["repair"]
        detail, = repair["diagnostic_details"]
        assert detail["json_pointer"] == "/constraints/0/expr/args/0/literal"
        assert detail["value"] == "x"
        assert repair["previous_candidate"]["constraints"] == original["constraints"]
        return good

    trace = propose_nl_with_repair(SOURCE, language="hir", provider=provider,
                                  max_attempts=2)
    assert len(trace.attempts) == 2
    assert not trace.attempts[0].valid and trace.attempts[1].valid
    assert trace.attempts[0].model["constraints"] == original["constraints"]
    assert bad == original
    assert requests[0]["source"] == requests[1]["source"] == SOURCE
    assert trace.attempts[1].model["constraints"] == good["constraints"]
