"""Malformed expression-valued literals get guidance, never automatic repair."""
import copy

import pytest

from somtparser._nl_feedback import validation_feedback
from somtparser.natural_language import propose_nl_with_repair


SOURCE = "For indices zero and one, cell a[i] is equal to i."
PATH = "constraints[0].expr.args[0].literal"
POINTER = "/constraints/0/expr/args/0"


def feedback(value, *, parent_extra=None, path=PATH, diagnostic=None):
    wrapper = dict(literal=value, sort="Int")
    wrapper.update(parent_extra or {})
    model = dict(constraints=[dict(expr=dict(op="eq", args=[wrapper,
        dict(literal=0, sort="Int")]), span=[0, len(SOURCE)])])
    message = diagnostic or path + ": expected an exact integer (not Boolean or floating point)"
    return model, validation_feedback(SOURCE, model, [message])[0]


@pytest.mark.parametrize("expression", [
    {"literal": 2, "sort": "Int"},
    {"var": "i"},
    {"op": "add", "args": [{"var": "i"}, {"literal": 1, "sort": "Int"}]},
    {"at": "a", "indices": [{"var": "i"}]},
    {"apply": "f", "args": [{"var": "i"}]},
    {"cp": "abs", "value": {"var": "i"}},
])
def test_expression_object_gets_non_executable_located_guidance(expression):
    model, detail = feedback(expression)
    assert detail["message"] == "expected an exact integer (not Boolean or floating point)"
    assert detail["kind"] == "construction" and detail["json_pointer"] == POINTER + "/literal"
    hint = detail["construction_hint"]
    assert hint["code"] == "expression-in-literal"
    assert hint["expression_json_pointer"] == POINTER
    assert hint["automatic_repair"] is False and "binders" in hint["message"]
    assert detail["source_span"] == [0, len(SOURCE)]
    assert model["constraints"][0]["expr"]["args"][0] == {"literal": expression, "sort": "Int"}


@pytest.mark.parametrize("value", ["{\"var\":\"i\"}", 0.5, {"unrecognized": "i"}])
def test_other_bad_values_are_not_guessed_as_expressions(value):
    _, detail = feedback(value)
    assert "construction_hint" not in detail


def test_malformed_wrapper_fields_are_not_silently_dropped():
    _, detail = feedback({"var": "i"}, parent_extra={"unknown": True})
    assert "construction_hint" not in detail


def test_missing_or_unlocated_diagnostic_does_not_guess_a_path():
    _, missing = feedback({"var": "i"}, path="constraints[0].expr.missing.literal")
    _, native = feedback({"var": "i"}, diagnostic="native error: unrelated literal message")
    assert not missing["value_present"] and "construction_hint" not in missing
    assert "construction_hint" not in native


def test_hint_is_fresh_and_does_not_mutate_candidate_or_annotations():
    value = {"var": "i"}
    original = copy.deepcopy(value)
    model, first = feedback(value)
    first["construction_hint"]["message"] = "provider mutation"
    second = validation_feedback(SOURCE, model, [PATH + ": expected an exact integer"])[0]
    assert second["construction_hint"]["message"] != "provider mutation"
    assert value == original and model["constraints"][0]["expr"]["args"][0]["literal"] == original


def array_model(*, malformed):
    literal = lambda n: dict(literal=n, sort="Int")
    var = dict(var="i")
    index = dict(literal=var, sort="Int") if malformed else var
    op = lambda name, *args: dict(op=name, args=list(args))
    body = op("implies", op("and", op("ge", var, literal(0)), op("lt", var, literal(2))),
              op("eq", dict(at="a", indices=[index]), var))
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
        declarations=[dict(name="a", sort="Int", shape=[2])], functions=[],
        constraints=[dict(expr=dict(quantifier="forall", binders=[dict(name="i", sort="Int")], body=body),
                          span=[0, len(SOURCE)])], objectives=[], objective_order="single", goal=None,
        assumptions=[], unresolved=[])


def test_public_repair_sees_hint_then_explicit_provider_change_has_exact_relation():
    import somtparser as sp
    import z3

    bad = array_model(malformed=True)
    saved = copy.deepcopy(bad)
    calls = []
    def provider(request):
        calls.append(copy.deepcopy(request))
        if "repair" not in request:
            return bad
        detail, = request["repair"]["diagnostic_details"]
        assert detail["construction_hint"]["code"] == "expression-in-literal"
        assert detail["construction_hint"]["automatic_repair"] is False
        assert request["source"] == SOURCE
        assert not {"reference", "gold", "solver", "counterexample"} & request.keys()
        return array_model(malformed=False)

    trace = propose_nl_with_repair(SOURCE, provider=provider, max_attempts=2)
    assert len(calls) == 2 and not trace.attempts[0].valid and trace.attempts[1].valid
    assert bad == saved and trace.attempts[0].model["constraints"] == saved["constraints"]
    compiled = sp.compile_candidate(trace.attempts[1], accept_digest=trace.attempts[1].digest)
    assert compiled.ok, compiled.diagnostics
    actual = z3.And(*z3.parse_smt2_string(compiled.to_smt2()))
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    expected = z3.And(a[0] == 0, a[1] == 1)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    witness = z3.Solver()
    witness.add(actual, a[2] == 17)
    assert witness.check() == z3.sat


def test_repeated_invalid_provider_never_becomes_valid_or_creates_a_binder():
    model = array_model(malformed=True)
    saved = copy.deepcopy(model)
    trace = propose_nl_with_repair(SOURCE, provider=lambda request: model, max_attempts=2)
    assert trace.stop_reason == "attempt-limit" and all(not c.valid for c in trace.attempts)
    assert model == saved
    assert all(c.model["constraints"] == saved["constraints"] for c in trace.attempts)


@pytest.mark.parametrize("nested", [
    {"literal": 3, "sort": "Int"},
    {"cp": "abs", "value": {"literal": -3, "sort": "Int"}},
])
def test_nested_constructor_repair_preserves_the_complete_relation(nested):
    import somtparser as sp
    import z3

    source = "Integer x equals three."
    model = dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
        declarations=[dict(name="x", sort="Int")], functions=[],
        constraints=[dict(expr=dict(op="eq", args=[dict(var="x"),
            dict(literal=nested, sort="Int")]), span=[0, len(source)])],
        objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])
    saved = copy.deepcopy(model)

    def provider(request):
        if "repair" not in request:
            return model
        detail, = request["repair"]["diagnostic_details"]
        hint = detail["construction_hint"]
        assert hint["expression_json_pointer"] == "/constraints/0/expr/args/1"
        assert hint["automatic_repair"] is False
        assert request["source"] == source
        repaired = copy.deepcopy(model)
        repaired["constraints"][0]["expr"]["args"][1] = copy.deepcopy(nested)
        return repaired

    trace = propose_nl_with_repair(source, provider=provider, max_attempts=2)
    assert not trace.attempts[0].valid and trace.attempts[1].valid
    assert model == saved and trace.attempts[0].model["constraints"] == saved["constraints"]
    result = sp.compile_candidate(trace.attempts[1], accept_digest=trace.attempts[1].digest)
    assert result.ok, result.diagnostics
    loaded = z3.Optimize()
    loaded.from_string(result.to_smt2())
    assert len(loaded.objectives()) == 0
    actual = z3.And(*loaded.assertions())
    solver = z3.Solver()
    solver.add(z3.Xor(actual, z3.Int("x") == 3))
    assert solver.check() == z3.unsat
    witness = z3.Solver()
    witness.add(actual)
    assert witness.check() == z3.sat


def test_nested_literal_hint_does_not_coerce_a_mismatched_sort():
    source = "Integer x equals three."
    model = dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
        declarations=[dict(name="x", sort="Int")], functions=[],
        constraints=[dict(expr=dict(op="eq", args=[dict(var="x"),
            dict(literal=dict(literal=True, sort="Bool"), sort="Int")]),
            span=[0, len(source)])], objectives=[], objective_order="single",
        goal=None, assumptions=[], unresolved=[])

    def provider(request):
        if "repair" not in request:
            return model
        detail, = request["repair"]["diagnostic_details"]
        assert detail["construction_hint"]["automatic_repair"] is False
        repaired = copy.deepcopy(model)
        repaired["constraints"][0]["expr"]["args"][1] = dict(literal=True, sort="Bool")
        return repaired

    trace = propose_nl_with_repair(source, provider=provider, max_attempts=2)
    assert trace.stop_reason == "attempt-limit"
    assert all(not candidate.valid for candidate in trace.attempts)
    assert trace.attempts[1].diagnostics
