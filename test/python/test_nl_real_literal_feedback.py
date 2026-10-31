"""Real-constant feedback preserves strict construction and source ownership."""
import copy

import pytest

from somtparser._nl_feedback import validation_feedback
from somtparser.natural_language import Candidate, propose_nl_with_repair


PATH = "constraints[0].expr.args[1].literal"
MESSAGE = "real literals must be exact decimal/rational strings"


def model(value, *, sort="Real", extra=None):
    literal = dict(literal=value, sort=sort)
    literal.update(extra or {})
    return dict(schema="somt-hir-model-v1", language="hir", decision="optimization",
        declarations=[dict(name="x", sort="Real", lower="0")], functions=[],
        constraints=[dict(expr=dict(op="ge", args=[dict(var="x"), literal]), span=[0, 1])],
        objectives=[dict(sense="minimize", expr=dict(var="x"), span=[0, 1])],
        objective_order="single", goal=None, assumptions=[], unresolved=[])


def detail(value, **kwargs):
    candidate = model(value, **kwargs)
    saved = copy.deepcopy(candidate)
    result, = validation_feedback("Real x is at least fifteen.", candidate, [PATH + ": " + MESSAGE])
    assert candidate == saved
    return result


@pytest.mark.parametrize("value", [0, 15, -7, 10**80 + 1])
def test_integer_hint_preserves_exact_value_and_real_sort(value):
    result = detail(value)
    hint = result["construction_hint"]
    assert hint["code"] == "real-integer-encoding"
    assert hint["same_value_literal"] == dict(literal=str(value), sort="Real")
    assert hint["expression_json_pointer"] == "/constraints/0/expr/args/1"
    assert hint["automatic_repair"] is False
    assert result["message"] == MESSAGE and result["value"] == value


@pytest.mark.parametrize("value", ["x", "single_load_machines", "not_declared"])
def test_identifier_hint_never_suggests_a_coefficient_or_variable_substitution(value):
    hint = detail(value)["construction_hint"]
    assert hint["code"] == "identifier-in-real-literal"
    assert hint["automatic_repair"] is False
    assert "same_value_literal" not in hint
    assert set(hint) == {"code", "message", "expression_json_pointer", "automatic_repair"}


@pytest.mark.parametrize("value", [True, 1.5, "3/0", "3.5", "1/7", "x + 1", [], None])
def test_no_hint_guesses_a_float_rational_expression_or_other_value(value):
    assert "construction_hint" not in detail(value)


@pytest.mark.parametrize("kwargs", [dict(sort="Int"), dict(extra={"unknown": 1})])
def test_hint_requires_the_exact_real_wrapper(kwargs):
    assert "construction_hint" not in detail(15, **kwargs)


def test_hint_requires_the_real_literal_diagnostic_and_exact_location():
    for diagnostic in [PATH + ": a different error", "native-only failure", "missing.literal: " + MESSAGE]:
        result, = validation_feedback("source", model(15), [diagnostic])
        assert "construction_hint" not in result


def test_hint_does_not_make_a_refused_candidate_valid_or_change_its_digest():
    bad = model("x")
    trace = propose_nl_with_repair("Real x is at least fifteen; minimize x.",
                                  provider=lambda request: bad, max_attempts=2)
    assert trace.stop_reason == "attempt-limit" and all(not item.valid for item in trace.attempts)
    first = trace.attempts[0]
    encoded, digest = first.to_json(), first.digest
    first.diagnostic_details[0]["construction_hint"]["message"] = "provider mutation"
    restored = Candidate.from_json(encoded)
    assert restored.to_json() == encoded and restored.digest == digest
    assert restored.model["constraints"] == bad["constraints"]


@pytest.mark.parametrize("bad_value", [15, "x"])
def test_explicit_source_only_repair_has_complete_relation_and_signed_cost(bad_value):
    import somtparser as sp
    import z3

    source = "Let x be a nonnegative real quantity. Require x to be at least fifteen and minimize x."
    bad = model(bad_value)
    saved = copy.deepcopy(bad)
    requests = []

    def provider(request):
        requests.append(copy.deepcopy(request))
        assert request["source"] == source
        assert not {"reference", "reference_model", "gold", "solver", "counterexample"} & request.keys()
        if "repair" not in request:
            return bad
        hint = request["repair"]["diagnostic_details"][0]["construction_hint"]
        assert hint["automatic_repair"] is False
        if type(bad_value) is int:
            assert hint["same_value_literal"] == dict(literal="15", sort="Real")
        else:
            assert "same_value_literal" not in hint
        # The replacement constant is explicit in source, not inferred from a
        # variable name or from the hint. The API never performs this edit.
        return model("15")

    trace = propose_nl_with_repair(source, provider=provider, max_attempts=2)
    assert len(requests) == 2 and not trace.attempts[0].valid and trace.attempts[1].valid
    assert bad == saved and trace.attempts[0].model["constraints"] == saved["constraints"]
    candidate = trace.attempts[1]
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest, dialect=sp.OmtDialect.Z3)
    assert result.ok, result.diagnostics
    ctx = z3.Context()
    loaded = z3.Optimize(ctx=ctx)
    loaded.from_string(result.to_smt2())
    x = z3.Real("x", ctx)
    formula = z3.And(*loaded.assertions())
    relation = z3.Solver(ctx=ctx)
    relation.add(z3.Xor(formula, z3.And(x >= 0, x >= 15)))
    assert relation.check() == z3.unsat
    assert len(loaded.objectives()) == 1
    cost = z3.Solver(ctx=ctx)
    cost.add(formula, loaded.objectives()[0] != x)
    assert cost.check() == z3.unsat
    witness = z3.Solver(ctx=ctx)
    witness.add(formula, x == 15)
    assert witness.check() == z3.sat
    # Guard against the tempting but unsound identifier -> var coercion.
    wrong = z3.Solver(ctx=ctx)
    wrong.add(z3.Xor(formula, z3.And(x >= 0, x >= x)))
    assert wrong.check() == z3.sat


def test_genuine_source_ambiguity_remains_a_refusal():
    bad = model("15")
    bad["unresolved"] = ["The source gives two incompatible lower bounds."]
    trace = propose_nl_with_repair("Two competing bounds remain undecided.",
                                  provider=lambda request: bad, max_attempts=2)
    assert all(not item.valid for item in trace.attempts)
    assert trace.attempts[-1].model["unresolved"] == bad["unresolved"]
    assert trace.attempts[-1].diagnostic_details[0]["kind"] == "unresolved_interpretation"
