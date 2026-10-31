"""Candidate errors identify the original JSON operand without repairing it."""
import copy

import pytest
from somtparser.hir import HirBuilder, ModelError, build_hir
from somtparser.natural_language import _candidate


def literal(value, sort="Int"):
    return {"literal": value, "sort": sort}


def model(expression):
    return dict(schema="somt-hir-model-v1", language="hir",
                decision="satisfiability", declarations=[], functions=[],
                constraints=[dict(expr=literal(True, "Bool"), span=[0, 1]),
                             dict(expr=expression, span=[0, 1])],
                objectives=[], objective_order="single", goal=None,
                assumptions=[], unresolved=[])


@pytest.mark.parametrize("expression,path,detail", [
    ({"op": "eq", "args": [literal(6), 6]},
     ".args[1]", "expression must be an object"),
    ({"fold": "forall", "var": "i", "range": [0, 19], "body":
      {"op": "ge", "args": [{"var": "i"}, 5]}},
     ".body.args[1]", "expression must be an object"),
    ({"op": "eq", "args": [literal({"var": "x1"}), literal(3)]},
     ".args[0].literal", "expected an exact integer"),
    ({"op": "ge", "args": [literal(True, "Bool"), literal(True, "Bool")]},
     ".args[0]", "numeric operands required"),
    ({"op": "ge", "args": [literal(1), literal(True, "Bool")]},
     ".args[1]", "numeric operands required"),
    ({"var": "invalid name"}, ".var", "expected an identifier"),
    ({"op": "ite", "args": [literal(1), literal(True, "Bool"), literal(False, "Bool")]},
     ".args[0]", "ite condition must have sort Bool"),
    ({"op_indexed": {"op": "extract", "indices": [3, 0], "args": [2]}},
     ".op_indexed.args[0]", "expression must be an object"),
    ({"at": "a", "indices": [4]}, ".indices[0]", "expression must be an object"),
])
def test_nested_candidate_errors_keep_exact_source_path(expression, path, detail):
    candidate = model(expression)
    if "at" in expression:
        candidate["declarations"] = [{"name": "a", "sort": {"Array": ["Int", "Int"]}}]
    before = copy.deepcopy(candidate)
    with pytest.raises(ModelError) as error:
        build_hir(candidate, "x")
    assert error.value.path == "constraints[1].expr" + path
    assert detail in str(error.value)
    assert candidate == before
    rejected = _candidate("x", candidate, "saved-provider-output")
    assert rejected.diagnostics and rejected.diagnostics[0].startswith(error.value.path + ": ")


@pytest.mark.parametrize("field", ["goal", "objectives"])
def test_errors_in_goal_and_objective_have_their_own_locations(field):
    candidate = model(literal(True, "Bool"))
    statement = {"expr": {"op": "add", "args": [literal(0), 2]}, "span": [0, 1]}
    if field == "goal":
        candidate.update(decision="validity", goal=statement)
        expected = "goal.expr.args[1]"
    else:
        candidate.update(decision="optimization", objectives=[dict(statement, sense="minimize")])
        expected = "objectives[0].expr.args[1]"
    with pytest.raises(ModelError) as error:
        build_hir(candidate, "x")
    assert error.value.path == expected


def test_standalone_builder_diagnostics_and_success_after_failure():
    builder = HirBuilder()
    with pytest.raises(ModelError) as error:
        builder.expr({"op": "eq", "args": [literal(2), 2]})
    assert error.value.path == "model.args[1]"
    builder.constrain({"op": "eq", "args": [literal(2), literal(2)]})
    assert builder.translate().ok
