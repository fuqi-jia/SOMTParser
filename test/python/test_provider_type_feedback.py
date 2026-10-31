"""Real HIR proposal/repair API contract for path-preserving type feedback."""
import copy

import pytest
import somtparser as sp

CONTEXT = {"observable": "x is the source's named integer"}
TEXTS = {
    "int-literal": "Let x be an integer from 0 to 10 and require x to equal 3.",
    "bool-ge": "Let x be an integer from 0 to 10 and require x to be at least 3.",
    "ite-condition": "Let x be an integer from 0 to 10 and require x to be positive.",
}


def model(case, repaired=False):
    text = TEXTS[case]
    if case == "int-literal":
        rhs = {"literal": 3 if repaired else True, "sort": "Int"}
        expr = {"op": "eq", "args": [{"var": "x"}, rhs]}
    elif case == "bool-ge":
        rhs = {"literal": 3, "sort": "Int"} if repaired else {
            "literal": True, "sort": "Bool"
        }
        expr = {"op": "ge", "args": [{"var": "x"}, rhs]}
    elif case == "ite-condition":
        condition = {"op": "gt", "args": [{"var": "x"}, {"literal": 0, "sort": "Int"}]}
        if not repaired:
            condition = {"var": "x"}
        expr = {
            "op": "eq",
            "args": [
                {"op": "ite", "args": [condition, {"literal": 1, "sort": "Int"},
                                          {"literal": 0, "sort": "Int"}]},
                {"literal": 1, "sort": "Int"},
            ],
        }
    else:
        raise AssertionError(case)
    return dict(
        schema="somt-hir-model-v1", language="hir", decision="satisfiability",
        declarations=[dict(name="x", sort="Int", lower=0, upper=10)], functions=[],
        constraints=[dict(expr=expr, span=[0, len(text)])], objectives=[],
        objective_order="single", goal=None, assumptions=[], unresolved=[],
    )


@pytest.mark.parametrize("case,path", [
    ("int-literal", "constraints[0].expr.args[1].literal"),
    ("ite-condition", "constraints[0].expr.args[0].args[0]"),
])
def test_real_hir_repair_receives_path_and_only_source_candidate(case, path):
    calls = []
    first = model(case)
    text = TEXTS[case]

    def provider(request):
        calls.append(copy.deepcopy(request))
        # The proposal API request is grounded in source/schema/context and the
        # prior candidate. No reference formula, reference model, or solver
        # witness is supplied to the provider.
        assert {"source", "source_sha256", "schema", "language", "context", "instruction"} <= set(request)
        assert not ({"reference", "reference_model", "gold", "solver", "counterexample"} & set(request))
        if "repair" not in request:
            return copy.deepcopy(first)
        feedback = request["repair"]
        assert len(feedback["diagnostics"]) == 1
        assert feedback["diagnostics"][0].startswith(path + ": ")
        assert feedback["previous_candidate"] == model(case)
        # For HIR the candidate envelope's context is API-attached. The repair
        # object must omit it from previous_candidate and carry context separately.
        replacement = model(case, repaired=True)
        return replacement

    trace = sp.propose_nl_with_repair(
        text, provider=provider, max_attempts=2, language="hir", context=CONTEXT,
    )
    assert len(trace.attempts) == len(calls) == 2
    invalid, repaired = trace.attempts
    assert not invalid.valid and repaired.valid, (invalid.diagnostics, repaired.diagnostics)
    assert invalid.diagnostics[0].startswith(path + ": ")
    assert calls[1]["repair"]["diagnostics"] == list(invalid.diagnostics)
    assert calls[0]["source"] == calls[1]["source"] == text
    assert calls[0]["context"] == calls[1]["context"] == CONTEXT
    assert "reference" not in calls[0] and "reference" not in calls[1]
    assert "solver" not in calls[0] and "solver" not in calls[1]
    assert invalid.model == model(case) | {"context": CONTEXT}
