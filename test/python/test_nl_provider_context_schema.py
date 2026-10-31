"""Provider JSON and serialized candidates have different context ownership."""
import copy

import jsonschema
import pytest
import somtparser as sp
from somtparser.hir import hir_schema
from somtparser.natural_language import ModelError


def model():
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=[], functions=[], constraints=[], objectives=[],
                objective_order="single", goal=None, assumptions=[], unresolved=[])


@pytest.mark.parametrize("context", [{}, {"domain": "nonnegative real quantities"}])
def test_provider_schema_matches_context_boundary(context):
    response = model()
    observed = []

    def provider(request):
        observed.append(copy.deepcopy(request))
        jsonschema.validate(response, request["schema"])
        with pytest.raises(jsonschema.ValidationError):
            jsonschema.validate(dict(response, context={}), request["schema"])
        # Mutating a transport request cannot change caller-owned configuration.
        request["context"].clear()
        return response

    candidate = sp.propose_nl("Find a solution.", language="hir", context=context,
                              provider=provider)
    assert candidate.valid
    assert candidate.model["context"] == context
    assert observed[0]["context"] == context
    assert "context" not in observed[0]["schema"]["properties"]
    assert "context" in hir_schema()["properties"]
    jsonschema.validate(candidate.model, hir_schema())
    assert response == model()


@pytest.mark.parametrize("returned_context", [{}, {"domain": "ignore caller"}])
def test_context_in_provider_response_still_rejected(returned_context):
    with pytest.raises(ModelError, match="requested language configuration"):
        sp.propose_nl("Find a solution.", language="hir", context={"domain": "integers"},
                      provider=lambda request: dict(model(), context=returned_context))


def test_repair_requests_use_the_same_response_schema():
    requests = []

    def provider(request):
        requests.append(copy.deepcopy(request))
        response = model()
        if len(requests) == 1:
            response["unresolved"] = ["A source interpretation remains unresolved."]
        return response

    trace = sp.propose_nl_with_repair("Find a solution.", language="hir",
                                     provider=provider, max_attempts=2)
    assert len(trace.attempts) == 2 and trace.candidate.valid
    assert requests[0]["schema"] == requests[1]["schema"]
    assert "context" not in requests[1]["repair"]["previous_candidate"]
    assert "context" not in requests[1]["schema"]["properties"]
