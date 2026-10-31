"""API regression for explicit objective-order validation and empty objectives."""
import pytest
import z3
from somtparser import hir


def model(source, objective_order="single"):
    return {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "x", "sort": "Int", "lower": 0}],
        "functions": [],
        "constraints": [{
            "expr": {"op": "ge", "args": [
                {"var": "x"}, {"literal": 2, "sort": "Int"}
            ]},
            "span": [0, len(source)],
        }],
        "objectives": [],
        "objective_order": objective_order,
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


def test_satisfiability_model_with_no_objectives_translates():
    source = "Choose an integer x that is at least 2."
    candidate = model(source)
    builder = hir.build_hir(candidate, source)
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
    assert solver.model()[z3.Int("x")].as_long() >= 2


@pytest.mark.parametrize("bad_value", [[], {}, None, 1, True, "pareto"])
def test_invalid_objective_order_has_model_error_path(bad_value):
    source = "A zero-objective satisfiability task."
    with pytest.raises(hir.ModelError) as exc:
        hir.build_hir(model(source, bad_value), source)
    assert exc.value.path == "objective_order"
    assert "expected 'single' or 'lexicographic'" in str(exc.value)
