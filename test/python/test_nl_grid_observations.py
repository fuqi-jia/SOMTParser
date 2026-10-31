"""Source-role prompt contract and exhaustive tiny-grid CP semantics."""
import itertools

import pytest
z3 = pytest.importorskip("z3")

from somtparser.hir_cp import build_cp_hir
from somtparser.natural_language import propose_nl


class CapturedRequest(Exception):
    pass


def test_hir_provider_prompt_distinguishes_observations_and_decisions():
    captured = {}

    def provider(request):
        captured.update(request)
        raise CapturedRequest

    with pytest.raises(CapturedRequest):
        propose_nl("A grid has opened numbered cells and unknown cells.",
                   language="hir", context={}, provider=provider)

    instruction = captured["instruction"]
    assert "observations or clues distinct from unknown decision cells" in instruction
    assert "constrain its mine indicator to false" in instruction
    assert "each in-bounds neighbor once" in instruction
    assert "exclude the center" in instruction
    assert "do not wrap at grid edges" in instruction


def _lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def _at(row, col):
    return {"at": "mine", "indices": [_lit(row), _lit(col)]}


def _grid_model(clue):
    # Corner (0,0) has exactly the other three cells as in-bounds neighbors.
    # The clue is fixed observed data; the neighboring Bool cells are decisions.
    return {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "mine", "sort": "Bool", "shape": [2, 2]}],
        "functions": [],
        "constraints": [
            {"expr": {"op": "eq", "args": [_at(0, 0), _lit(False, "Bool")]},
             "span": [0, 1]},
            {"expr": {"op": "eq", "args": [
                {"cp": "count_true", "items": [_at(0, 1), _at(1, 0), _at(1, 1)]},
                _lit(clue),
            ]}, "span": [0, 1]},
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


@pytest.mark.parametrize("clue", range(4))
def test_fixed_corner_clue_and_neighbor_count_match_every_two_by_two_grid(clue):
    translated = build_cp_hir(_grid_model(clue), "x").translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(translated.to_smt2()))
    # Native HIR represents a shaped array as nested SMT arrays.
    rows = z3.ArraySort(z3.IntSort(), z3.BoolSort())
    mine = z3.Array("mine", z3.IntSort(), rows)
    variables = [z3.Select(z3.Select(mine, r), c)
                 for r in range(2) for c in range(2)]
    solver = z3.Solver()
    for bits in itertools.product([False, True], repeat=4):
        solver.push()
        solver.add(formula)
        solver.add(*[var == value for var, value in zip(variables, bits)])
        expected = (not bits[0]) and sum(bits[1:]) == clue
        assert (solver.check() == z3.sat) is expected, (clue, bits)
        solver.pop()
