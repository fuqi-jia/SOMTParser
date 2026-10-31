"""Projection keeps complete observable relations while sharing scalar maps."""
import pytest
import z3

from tools.semantic_checks import projection
from tools.semantic_checks.checker_adapter import candidate_projection


def assert_relation(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_duplicate_scalar_and_composite_observations_keep_cost():
    x = z3.Int("source_x")
    first, duplicate, successor = z3.Ints("first duplicate successor")
    cost = z3.Real("cost")
    result = candidate_projection(
        [x >= 2, x <= 4],
        [(first, x), (duplicate, x), (successor, x + 1)],
        (cost, -3 * x))
    assert_relation(result.formula,
        z3.And(first >= 2, first <= 4, duplicate == first,
               successor == first + 1, cost == -3 * first))
    assert result.optimization.scalar_terms == ("source_x",)


def test_scalar_substitution_reaches_symbolic_array_observation():
    x = z3.Int("index")
    values = z3.Array("values", z3.IntSort(), z3.IntSort())
    index, first, selected = z3.Ints("out_index out_first out_selected")
    result = candidate_projection(
        [x >= 0, x <= 1], [(index, x), (first, values[0]), (selected, values[x])])
    # For index 0 both observed cells coincide; for index 1 either cell is
    # unconstrained. Keeping the residual symbolic read is essential.
    assert_relation(result.formula,
        z3.And(index >= 0, index <= 1, z3.Implies(index == 0, selected == first)))


@pytest.mark.parametrize("size", [1, 128])
def test_scalar_projection_marshalling_scales_with_observation_count(monkeypatch, size):
    source = [z3.Int(f"source_{i}") for i in range(size)]
    aliases = [z3.Int(f"visible_{i}") for i in range(size)]
    body = z3.And(*[x == i for i, x in enumerate(source)],
                  *[alias == x for alias, x in zip(aliases, source)])
    real_substitute = projection._substitute
    marshalled_pairs = 0

    def measured_substitute(expression, substitutions):
        nonlocal marshalled_pairs
        marshalled_pairs += len(substitutions)
        return real_substitute(expression, substitutions)

    monkeypatch.setattr(projection, "_substitute", measured_substitute)
    result = projection.optimize_observation_projection(body, zip(aliases, source))
    assert_relation(result.body, z3.And(*[alias == i for i, alias in enumerate(aliases)]))
    # Count boundary work instead of using a noisy timing threshold. Larger
    # scalar-only interfaces must not marshal a full table once per leaf.
    assert marshalled_pairs <= 4 * size
