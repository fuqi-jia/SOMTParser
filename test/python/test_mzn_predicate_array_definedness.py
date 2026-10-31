"""Semantics of predicate calls with unused partial array actuals."""

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


def _solver(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    return solver


@pytest.mark.parametrize(
    "call, expected",
    [("p([1 div d])", z3.unsat), ("not p([1 div d])", z3.sat)],
)
def test_ignored_array_actual_is_defined_even_under_negation(call, expected):
    # The predicate body ignores its array parameter. MiniZinc still evaluates
    # the argument: with d = 0 the positive call is undefined/false, while its
    # negation is true. SMT's total integer division must not change that.
    source = f"""
predicate p(array[int] of var int: a) = true;
var int: d;
constraint {call};
constraint d = 0;
solve satisfy;
"""
    assert _solver(source).check() == expected


@pytest.mark.parametrize("index_first", [False, True])
@pytest.mark.parametrize("concatenated", [False, True])
@pytest.mark.parametrize("machine, expected", [(1, z3.unsat), (2, z3.sat), (3, z3.unsat)])
def test_integer_type_variable_unifies_elements_and_indices(index_first, concatenated, machine, expected):
    # The official IHTC cumulatives signature uses $$M for both positions.
    # Ordinary Int elements and integer array axes must unify in either order.
    formals = ["array[int] of var $$M: m", "array[$$M] of var int: b"]
    actuals = ["machines ++ [2]" if concatenated else "machines", "[5, 7]"]
    if index_first:
        formals.reverse()
        actuals.reverse()
    source = f"""
array[1..1] of var 1..3: machines;
predicate p({', '.join(formals)}) = b[m[1]] = 7;
constraint p({', '.join(actuals)});
constraint machines[1] = {machine};
solve satisfy;
"""
    assert _solver(source).check() == expected
