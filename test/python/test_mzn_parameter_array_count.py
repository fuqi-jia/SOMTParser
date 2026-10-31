"""Counts select parameter cells even when array shape metadata is present."""
import pytest
import z3
import somtparser as sp


@pytest.mark.parametrize("declaration,expression,value", [
    ("array[-1..1] of bool: a=array1d(-1..1,[true,false,true]);", "count(a)", 2),
    ("array[4..6] of int: a=array1d(4..6,[7,8,7]);", "count(a,7)", 2),
    ("array[-1..0,4..5] of int: a=array2d(-1..0,4..5,[7,8,7,7]);", "count(a,7)", 3),
])
def test_parameter_array_count_uses_values(declaration, expression, value):
    result = sp.translate(source=declaration + "var int: n; constraint n=" + expression
                          + "; solve satisfy;", language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=3000)
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
    solver.add(z3.Int("n") != value)
    assert solver.check() == z3.unsat


def test_parameter_array_predicate_count_uses_values():
    result = sp.translate(source='include "globals.mzn";' + "array[4..6] of int: a=array1d(4..6,[7,8,7]); var int: n; "
                          "constraint count(a,7,n); solve satisfy;", language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=3000)
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
    solver.add(z3.Int("n") != 2)
    assert solver.check() == z3.unsat
