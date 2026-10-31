"""A trailing argument comma is used by the official IHTC model."""

import pytest

z3 = pytest.importorskip("z3")
import somtparser as sp


@pytest.mark.parametrize("declaration, call", [
    ("predicate positive(var int: x) = x > 0;", "positive(x,)"),
    ("function var int: identity(var int: x) = x;", "identity(x,) > 0"),
    ("predicate positive(array[int] of var int: a) = a[1] > 0;", "positive([x],)"),
])
@pytest.mark.parametrize("value, expected", [(-1, z3.unsat), (1, z3.sat)])
def test_trailing_comma_preserves_call_semantics(declaration, call, value, expected):
    result = sp.translate(source=f"""
{declaration}
var int: x;
constraint {call};
constraint x = {value};
solve satisfy;
""", language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == expected


@pytest.mark.parametrize("declaration, call", [
    ("predicate p(int: x) = true;", "p(1,2,)"),
    ("predicate p(int: x) = true;", "p(1,,)"),
    ("predicate p() = true;", "p(,)"),
    ("function int: f(int: x) = x;", "f(1,2,) = 1"),
])
def test_trailing_comma_does_not_hide_wrong_arity(declaration, call):
    result = sp.translate(source=f"{declaration} constraint {call}; solve satisfy;", language="minizinc")
    assert not result.ok
