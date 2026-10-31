"""Hexadecimal number scanning must leave both dots of an interval intact."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _relation(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))


@pytest.mark.parametrize("interval,lower,upper", [
    ("0x1..0x3", 1, 3), ("0X1..0X3", 1, 3),
    ("-0x3..-0x1", -3, -1), ("-0x3..0x3", -3, 3),
    ("-0x8000000000000000..-0x7fffffffffffffff", -(2**63), -(2**63) + 1),
    ("0x7fffffffffffffff..0x7fffffffffffffff", 2**63 - 1, 2**63 - 1),
])
def test_hexadecimal_integer_interval_has_exact_bounds(interval, lower, upper):
    actual = _relation(f"var {interval}:x; solve satisfy;")
    x = z3.Int("x")
    solver = z3.Solver()
    solver.add(z3.Xor(actual, z3.And(x >= lower, x <= upper)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("literal,value", [
    ("0x1.8p1", "3"), ("-0x1.p-1", "-1/2"),
    ("0X1.AP+1", "13/4"), ("0x.8p1", "1"), ("0x1p-2", "1/4"),
])
def test_hexadecimal_float_retains_its_fraction_and_binary_exponent(literal, value):
    actual = _relation(f"var float:x; constraint x={literal}; solve satisfy;")
    solver = z3.Solver()
    solver.add(z3.Xor(actual, z3.Real("x") == z3.RealVal(value)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("literal", ["0x1.", "0x1.8", "0x1.p", "0x1.p+", "0x.p1"])
def test_bad_hexadecimal_float_is_not_reinterpreted_as_integer(literal):
    result = sp.translate(source=f"float:k={literal}; solve satisfy;", language="minizinc")
    assert not result.ok
    assert result.diagnostic_items


@pytest.mark.parametrize("interval", ["0x1..", "0x1...0x2", "0x1..0x2.p"])
def test_bad_interval_boundary_remains_an_error(interval):
    result = sp.translate(source=f"var {interval}:x; solve satisfy;", language="minizinc")
    assert not result.ok
    assert result.diagnostic_items
