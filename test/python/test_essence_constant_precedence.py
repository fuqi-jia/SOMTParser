"""Parameter arithmetic must preserve expression precedence in elaboration."""
import pytest
import z3
import somtparser as sp


def translate(declarations, constraint):
    result = sp.translate(source="language ESSENCE' 1.0\n" + declarations +
                          "\nsuch that " + constraint, language="essence")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    return result


@pytest.mark.parametrize("expression,expected", [
    ("2 + 3 * 4", 14), ("20 - 2 * 3", 14),
    ("2 * 3 + 4 * 5", 26), ("(2 + 3) * 4", 20),
    ("20 - 3 - 2", 15), ("2 + -3 * 4", -10),
])
def test_letting_arithmetic_matches_decision_expression(expression, expected):
    result = translate("letting n be " + expression + "\nfind x : int(-100..100)",
                       "x = n")
    solver = z3.Solver()
    solver.from_string(result.to_smt2())
    assert solver.check() == z3.sat
    solver.add(z3.Int("x") != expected)
    assert solver.check() == z3.unsat


def test_precedence_controls_exact_variable_domain():
    result = translate("find x : int(0..2 + 3 * 4)", "true")
    solver = z3.Solver()
    solver.from_string(result.to_smt2())
    solver.add(z3.Int("x") == 14)
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.from_string(result.to_smt2())
    solver.add(z3.Int("x") == 15)
    assert solver.check() == z3.unsat


def test_precedence_controls_comprehension_generator():
    result = translate("find x : int(0..1000)",
                       "x = sum([i | i : int(1..2 + 3 * 4)])")
    solver = z3.Solver()
    solver.from_string(result.to_smt2())
    assert solver.check() == z3.sat
    solver.add(z3.Int("x") != 105)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("expression", [
    "9223372036854775807 + 1 * 2",
    "2 + 9223372036854775807 * 2",
    "-9223372036854775807 - 2 * 1",
])
def test_constant_overflow_remains_an_explicit_error(expression):
    result = sp.translate(source="language ESSENCE' 1.0\nletting n be " + expression +
                          "\nfind x : int(0..1)\nsuch that true", language="essence")
    assert not result.ok
    assert any("overflows" in d.message for d in result.diagnostic_items)
