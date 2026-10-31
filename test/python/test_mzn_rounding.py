"""MiniZinc rounding: parameter folding, decision values, and partiality."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

# Independent expected table, including negative half ties and both sides.
_VALUES = ["-2.75", "-2.5", "-2.25", "-0.5", "0.0", "0.5", "2.25", "2.5", "2.75"]
_EXPECTED = {
    "floor": [-3, -3, -3, -1, 0, 0, 2, 2, 2],
    "ceil": [-2, -2, -2, 0, 0, 1, 3, 3, 3],
    "round": [-3, -3, -2, -1, 0, 1, 2, 3, 3],
}


def translate(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.parse_smt2_string(result.to_smt2())


@pytest.mark.parametrize("operation", _EXPECTED)
def test_parameter_array_rounding(operation):
    values = ", ".join(_VALUES)
    expected = ", ".join(map(str, _EXPECTED[operation]))
    assertions = translate(
        f"array[1..9] of float: a = [{values}];"
        f"array[1..9] of int: b = [{operation}(a[i]) | i in 1..9];"
        f"array[1..9] of int: expected = [{expected}];"
        "constraint forall(i in 1..9)(b[i] = expected[i]); solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.sat


@pytest.mark.parametrize("operation", _EXPECTED)
def test_decision_rounding_has_unique_expected_result(operation):
    assertions = translate(
        f"var float: x; var int: y; constraint y = {operation}(x); solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(*assertions)
    for value, expected in zip(_VALUES, _EXPECTED[operation]):
        solver.push()
        solver.add(z3.Real("x") == z3.RealVal(value))
        solver.push()
        solver.add(z3.Int("y") == expected)
        assert solver.check() == z3.sat
        solver.pop()
        solver.add(z3.Int("y") != expected)
        assert solver.check() == z3.unsat
        solver.pop()


def test_rounded_parameter_can_define_array_index_set():
    assertions = translate(
        "int: n = round(2.5); array[1..n] of var int: a;"
        "constraint a[3] = 7; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.sat


@pytest.mark.parametrize("operation", _EXPECTED)
@pytest.mark.parametrize("negated", [False, True])
def test_rounding_preserves_division_definedness(operation, negated):
    body = f"{operation}(1.0 / d) = 0"
    if negated:
        body = f"not ({body})"
    assertions = translate(
        f"var float: d; constraint d = 0.0; constraint {body}; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == (z3.sat if negated else z3.unsat)


@pytest.mark.parametrize("operation", _EXPECTED)
def test_rounding_rejects_string_argument(operation):
    result = sp.translate(source=f'constraint {operation}("abc") = 0; solve satisfy;',
                          language="minizinc")
    assert not result.ok
    assert any("numeric argument" in d.message for d in result.diagnostic_items)


def test_rounding_accepts_implicit_boolean_and_integer_coercions():
    assertions = translate(
        "int: a = round(true); int: b = floor(false); int: c = ceil(3);"
        "constraint a = 1 /\\ b = 0 /\\ c = 3; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.sat
