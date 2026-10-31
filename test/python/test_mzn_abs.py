"""Absolute values preserve exact arithmetic and MiniZinc partiality."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def translate(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))


@pytest.mark.parametrize("kind", ["int", "float"])
def test_absolute_value_is_exact_for_all_numeric_inputs(kind):
    actual = translate(
        f"var {kind}: x; var {kind}: y; var bool: b;"
        "constraint b = (y = abs(x)); solve satisfy;"
    )
    x, y = z3.Ints("x y") if kind == "int" else z3.Reals("x y")
    expected = z3.Bool("b") == (y == z3.If(x >= 0, x, -x))
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_absolute_value_coerces_boolean_inputs():
    actual = translate("var bool: b; var int: y; constraint y = abs(b); solve satisfy;")
    expected = z3.Int("y") == z3.If(z3.Bool("b"), 1, 0)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("source", [
    "int: n = abs(-3); array[1..n] of var int: a; constraint a[3] = 7;",
    "array[1..3] of int: a = [abs(i) | i in -1..1];"
    "constraint a[1] = 1 /\\ a[2] = 0 /\\ a[3] = 1;",
    "float: r = abs(-0.125); constraint r = 1.0 / 8.0;",
    "int: n = floor(abs(-3.75)); array[1..n] of var int: a; constraint a[3] = 7;",
    "int: n = abs(true) + abs(false); constraint n = 1;",
    "enum E = {first, second}; int: n = abs(second); constraint n = 2;",
    "array[1..1] of int: a = [i | i in -1..1 where abs(i) = 0]; constraint a[1] = 0;",
])
def test_absolute_value_in_fixed_contexts(source):
    solver = z3.Solver()
    solver.add(translate(source + " solve satisfy;"))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("kind,operand", [("int", "1 div d"), ("float", "1.0 / d")])
@pytest.mark.parametrize("negated", [False, True])
def test_absolute_value_keeps_division_definedness(kind, operand, negated):
    body = f"abs({operand}) = 0"
    if negated:
        body = f"not ({body})"
    actual = translate(f"var {kind}: d; constraint d = 0; constraint {body}; solve satisfy;")
    solver = z3.Solver()
    solver.add(actual)
    assert solver.check() == (z3.sat if negated else z3.unsat)


@pytest.mark.parametrize("negated", [False, True])
def test_absolute_value_keeps_dynamic_index_definedness(negated):
    body = "abs(a[i]) = 2"
    if negated:
        body = f"not ({body})"
    actual = translate(
        "array[1..2] of int: a = [-2, 2]; var int: i; constraint i = 0;"
        f"constraint {body}; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(actual)
    assert solver.check() == (z3.sat if negated else z3.unsat)


@pytest.mark.parametrize("source,diagnostic", [
    ('constraint abs("abc") = 0;', "numeric argument"),
    ("constraint abs({1, 2}) = 0;", "numeric argument"),
    ("int: n = abs(-9223372036854775807 - 1);", "overflows"),
    ("int: n = abs(1 div 0);", "division by zero"),
])
def test_invalid_absolute_value_is_diagnosed(source, diagnostic):
    result = sp.translate(source=source + " solve satisfy;", language="minizinc")
    assert not result.ok
    assert any(diagnostic in d.message for d in result.diagnostic_items)
