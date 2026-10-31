"""Fixed ranges acquire ordered, one-based array values in array contexts."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


CASES = [
    ("reverse(1..3)", "[3,2,1]"),
    ("reverse(-2..0)", "[0,-1,-2]"),
    ("reverse((1+1)..4)", "[4,3,2]"),
    ("reverse(((1..3)))", "[3,2,1]"),
    ("reverse(3..1)", "[]"),
    ("array1d(1..3)", "[1,2,3]"),
    ("sort(-1..1)", "[-1,0,1]"),
    ("reverse([7,8] ++ (1..2))", "[2,1,8,7]"),
    ("reverse(([7,8]) ++ (1..2))", "[2,1,8,7]"),
    ("reverse(1..card({2,4,6}))", "[3,2,1]"),
]


@pytest.mark.parametrize("expression,expected", CASES)
def test_range_values_and_order(expression, expected):
    result = sp.translate(source=(f"array[int] of int: a = {expression};"
        f"constraint a = {expected}; solve satisfy;"), language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat


def test_range_initializer_has_exact_one_based_layout_for_all_assignments():
    result = sp.translate(source="array[1..3] of var int: a = reverse(-2..0); solve satisfy;",
                          language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    array = z3.Array("a", z3.IntSort(), z3.IntSort())
    expected = z3.And(array[1] == 0, array[2] == -1, array[3] == -2)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_stripboard_enum_reindexing_of_reversed_range():
    source = ("enum LINKS = {a,b,c};"
              "constraint let { array[LINKS] of int: unused_x = "
              "array1d(LINKS,reverse(1..card(LINKS))); } in "
              "unused_x[a] = 3 /\\ unused_x[b] = 2 /\\ unused_x[c] = 1; solve satisfy;")
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat


def test_enum_range_retains_nominal_element_type():
    source = ("enum E = {a,b,c}; array[1..3] of E: xs = reverse(a..c);"
              "constraint xs[1] = c /\\ xs[2] = b /\\ xs[3] = a; solve satisfy;")
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("source", [
    "array[2..4] of var int: a = reverse(1..3); solve satisfy;",
    "var int: n; array[int] of int: a = reverse(1..n); solve satisfy;",
    "array[int] of int: a = reverse(1..(1 div 0)); solve satisfy;",
])
def test_range_coercion_does_not_invent_indices_or_values(source):
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
