"""Numeric MiniZinc min/max overloads over values, literals, and arrays."""

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


def _solve(source, data=()):
    result = sp.translate(source=source, language="minizinc", data=list(map(str, data)))
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    return solver


def test_numeric_two_argument_and_literal_overloads_include_negative_values():
    source = (
        "constraint max(-7, -2) = -2;\n"
        "constraint min(-7, -2) = -7;\n"
        "constraint max([-9, -2, -5]) = -2;\n"
        "constraint min([-9, -2, -5]) = -9;\n"
        "constraint max(1.25, -2.5) = 1.25;\n"
        "solve satisfy;\n"
    )
    assert _solve(source).check() == z3.sat
    assert _solve(source.replace("max(-7, -2) = -2", "max(-7, -2) = -7")).check() == z3.unsat


def test_whole_decision_array_minmax_preserves_non1based_and_multidimensional_cells():
    one_dimensional = (
        "array[0..2] of var -5..5: a;\n"
        "constraint a[0] = -4; constraint a[1] = 3; constraint a[2] = 0;\n"
        "constraint min(a) = -4; constraint max(a) = 3;\n"
        "solve satisfy;\n"
    )
    assert _solve(one_dimensional).check() == z3.sat
    assert _solve(one_dimensional.replace("max(a) = 3", "max(a) = 2")).check() == z3.unsat

    two_dimensional = (
        "array[0..1,4..5] of var -8..8: m;\n"
        "constraint m[0,4] = -6; constraint m[0,5] = 7;\n"
        "constraint m[1,4] = 2; constraint m[1,5] = -1;\n"
        "constraint min(m) = -6; constraint max(m) = 7;\n"
        "solve satisfy;\n"
    )
    assert _solve(two_dimensional).check() == z3.sat
    assert _solve(two_dimensional.replace("min(m) = -6", "min(m) = -5")).check() == z3.unsat


def test_whole_array_minmax_output_size_scales_with_number_of_cells():
    def output_size(cells):
        source = (
            f"array[1..{cells}] of var -20..20: a;\n"
            "constraint max(a) = 0;\n"
            "solve satisfy;\n"
        )
        result = sp.translate(source=source, language="minizinc")
        assert result.ok, [d.message for d in result.diagnostic_items]
        return len(result.to_smt2())

    size16 = output_size(16)
    size64 = output_size(64)
    # The balanced comparison tree expands quadratically because each child
    # occurs in both comparison and branch. A left fold would grow
    # exponentially; quadrupling the cells would blow past this ratio by many
    # orders of magnitude.
    assert size64 < size16 * 32 + 1000


def test_whole_parameter_array_minmax_uses_supplied_values(tmp_path):
    source = (
        "array[4..6] of int: costs;\n"
        "int: largest = max(costs);\n"
        "constraint largest = 8;\n"
        "constraint min(costs) = -11;\n"
        "constraint max(costs) = 8;\n"
        "solve satisfy;\n"
    )
    data = tmp_path / "costs.dzn"
    data.write_text("costs = array1d(4..6, [-11, 8, 2]);\n", encoding="utf-8")
    assert _solve(source, [data]).check() == z3.sat

    data.write_text("costs = array1d(4..6, [-11, 7, 2]);\n", encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("fn", ["min", "max"])
def test_numeric_minmax_of_empty_array_is_rejected_as_undefined(fn):
    result = sp.translate(
        source=f"constraint {fn}([]) = 0; solve satisfy;",
        language="minizinc",
    )
    assert not result.ok
    assert any("empty array has no value" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("expression", [
    "max(1 div z, 5)", "min(1 div z, 5)",
    "max(5, 1 div z)", "min(5, 1 div z)",
    "max([1 div z, 5])", "min([1 div z, 5])",
])
def test_minmax_requires_every_operand_in_its_enclosing_boolean_scope(expression):
    # Undefined arithmetic makes its enclosing comparison false, including
    # when the other operand would be the selected extremum. Negation then
    # operates on that Boolean result; it must not hoist the domain globally.
    base = "var -1..1: z; constraint z = 0; "
    assert _solve(base + f"constraint {expression} = 5; solve satisfy;").check() == z3.unsat
    assert _solve(base + f"constraint not ({expression} = 5); solve satisfy;").check() == z3.sat


def test_numeric_pairs_and_fixed_ranges_dispatch_by_argument_shape():
    source = (
        "int: lo = -7; int: hi = -2;"
        "constraint max(-7, -2) = -2; constraint min(-7, -2) = -7;"
        "constraint max(-7..-2) = -2; constraint min(lo..hi) = -7;"
        "constraint max(1+2, 8) = 8; constraint max(1+2..8) = 8;"
        "constraint max([min(1, 3), max(2, 4)]) = 4; solve satisfy;"
    )
    assert _solve(source).check() == z3.sat
