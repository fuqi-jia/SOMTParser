"""User-function domains, lexical scope, and array definedness semantics."""

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _solve(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3), ctx=context))
    status = solver.check()
    assert status != z3.unknown, solver.reason_unknown()
    return status


@pytest.mark.parametrize("actual,call,expected", [
    (3, "f(x)=3", z3.unsat),
    (2, "f(x)=2", z3.sat),
    (3, "not (f(x)=3)", z3.sat),
])
def test_scalar_formal_domain_is_per_call_and_survives_negation(
        actual, call, expected):
    source = f"""
set of int: S = 1..2;
var 1..3: x;
function var int: f(var S: value) = value;
constraint x = {actual};
constraint {call};
solve satisfy;
"""
    assert _solve(source) == expected


@pytest.mark.parametrize("actual,call,expected", [
    ("[1, 2]", "f(values)=1", z3.sat),
    # The function reads only cell 1. The domain on its array formal still
    # applies to every actual cell, including the unread second cell.
    ("[1, 3]", "f(values)=1", z3.unsat),
    ("[1, 3]", "not (f(values)=1)", z3.sat),
])
def test_array_formal_domain_covers_every_actual_cell_under_both_polarities(
        actual, call, expected):
    source = f"""
set of int: S = 1..2;
array[1..2] of var 1..3: values = {actual};
function var int: f(array[int] of var S: cells) = cells[1];
constraint {call};
solve satisfy;
"""
    assert _solve(source) == expected


@pytest.mark.parametrize("formal_type,expected", [
    ("int", "9"),
    ("float", "9.0"),
])
def test_boolean_array_actuals_coerce_to_numeric_function_formals(formal_type, expected):
    source = f"""
array[1..2] of bool: flags = [true, false];
function {formal_type}: numeric_total(array[int] of {formal_type}: values) =
    values[1] + values[2] + 8;
constraint numeric_total(flags) = {expected};
solve satisfy;
"""
    assert _solve(source) == z3.sat


def test_empty_boolean_array_can_coerce_to_integer_function_formal():
    source = """
array[1..0] of bool: flags = [];
function bool: array_is_empty(array[int] of int: values) = length(values) = 0;
constraint array_is_empty(flags);
solve satisfy;
"""
    assert _solve(source) == z3.sat


@pytest.mark.parametrize("source", [
    """array[1..0] of float: values = [];
function bool: accept(array[int] of int: actual) = length(actual) = 0;
constraint accept(values); solve satisfy;""",
    """enum A = {a0, a1}; enum B = {b0, b1};
array[1..0] of A: values = [];
function bool: accept(array[int] of B: actual) = length(actual) = 0;
constraint accept(values); solve satisfy;""",
    """array[1..0] of string: values = [];
function bool: accept(array[int] of int: actual) = length(actual) = 0;
constraint accept(values); solve satisfy;""",
])
def test_empty_array_actual_still_checks_formal_element_sort(source):
    # No cells means there is no value-level coercion to inspect. The array's
    # declared element sort still has to match the function formal.
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok


@pytest.mark.parametrize("index,negated,expected", [
    (2, False, z3.unsat),  # bad cell is unselected, but array construction is partial
    (1, False, z3.unsat),  # bad cell is selected
    (2, True, z3.sat),
    (1, True, z3.sat),
])
def test_dynamic_selection_preserves_all_cell_definedness_under_negation(
        index, negated, expected):
    relation = "[1 div divisor, 7][k] = 7"
    if negated:
        relation = f"not ({relation})"
    source = f"""
var 1..2: k;
var int: divisor;
constraint k = {index};
constraint divisor = 0;
constraint {relation};
solve satisfy;
"""
    assert _solve(source) == expected


@pytest.mark.parametrize("index,negated,expected", [
    (3, False, z3.unsat),
    (3, True, z3.sat),
])
def test_dynamic_boolean_selection_out_of_range_has_complementary_polarity(
        index, negated, expected):
    relation = "[i > 1 | i in 1..2][k]"
    if negated:
        relation = f"not ({relation})"
    source = f"""
var 1..3: k;
constraint k = {index};
constraint {relation};
solve satisfy;
"""
    assert _solve(source) == expected


@pytest.mark.parametrize("element_type,expected_values", [
    ("int", "[0, 1]"),
    ("float", "[0.0, 1.0]"),
])
def test_boolean_array_comprehension_coerces_to_numeric_element_type(
        element_type, expected_values):
    source = f"""
array[1..2] of var bool: flags;
array[1..2] of var {element_type}: values = [not flags[i] | i in 1..2];
constraint flags[1] /\\ not flags[2];
constraint values = {expected_values};
solve satisfy;
"""
    assert _solve(source) == z3.sat


def test_comprehension_keeps_values_when_final_generator_tuples_are_filtered():
    source = """
array[1..5] of int: values = [i * 10 + j | i in 1..2, j in 1..3
                                      where i * 10 + j < 23];
constraint values = [11, 12, 13, 21, 22];
solve satisfy;
"""
    assert _solve(source) == z3.sat


def test_nested_dependent_generators_preserve_values_and_filtering():
    source = """
int: total = sum([i + j | i in 1..3, j in 1..i where i + j < 5]);
constraint total = 13;
solve satisfy;
"""
    assert _solve(source) == z3.sat


@pytest.mark.parametrize("generator", [
    "i in 1..2, j in 1..0",
    "i in 1..2, j in 1..2 where false",
])
def test_empty_or_all_filtered_nested_generators_still_typecheck_the_head(generator):
    source = f"array[1..0] of int: values = [{{i}} | {generator}]; solve satisfy;"
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok


def test_forward_functions_and_included_helpers_keep_definition_scope(tmp_path):
    helpers = tmp_path / "helpers.mzn"
    helpers.write_text("function int: global_reader() = global_array[1];\n",
                       encoding="utf-8")
    model = tmp_path / "model.mzn"
    model.write_text("""
array[1..1] of int: global_array = [11];
include "helpers.mzn";
var int: forward_value = double_later(3);
function int: double_later(int: x) = times_two(x);
function int: times_two(int: x) = x * 2;
constraint forward_value = 6;
constraint let { array[1..1] of int: global_array = [99]; }
          in global_reader() = 11;
solve satisfy;
""", encoding="utf-8")

    result = sp.translate(path=str(model), language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3), ctx=context))
    assert solver.check() == z3.sat, solver.reason_unknown()
