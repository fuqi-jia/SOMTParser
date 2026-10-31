"""Decision-indexed reads from fixed MiniZinc parameter arrays."""

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


def _solver(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    return solver


def test_dynamic_index_selects_the_exact_parameter_value():
    source = """
array[1..2] of int: costs = [7, 11];
array[1..1] of var 1..2: selected;
constraint selected[1] = 2;
constraint costs[selected[1]] = 11;
solve satisfy;
"""
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace(
        "costs[selected[1]] = 11", "costs[selected[1]] = 7"
    )).check() == z3.unsat


def test_mixed_fixed_and_dynamic_indices_select_the_row_major_matrix_cell():
    source = """
array[4..5, -1..0] of int: duration = array2d(4..5, -1..0, [2, 7, 11, 19]);
array[1..1] of var 4..5: row;
array[1..1] of var -1..0: column;
constraint row[1] = 5;
constraint column[1] = 0;
constraint duration[row[1], column[1]] = 19;
solve satisfy;
"""
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace(
        "duration[row[1], column[1]] = 19",
        "duration[row[1], column[1]] = 11",
    )).check() == z3.unsat


def test_dynamic_read_keeps_parameter_array_index_definedness():
    source = """
array[1..2] of int: costs = [7, 11];
var int: index;
constraint index = 0;
constraint costs[index] = 7;
solve satisfy;
"""
    # SMT arrays are total, but MiniZinc indexing outside 1..2 is undefined;
    # the relational definedness obligation must therefore make this UNSAT.
    assert _solver(source).check() == z3.unsat


def test_negated_out_of_range_read_keeps_undefinedness_in_negated_scope():
    source = """
array[1..2] of int: costs = [7, 11];
var int: index;
constraint index = 0;
constraint not (costs[index] = 7);
solve satisfy;
"""
    # The undefined read is false in positive polarity, so its negation is true.
    assert _solver(source).check() == z3.sat


def test_partial_index_expression_is_strict_in_positive_and_negated_polarity():
    positive = """
array[1..2] of int: costs = [7, 11];
constraint costs[1 div 0] = 7;
solve satisfy;
"""
    negative = positive.replace(
        "constraint costs[1 div 0] = 7;",
        "constraint not (costs[1 div 0] = 7);",
    )
    assert _solver(positive).check() == z3.unsat
    assert _solver(negative).check() == z3.sat


@pytest.mark.parametrize("index, value, expected", [
    (1, 7, z3.sat), (1, 8, z3.unsat), (2, 23, z3.sat),
    (3, 11, z3.sat), (3, 7, z3.unsat),
])
def test_dynamic_index_preserves_fixed_cells_and_free_initializer_holes(index, value, expected):
    source = f"""
array[1..3] of var int: costs = [7, _, 11];
var 1..3: i;
constraint i = {index};
constraint costs[i] = {value};
solve satisfy;
"""
    assert _solver(source).check() == expected


@pytest.mark.parametrize("negated, expected", [(False, z3.unsat), (True, z3.sat)])
def test_algebraically_constant_partial_index_still_requires_definedness(negated, expected):
    relation = "costs[0 * (1 div 0) + 1] = 7"
    if negated:
        relation = f"not ({relation})"
    source = f"array[1..2] of int: costs = [7, 11]; constraint {relation}; solve satisfy;"
    assert _solver(source).check() == expected


@pytest.mark.parametrize("kind, cells, expected, wrong", [
    ("bool", "false, true", "true", "false"),
    ("string", '\"red\", \"blue\"', '\"blue\"', '\"red\"'),
])
def test_dynamic_index_preserves_noninteger_cell_sort(kind, cells, expected, wrong):
    prefix = f"array[1..2] of {kind}: cells = [{cells}]; var 1..2: i; constraint i = 2;"
    assert _solver(prefix + f"constraint cells[i] = {expected}; solve satisfy;").check() == z3.sat
    assert _solver(prefix + f"constraint cells[i] = {wrong}; solve satisfy;").check() == z3.unsat
