"""Semantics of MiniZinc parameter arrays of sets built by comprehensions."""

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


def _translate(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


def _solver(source):
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(_translate(source).to_smt2()))
    return solver


def test_outer_array_binder_survives_inner_set_and_exists_comprehensions():
    source = r"""
set of int: moulds = 4..5;
set of int: colors = {1, 3, 5};
set of int: demands = 1..4;
array[demands] of int: demand_color = [1, 3, 1, 5];
array[demands] of int: demand_mould = [4, 4, 5, 5];
array[moulds] of set of colors: demanded_colors_for_mould = array1d(moulds, [
    {c | c in colors where
        exists(d in demands)(demand_color[d] = c /\ demand_mould[d] = m)}
    | m in moulds]);
constraint 1 in demanded_colors_for_mould[4];
constraint 3 in demanded_colors_for_mould[4];
constraint 5 in demanded_colors_for_mould[5];
constraint not (5 in demanded_colors_for_mould[4]);
solve satisfy;
"""
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace(
        "constraint not (5 in demanded_colors_for_mould[4]);",
        "constraint 5 in demanded_colors_for_mould[4];",
    )).check() == z3.unsat


def test_empty_set_array_comprehension_keeps_declared_empty_shape():
    source = r"""
set of int: colors = 1..2;
array[1..0] of set of int: empty = [
    {c | c in colors} | m in 1..0];
solve satisfy;
"""
    assert _solver(source).check() == z3.sat


def test_filtered_comprehension_must_match_declared_shape_cardinality():
    source = r"""
set of int: colors = 1..2;
array[4..5] of set of int: by_index = [
    {c | c in colors} | m in 4..5 where m != 4];
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("produces 1 value(s), but its declared shape has 2 cell(s)" in d.message
               for d in result.diagnostic_items)


def test_array1d_preserves_comprehension_values_on_non1based_indices():
    source = r"""
array[1..2] of set of int: raw_values = [{i} | i in 1..2];
array[4..5] of set of int: values = array1d(4..5, raw_values);
constraint 1 in values[4];
constraint 2 in values[5];
solve satisfy;
"""
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace("2 in values[5]", "2 in values[4]")).check() == z3.unsat


def test_comprehension_cells_obey_sparse_named_set_element_domain():
    source = r"""
set of int: colors = {1, 3};
array[1..2] of set of colors: raw_by_index =
    [{c | c in colors where c = 2 * m - 7} | m in 4..5];
array[4..5] of set of colors: by_index = array1d(4..5, raw_by_index);
constraint 1 in by_index[4];
constraint not (1 in by_index[5]);
constraint 3 in by_index[5];
solve satisfy;
"""
    assert _solver(source).check() == z3.sat

    outside = source.replace(
        "{c | c in colors where c = 2 * m - 7}", "{m - 2}"
    )
    result = sp.translate(source=outside, language="minizinc")
    assert not result.ok


def test_multiple_generator_axes_flatten_in_source_order_into_one_dimensional_target():
    source = r"""
array[1..4] of set of int: raw_values =
    [{i * 10 + j} | i in 1..2, j in 1..2];
array[4..7] of set of int: values = array1d(4..7, raw_values);
constraint 11 in values[4];
constraint 12 in values[5];
constraint 21 in values[6];
constraint 22 in values[7];
solve satisfy;
"""
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace(
        "constraint 21 in values[6];", "constraint 21 in values[5];"
    )).check() == z3.unsat


def test_literal_set_generator_has_same_order_as_named_set():
    source = r"""
set of int: indices = {3, 1, 3, 2};
array[1..3] of set of int: literal = [{i} | i in {3, 1, 3, 2}];
array[1..3] of set of int: named = [{i} | i in indices];
constraint forall(i in 1..3)(i in literal[i] /\ i in named[i]);
solve satisfy;
"""
    assert _solver(source).check() == z3.sat


def test_nested_same_name_generator_restores_outer_and_global_bindings():
    source = r"""
int: i = 99;
array[1..2] of set of int: values = [
    {i + sum(i in 1..2)(i) + i} | i in 1..2];
constraint 5 in values[1];
constraint 7 in values[2];
constraint i = 99;
solve satisfy;
"""
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace("7 in values[2]", "5 in values[2]")).check() == z3.unsat


def test_two_dimensional_set_literal_is_not_treated_as_comprehension():
    source = """
array[4..5, -1..0] of set of int: cells = array2d(4..5, -1..0, [{2}, {7}, {11}, {19}]);
constraint 19 in cells[5, 0];
constraint not (11 in cells[5, 0]);
solve satisfy;
"""
    assert _solver(source).check() == z3.sat


@pytest.mark.parametrize("generator", ["i in 1..0", "i in 1..2 where false"])
def test_vacuous_comprehension_does_not_accept_a_nonset_head(generator):
    result = sp.translate(
        source=f"array[1..0] of set of int: cells = [true | {generator}]; solve satisfy;",
        language="minizinc",
    )
    assert not result.ok


@pytest.mark.parametrize("initializer", [
    "array1d(3..4, [{i} | i in 1..2])",
    "array1d(3..4, ([{i} | i in 1..1] ++ [{2}]))",
])
def test_constructed_set_comprehensions_keep_generator_values(initializer):
    source = (
        f"array[3..4] of set of int: s = {initializer};"
        "constraint s[3] = {1}; constraint s[4] = {2}; solve satisfy;"
    )
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace("s[4] = {2}", "s[4] = {1}")).check() == z3.unsat


def test_constructed_set_comprehension_rejects_another_enum_type():
    source = (
        "enum E = {a,b}; enum F = {c,d};"
        "array[1..2] of set of E: s = array1d(1..2, [{i} | i in F]);"
        "solve satisfy;"
    )
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("enum element type" in d.message for d in result.diagnostic_items)
