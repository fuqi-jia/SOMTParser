"""Data-file array index sets retain their source origins in model scope."""

import json

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


def _translate(source, data_path):
    result = sp.translate(source=source, language="minizinc", data=[str(data_path)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


def _data(tmp_path, text, suffix="dzn"):
    path = tmp_path / ("instance." + suffix)
    path.write_text(text, encoding="utf-8")
    return path


def _check(source, data_path):
    result = _translate(source, data_path)
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    return solver


def test_dzn_array2d_resolves_model_index_sets_and_keeps_row_major_order(tmp_path):
    source = (
        "set of int: ROWS = 2..3;\n"
        "set of int: COLS = 4..5;\n"
        "array[ROWS,COLS] of int: M;\n"
        "constraint M[2,4] = 11;\n"
        "constraint M[2,5] = 12;\n"
        "constraint M[3,4] = 21;\n"
        "constraint M[3,5] = 22;\n"
        "solve satisfy;\n"
    )
    data = _data(tmp_path, "M = array2d(ROWS, COLS, [11, 12, 21, 22]);\n")
    assert _check(source, data).check() == z3.sat

    # All four constants are distinct, so a transpose, changed stride, or
    # column-major flattening makes at least one source relation false.
    wrong = source.replace("M[2,4] = 11", "M[2,4] = 12")
    assert _check(wrong, data).check() == z3.unsat


def test_explicit_same_extent_different_origin_is_rejected(tmp_path):
    source = "array[0..1,4..5] of int: M; solve satisfy;"
    data = _data(tmp_path, "M = array2d(2..3, 4..5, [11, 12, 21, 22]);\n")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any("different index set" in d.message for d in result.diagnostic_items)


def test_plain_list_and_explicit_array1d_must_match_declared_indices(tmp_path):
    source = "array[0..1] of int: M; constraint M[0] = 7; solve satisfy;"
    implicit = _data(tmp_path, "M = [7, 8];\n")
    result = sp.translate(source=source, language="minizinc", data=[str(implicit)])
    assert not result.ok
    assert any("different index set" in d.message for d in result.diagnostic_items)

    explicit = _data(tmp_path, "M = array1d(0..1, [7, 8]);\n")
    assert _check(source, explicit).check() == z3.sat

    wrong = _data(tmp_path, "M = array1d(1..2, [7, 8]);\n")
    result = sp.translate(source=source, language="minizinc", data=[str(wrong)])
    assert not result.ok
    assert any("different index set" in d.message for d in result.diagnostic_items)


def test_json_nested_arrays_rebase_synthetic_shape_indices(tmp_path):
    source = (
        "array[0..1,4..5] of int: M;\n"
        "constraint M[0,4] = 11;\n"
        "constraint M[0,5] = 12;\n"
        "constraint M[1,4] = 21;\n"
        "constraint M[1,5] = 22;\n"
        "solve satisfy;\n"
    )
    data = tmp_path / "instance.json"
    data.write_text(json.dumps({"M": [[11, 12], [21, 22]]}), encoding="utf-8")
    assert _check(source, data).check() == z3.sat

    wrong = source.replace("M[0,4] = 11", "M[0,4] = 12")
    assert _check(wrong, data).check() == z3.unsat


def test_json_matrix_coerces_to_non1_based_named_set_array(tmp_path):
    source = (
        "set of int: D = {1,2,3};\n"
        "array[0..1] of set of D: S;\n"
        "constraint 1 in S[0];\n"
        "constraint 2 in S[0];\n"
        "constraint 2 in S[1];\n"
        "constraint 3 in S[1];\n"
        "constraint card(S[0]) = 2;\n"
        "constraint card(S[1]) = 2;\n"
        "solve satisfy;\n"
    )
    data = tmp_path / "sets.json"
    data.write_text(json.dumps({"S": [[1, 2], [2, 3]]}), encoding="utf-8")
    assert _check(source, data).check() == z3.sat

    wrong = source.replace("constraint 1 in S[0]", "constraint 3 in S[0]")
    assert _check(wrong, data).check() == z3.unsat

    wrong_cardinality = source.replace("card(S[0]) = 2", "card(S[0]) = 1")
    assert _check(wrong_cardinality, data).check() == z3.unsat

    data.write_text(json.dumps({"S": [[1, 4], [2, 3]]}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any("outside" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("symbol,model,reason", [
    ("MISSING", "array[1..2] of int: M;", "not a known fixed integer set"),
    ("S", "set of int: S = {1, 3}; array[1..2] of int: M;", "is sparse"),
])
def test_deferred_unknown_or_sparse_index_set_is_rejected(
        symbol, model, reason, tmp_path):
    source = model + "\nsolve satisfy;"
    data = _data(tmp_path, f"M = array1d({symbol}, [7, 8]);\n")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any(reason in d.message for d in result.diagnostic_items)


def test_empty_deferred_dimension_has_zero_cells_without_rebasing(tmp_path):
    source = (
        "set of int: ROWS = {};\n"
        "set of int: COLS = 4..5;\n"
        "array[ROWS,COLS] of int: M;\n"
        "solve satisfy;\n"
    )
    data = _data(tmp_path, "M = array2d(ROWS, COLS, []);\n")
    assert _check(source, data).check() == z3.sat


def test_constructor_dimension_count_and_payload_size_are_checked(tmp_path):
    wrong_rank = _data(tmp_path, "M = array2d(1..2, 1..2, [1, 2, 3, 4]);\n")
    result = sp.translate(
        source="array[1..4] of int: M; solve satisfy;",
        language="minizinc", data=[str(wrong_rank)])
    assert not result.ok
    assert any("dimension(s)" in d.message for d in result.diagnostic_items)

    wrong_size = _data(tmp_path, "M = array2d(1..2, 1..2, [1, 2, 3]);\n")
    result = sp.translate(
        source="array[1..2,1..2] of int: M; solve satisfy;",
        language="minizinc", data=[str(wrong_size)])
    assert not result.ok
    assert any("element(s)" in d.message for d in result.diagnostic_items)


def test_bounded_integer_parameter_array_checks_dzn_values_and_relations(tmp_path):
    source = (
        "array[1..2] of 0..1: M;\n"
        "constraint M[1] = 0;\n"
        "constraint M[2] = 1;\n"
        "solve satisfy;\n"
    )
    data = _data(tmp_path, "M = array1d(1..2, [0, 1]);\n")
    assert _check(source, data).check() == z3.sat

    wrong_cell = source.replace("M[1] = 0", "M[1] = 1")
    assert _check(wrong_cell, data).check() == z3.unsat

    outside = _data(tmp_path, "M = array1d(1..2, [0, 2]);\n")
    result = sp.translate(source=source, language="minizinc", data=[str(outside)])
    assert not result.ok
    assert any("outside that domain" in d.message for d in result.diagnostic_items)


def test_named_sparse_element_domain_checks_external_dzn_membership(tmp_path):
    source = (
        "set of int: D = {1,3};\n"
        "array[1..1] of D: M;\n"
        "solve satisfy;\n"
    )
    invalid = _data(tmp_path, "M = [2];\n")
    result = sp.translate(source=source, language="minizinc", data=[str(invalid)])
    assert not result.ok
    assert any("outside that domain" in d.message for d in result.diagnostic_items)


def test_bounded_integer_array_accepts_parameter_range_and_rejects_bool_bound(tmp_path):
    source = (
        "int: lo; int: hi;\n"
        "array[1..2] of lo..hi: M;\n"
        "constraint M[1] = 0; constraint M[2] = 1;\n"
        "solve satisfy;\n"
    )
    data = _data(tmp_path, "lo = 0; hi = 1; M = [0, 1];\n")
    assert _check(source, data).check() == z3.sat

    bool_bound = (
        "bool: lo = false;\n"
        "array[1..1] of lo..1: M;\n"
        "solve satisfy;\n"
    )
    result = sp.translate(source=bool_bound, language="minizinc")
    assert not result.ok
