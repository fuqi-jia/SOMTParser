"""Declared array axes must agree with non-JSON literal source axes."""

import json

import pytest

z3 = pytest.importorskip("z3")
import somtparser as sp


def _translate(source, data=()):
    return sp.translate(source=source, language="minizinc", data=list(data))


def _solver(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    return solver


def test_non1_based_numeric_inline_parameter_and_decision_lists_are_rejected():
    parameter = _translate(
        "array[3..4] of int: a = [11,22]; constraint a[3] = 11; solve satisfy;")
    decision = _translate(
        "array[3..4] of var int: a = [11,22]; constraint a[3] = 11; solve satisfy;")
    assert not parameter.ok
    assert not decision.ok
    assert any("indexes differ" in d.message for d in parameter.diagnostic_items)
    assert any("indexes differ" in d.message for d in decision.diagnostic_items)


def test_enum_and_inferred_array_literals_keep_contextual_indexing():
    enum_source = (
        "enum E = {red, blue}; array[E] of int: a = [11,22]; "
        "constraint a[red] = 11; solve satisfy;")
    assert _solver(_translate(enum_source)).check() == z3.sat
    wrong_enum = _translate(enum_source.replace("a[red] = 11", "a[red] = 22"))
    assert _solver(wrong_enum).check() == z3.unsat

    inferred = _translate(
        "array[int] of var int: a = [11,22]; "
        "constraint index_set(a) = 1..2; constraint a[1] = 11; "
        "constraint a[2] = 22; solve satisfy;")
    assert _solver(inferred).check() == z3.sat


def test_matching_explicit_arraynd_origins_are_accepted():
    parameter = _translate(
        "array[3..4] of int: a = array1d(3..4,[11,22]); "
        "constraint a[3] = 11; constraint a[4] = 22; solve satisfy;")
    decision = _translate(
        "array[3..4] of var int: a = array1d(3..4,[11,22]); "
        "constraint a[3] = 11; constraint a[4] = 22; solve satisfy;")
    assert _solver(parameter).check() == z3.sat
    assert _solver(decision).check() == z3.sat


@pytest.mark.parametrize("element_type", ["int", "var int"])
def test_dzn_list_does_not_acquire_a_numeric_declared_origin(tmp_path, element_type):
    source = (
        f"array[3..4] of {element_type}: a; constraint a[3] = 11; "
        "constraint a[4] = 22; solve satisfy;")
    data = tmp_path / "instance.dzn"
    data.write_text("a = [11,22];\n", encoding="utf-8")
    result = _translate(source, [str(data)])
    assert not result.ok
    assert any("different index set" in d.message for d in result.diagnostic_items)


def test_explicit_dzn_shape_and_json_declared_shape_remain_supported(tmp_path):
    source = (
        "array[3..4] of int: a; constraint a[3] = 11; "
        "constraint a[4] = 22; solve satisfy;")
    dzn = tmp_path / "instance.dzn"
    dzn.write_text("a = array1d(3..4,[11,22]);\n", encoding="utf-8")
    assert _solver(_translate(source, [str(dzn)])).check() == z3.sat
    decision_source = (
        "array[3..4] of var int: a; constraint a[3] = 11; "
        "constraint a[4] = 22; solve satisfy;")
    assert _solver(_translate(decision_source, [str(dzn)])).check() == z3.sat

    json_path = tmp_path / "instance.json"
    json_path.write_text(json.dumps({"a": [11, 22]}), encoding="utf-8")
    assert _solver(_translate(source, [str(json_path)])).check() == z3.sat
    wrong = _translate(source.replace("a[3] = 11", "a[3] = 22"), [str(json_path)])
    assert _solver(wrong).check() == z3.unsat


@pytest.mark.parametrize("initializer", [
    "([11,22])",
    "[11] ++ [22]",
    "[i | i in 1..2]",
    "[i | i in 3..4]",
])
@pytest.mark.parametrize("element_type", ["int", "var int"])
def test_nonmatching_numeric_origin_is_checked_after_expression_parsing(
    initializer, element_type
):
    result = _translate(
        f"array[3..4] of {element_type}: a = {initializer}; "
        "constraint a[3] = 11; solve satisfy;"
    )
    assert not result.ok
    assert any("indexes differ" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("element_type", ["int", "var int"])
def test_separate_model_assignment_checks_and_preserves_source_axes(element_type):
    suffix = "constraint a[3] = 11; constraint a[4] = 22; solve satisfy;"
    invalid = _translate(
        f"array[3..4] of {element_type}: a; a = [11,22]; " + suffix
    )
    assert not invalid.ok
    assert any("different index set" in d.message for d in invalid.diagnostic_items)

    explicit = _translate(
        f"array[3..4] of {element_type}: a; "
        "a = array1d(3..4,[11,22]); " + suffix
    )
    assert _solver(explicit).check() == z3.sat


def test_set_array_literal_and_comprehension_origins_are_checked():
    literal = _translate(
        "array[4..5] of set of int: a = [{1},{2}]; "
        "constraint 1 in a[4]; solve satisfy;"
    )
    assert not literal.ok

    comprehension = _translate(
        "array[4..5] of set of int: a = [{i} | i in 1..2]; "
        "constraint 1 in a[4]; solve satisfy;"
    )
    assert not comprehension.ok

    explicit = _translate(
        "array[4..5] of set of int: a = array1d(4..5, [{1},{2}]); "
        "constraint 1 in a[4]; constraint 2 in a[5]; solve satisfy;"
    )
    assert _solver(explicit).check() == z3.sat

    enum = _translate(
        "enum E = {red,blue}; array[E] of set of int: a = [{1},{2}]; "
        "constraint 1 in a[red]; constraint 2 in a[blue]; solve satisfy;"
    )
    assert _solver(enum).check() == z3.sat


def test_enum_array_keeps_contextual_positional_initializers():
    for initializer, expected in [
        ("[11,22]", 11),
        ("([11,22])", 11),
        ("[11] ++ [22]", 11),
        ("[i | i in 1..2]", 1),
    ]:
        source = (
            "enum E = {red, blue}; "
            f"array[E] of int: a = {initializer}; "
            f"constraint a[red] = {expected}; solve satisfy;"
        )
        assert _solver(_translate(source)).check() == z3.sat


def test_dzn_matrix_origin_is_checked_and_array2d_is_explicit(tmp_path):
    source = (
        "array[0..1,0..1] of int: a; "
        "constraint a[0,0] = 11; solve satisfy;")
    wrong = tmp_path / "matrix-literal.dzn"
    wrong.write_text("a = [|11,12|21,22|];\n", encoding="utf-8")
    result = _translate(source, [str(wrong)])
    assert not result.ok
    assert any("different index set" in d.message for d in result.diagnostic_items)

    correct = tmp_path / "matrix-array2d.dzn"
    correct.write_text(
        "a = array2d(0..1,0..1,[11,12,21,22]);\n", encoding="utf-8")
    assert _solver(_translate(source, [str(correct)])).check() == z3.sat


def test_inferred_set_array_comprehension_keeps_its_implicit_axis():
    # Official GT-sort declares this set-array shape as array[int].
    source = (
        "array[int] of set of int: s = [{i} | i in 1..3]; "
        "constraint index_set(s) = 1..3; constraint 2 in s[2]; solve satisfy;")
    assert _solver(_translate(source)).check() == z3.sat
    assert _solver(_translate(source.replace("2 in s[2]", "1 in s[2]"))).check() == z3.unsat


@pytest.mark.parametrize("element_type", ["int", "var int"])
@pytest.mark.parametrize("separate", [False, True])
def test_wrong_explicit_constructor_origin_remains_rejected(element_type, separate):
    source = f"array[3..4] of {element_type}: a"
    source += "; a" if separate else ""
    source += " = array1d(1..2,[11,22]); solve satisfy;"
    assert not _translate(source).ok
