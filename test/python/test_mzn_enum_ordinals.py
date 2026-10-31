"""Nominal MiniZinc enums retain local ordinals and type identity."""

import json

import pytest
import z3

import somtparser as sp


def _translate(tmp_path, source, data=None, *, dzn=False):
    kwargs = {"source": source, "language": "minizinc"}
    if data is not None:
        path = tmp_path / ("values.dzn" if dzn else "values.json")
        path.write_text(data if dzn else json.dumps(data, indent=2), encoding="utf-8")
        kwargs["data"] = [str(path)]
    return sp.translate(**kwargs)


def _assert_exact_booleans(result, expected_values):
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected = z3.And(
        *[z3.Bool(name) == value for name, value in expected_values.items()]
    )
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def _assert_forced_boolean_values(result, expected_values):
    """Check selected Boolean consequences while existentially leaving others free."""
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(actual)
    assert solver.check() == z3.sat
    for name, value in expected_values.items():
        solver = z3.Solver()
        solver.add(actual, z3.Bool(name) != value)
        assert solver.check() == z3.unsat


def test_enum_to_int_uses_each_enums_local_one_based_ordinal():
    result = _translate(
        None,
        """
        enum FIRST = {F0, F1};
        enum SECOND = {S0, S1, S2};
        int: explicit_ordinal = enum2int(S1);
        int: implicit_ordinal = S2;
        var bool: explicit_is_two;
        var bool: implicit_is_three;
        constraint explicit_is_two <-> explicit_ordinal = 2;
        constraint implicit_is_three <-> implicit_ordinal = 3;
        solve satisfy;
        """,
    )
    _assert_exact_booleans(
        result, {"explicit_is_two": True, "implicit_is_three": True}
    )


@pytest.mark.parametrize("dzn", [False, True])
def test_scalar_array_and_set_data_keep_nominal_enum_values(tmp_path, dzn):
    source = """
        enum FIRST = {F0, F1};
        enum SECOND = {S0, S1, S2};
        FIRST: first;
        array[1..2] of SECOND: values;
        set of SECOND: selected;
        var bool: first_is_local_two;
        var bool: second_value_is_local_three;
        var bool: selected_has_s2;
        var bool: selected_has_s1;
        constraint first_is_local_two <-> enum2int(first) = 2;
        constraint second_value_is_local_three <-> enum2int(values[2]) = 3;
        constraint selected_has_s2 <-> S2 in selected;
        constraint selected_has_s1 <-> S1 in selected;
        solve satisfy;
    """
    if dzn:
        data = "first=F1; values=[S1,S2]; selected={S0,S2};"
    else:
        data = {
            "first": "F1",
            "values": ["S1", "S2"],
            "selected": {"set": ["S0", "S2"]},
        }
    result = _translate(tmp_path, source, data, dzn=dzn)
    _assert_exact_booleans(
        result,
        {
            "first_is_local_two": True,
            "second_value_is_local_three": True,
            "selected_has_s2": True,
            "selected_has_s1": False,
        },
    )


def test_same_enum_variables_and_generator_indices_preserve_enum_identity():
    result = _translate(
        None,
        """
        enum COLOR = {Red, Green, Blue};
        array[COLOR] of var bool: enabled;
        var COLOR: chosen;
        var COLOR: copied;
        var bool: chosen_is_red;
        var bool: red_enabled;
        var bool: green_enabled;
        var bool: blue_enabled;
        constraint chosen = Red;
        constraint copied = chosen;
        constraint chosen_is_red <-> copied = Red;
        constraint forall(i in COLOR)(enabled[i]);
        constraint red_enabled <-> enabled[Red];
        constraint green_enabled <-> enabled[Green];
        constraint blue_enabled <-> enabled[Blue];
        solve satisfy;
        """,
    )
    _assert_forced_boolean_values(
        result,
        {
            "chosen_is_red": True,
            "red_enabled": True,
            "green_enabled": True,
            "blue_enabled": True,
        },
    )


def test_default_keeps_same_enum_type():
    result = _translate(
        None,
        """
        enum COLOR = {Red, Green};
        COLOR: retained = Red default Green;
        var bool: same_enum_kept;
        constraint same_enum_kept <-> retained = Red;
        solve satisfy;
        """,
    )
    _assert_forced_boolean_values(result, {"same_enum_kept": True})


def test_typed_and_context_inferred_empty_enum_sets():
    result = _translate(
        None,
        """
        enum COLOR = {Red, Green};
        set of COLOR: empty_color = {};
        set of COLOR: empty_color_alias = empty_color;
        var bool: typed_empty_is_empty;
        var bool: same_enum_empty_alias_is_empty;
        var bool: red_absent_from_typed_empty;
        var bool: red_absent_from_inferred_empty;
        constraint typed_empty_is_empty <-> card(empty_color) = 0;
        constraint same_enum_empty_alias_is_empty <-> card(empty_color_alias) = 0;
        constraint red_absent_from_typed_empty <-> not (Red in empty_color);
        constraint red_absent_from_inferred_empty <-> not (Red in {});
        solve satisfy;
        """,
    )
    _assert_forced_boolean_values(
        result,
        {
            "typed_empty_is_empty": True,
            "same_enum_empty_alias_is_empty": True,
            "red_absent_from_typed_empty": True,
            "red_absent_from_inferred_empty": True,
        },
    )


def test_enum_indexed_row_and_column_preserve_the_other_axis():
    result = _translate(
        None,
        """
        enum ROW = {R0, R1};
        enum COL = {C0, C1};
        array[ROW, COL] of int: grid = array2d(ROW, COL, [11, 12, 21, 22]);
        array[COL] of int: selected_row = row(grid, R1);
        array[ROW] of int: selected_column = col(grid, C1);
        var bool: row_lookup;
        var bool: column_lookup;
        constraint row_lookup <-> selected_row[C0] = 21;
        constraint column_lookup <-> selected_column[R0] = 12;
        solve satisfy;
        """,
    )
    _assert_forced_boolean_values(
        result, {"row_lookup": True, "column_lookup": True}
    )


def test_empty_enum_array_comprehension_is_vacuously_true():
    result = _translate(
        None,
        """
        enum E = {E0};
        array[1..0] of E: xs = [];
        var bool: vacuous_enum_property;
        constraint vacuous_enum_property <-> forall(x in xs)(enum2int(x) > 0);
        solve satisfy;
        """,
    )
    _assert_forced_boolean_values(result, {"vacuous_enum_property": True})


@pytest.mark.parametrize(
    "source",
    [
        "enum ROW={R0,R1};enum WRONG={W0,W1};"
        "array[ROW,ROW]of int:grid=array2d(ROW,ROW,[1,2,3,4]);"
        "array[ROW]of int:bad=row(grid,W0);solve satisfy;",
        "enum COL={C0,C1};enum WRONG={W0,W1};"
        "array[COL,COL]of int:grid=array2d(COL,COL,[1,2,3,4]);"
        "array[COL]of int:bad=col(grid,W0);solve satisfy;",
        "enum A={A0};enum B={B0};set of B:bs={};set of A:bad=bs;solve satisfy;",
    ],
)
def test_wrong_enum_row_column_or_typed_empty_set_is_rejected(source):
    result = _translate(None, source)
    assert not result.ok
    assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)


@pytest.mark.parametrize(
    "source",
    [
        "enum A={A0,A1};enum B={B0,B1};A:x=B0;solve satisfy;",
        "enum A={A0,A1};int:n=1;A:x=n;solve satisfy;",
        "enum A={A0,A1};array[A]of var int:x;constraint x[1]=0;solve satisfy;",
        "enum A={A0,A1};enum B={B0,B1};array[A]of var int:x;"
        "constraint x[B0]=0;solve satisfy;",
        "enum A={A0,A1};enum B={B0,B1};"
        "array[A]of int:x=array1d(B,[1,2]);solve satisfy;",
    ],
)
def test_wrong_enum_identity_or_integer_to_enum_coercion_is_rejected(source):
    result = _translate(None, source)
    assert not result.ok
    assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)


def test_plain_int_generator_shadow_does_not_inherit_enum_parameter_type():
    result = _translate(
        None,
        "enum E={E0,E1};E:i=E0;array[E]of var bool:a;"
        "constraint forall(i in 1..2)(a[i]);solve satisfy;",
    )
    assert not result.ok
    assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)


def test_quoted_dzn_string_does_not_coerce_to_enum(tmp_path):
    result = _translate(
        tmp_path,
        "enum COLOR={Red,Blue};COLOR: chosen;solve satisfy;",
        'chosen="Red";',
        dzn=True,
    )
    assert not result.ok
    assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)


@pytest.mark.parametrize("negated", [False, True])
def test_boolean_argument_to_integer_predicate_preserves_relation(negated):
    call = "not pos(b)" if negated else "pos(b)"
    result = sp.translate(source=("predicate pos(var int: a)=a>0;var bool:b;"
                                  "constraint " + call + ";solve satisfy;"),
                          language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected = z3.Not(z3.Bool("b")) if negated else z3.Bool("b")
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("expression,truth", [
    ("Red in {}", False),
    ("not (Red in {})", True),
    ("Red in {} union {Red}", True),
    ("Red in {Red} intersect {}", False),
    ("1 div 0 in {}", False),
    ("not (1 div 0 in {})", True),
])
def test_membership_supplies_empty_literal_type_and_retains_definedness(expression, truth):
    result = sp.translate(source=("enum COLOR={Red,Green};var bool:answer;"
                                  "constraint answer <-> (" + expression + ");solve satisfy;"),
                          language="minizinc")
    _assert_exact_booleans(result, {"answer": truth})
