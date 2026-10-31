"""Focused oracle-repair tests for enum default joins and empty array axes."""

import z3
import somtparser as sp


def _translate(source):
    return sp.translate(source=source, language="minizinc")


def _assert_sat(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat


def _assert_error(result):
    assert not result.ok
    assert all("E_INTERNAL" not in str(d.code) for d in result.diagnostic_items)


def _assert_unsat(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat


def test_same_enum_default_retains_nominal_type():
    result = _translate(
        "enum COLOR={Red,Green};COLOR:kept=Red default Green;"
        "constraint kept=Red;solve satisfy;"
    )
    _assert_sat(result)


def test_cross_enum_default_is_rejected_before_int_context_coercion():
    result = _translate(
        "enum COLOR={Red,Green};enum OTHER={Oak,Pine,Elm};"
        "int:joined=Green default Elm;solve satisfy;"
    )
    _assert_error(result)


def test_cross_enum_enum2int_default_retains_nominal_provenance():
    result = _translate(
        "enum COLOR={Red,Green};enum OTHER={Oak,Pine,Elm};"
        "int:joined=enum2int(Green) default enum2int(Elm);"
        "constraint joined=2;solve satisfy;"
    )
    _assert_error(result)


def test_enum2int_numeric_aliases_and_arithmetic_are_plain_integer_contexts():
    aliases = _translate(
        "enum A={A0,A1};enum B={B0,B1,B2};"
        "int:a=enum2int(A1);int:b=enum2int(B2);int:x=a default b;"
        "constraint x=2;solve satisfy;"
    )
    _assert_sat(aliases)
    arithmetic = _translate(
        "enum A={A0,A1};enum B={B0,B1,B2};"
        "int:x=(enum2int(A1)+0) default (enum2int(B2)+0);"
        "constraint x=2;solve satisfy;"
    )
    _assert_sat(arithmetic)


def test_cross_enum_enum2int_default_with_one_uncoerced_operand_is_rejected():
    left = _translate(
        "enum A={A0,A1};enum B={B0,B1,B2};"
        "int:x=enum2int(A1) default B2;solve satisfy;"
    )
    _assert_error(left)
    right = _translate(
        "enum A={A0,A1};enum B={B0,B1,B2};"
        "int:x=A1 default enum2int(B2);solve satisfy;"
    )
    _assert_error(right)


def test_cross_enum_enum2int_comparison_is_rejected():
    result = _translate(
        "enum A={A0,A1};enum B={B0,B1,B2};"
        "constraint enum2int(A1)=enum2int(B2);solve satisfy;"
    )
    _assert_error(result)


def test_mixed_raw_enum_and_enum2int_same_origin_default_joins_enum_in_both_orders():
    left_raw = _translate(
        "enum A={A0,A1};A:x=(A0 default enum2int(A0));"
        "constraint x=A0;solve satisfy;"
    )
    _assert_sat(left_raw)
    right_raw = _translate(
        "enum A={A0,A1};A:x=(enum2int(A0) default A0);"
        "constraint x=A0;solve satisfy;"
    )
    _assert_sat(right_raw)
    int_context_left = _translate(
        "enum A={A0,A1};int:x=(A0 default enum2int(A0));"
        "constraint x=1;solve satisfy;"
    )
    _assert_sat(int_context_left)
    int_context_right = _translate(
        "enum A={A0,A1};int:x=(enum2int(A0) default A0);"
        "constraint x=1;solve satisfy;"
    )
    _assert_sat(int_context_right)


def test_same_origin_default_keeps_identity_for_nested_cross_enum_checks():
    nested = _translate(
        "enum A={A0,A1};enum B={B0,B1};"
        "int:x=((A0 default enum2int(A0)) default B0);solve satisfy;"
    )
    _assert_error(nested)
    comparison = _translate(
        "enum A={A0,A1};enum B={B0,B1};"
        "constraint (A0 default enum2int(A0))=B0;solve satisfy;"
    )
    _assert_error(comparison)


def test_cast_only_same_origin_default_restores_enum_type():
    assignment = _translate(
        "enum A={A0,A1};A:x=(enum2int(A0) default enum2int(A1));"
        "constraint x=A0;solve satisfy;"
    )
    _assert_sat(assignment)
    index = _translate(
        "enum A={A0,A1};array[A]of int:a=[10,20];"
        "constraint a[enum2int(A0) default enum2int(A1)]=10;solve satisfy;"
    )
    _assert_sat(index)


def test_default_join_with_plain_integer_has_no_enum_result_type():
    cast_to_enum = _translate(
        "enum A={A0,A1};A:x=(enum2int(A0) default 1);solve satisfy;"
    )
    _assert_error(cast_to_enum)
    cast_to_int = _translate(
        "enum A={A0,A1};int:x=(enum2int(A0) default 1);"
        "constraint x=1;solve satisfy;"
    )
    _assert_sat(cast_to_int)
    raw_to_enum = _translate("enum A={A0,A1};A:x=(A0 default 1);solve satisfy;")
    _assert_error(raw_to_enum)
    raw_to_int = _translate(
        "enum A={A0,A1};int:x=(A0 default 1);constraint x=1;solve satisfy;"
    )
    _assert_sat(raw_to_int)


def test_plain_integer_join_drops_prior_enum_origin_before_nested_default():
    cast_left = _translate(
        "enum A={A0,A1};enum B={B0,B1};"
        "int:x=((enum2int(A0) default 1) default enum2int(B0));"
        "constraint x=1;solve satisfy;"
    )
    _assert_sat(cast_left)
    raw_left = _translate(
        "enum A={A0,A1};enum B={B0,B1};"
        "int:x=((A0 default 1) default enum2int(B0));"
        "constraint x=1;solve satisfy;"
    )
    _assert_sat(raw_left)
    reverse = _translate(
        "enum A={A0,A1};enum B={B0,B1};"
        "int:x=((1 default enum2int(A0)) default enum2int(B0));solve satisfy;"
    )
    _assert_sat(reverse)
    comparisons = [
        "constraint (enum2int(A0) default 1)=enum2int(B0);",
        "constraint (A0 default 1)=enum2int(B0);",
        "constraint (1 default enum2int(A0))=enum2int(B0);",
    ]
    for comparison in comparisons:
        _assert_sat(_translate("enum A={A0,A1};enum B={B0,B1};" + comparison + "solve satisfy;"))


def test_enum2int_integer_assignment_and_same_enum_default_remain_valid():
    integer = _translate(
        "enum A={A0,A1};int:x=enum2int(A1);constraint x=2;solve satisfy;"
    )
    _assert_sat(integer)
    same_enum = _translate(
        "enum A={A0,A1};int:x=enum2int(A0) default enum2int(A1);"
        "constraint x=1;solve satisfy;"
    )
    _assert_sat(same_enum)


def test_enum2int_does_not_become_an_enum_value_or_enum_index():
    assignment = _translate("enum A={A0,A1};A:x=enum2int(A0);solve satisfy;")
    _assert_error(assignment)
    index = _translate(
        "enum A={A0,A1};array[A]of int:a=[1,2];"
        "constraint a[enum2int(A0)]=1;solve satisfy;"
    )
    _assert_error(index)
    int_index = _translate(
        "enum A={A0,A1};array[1..2]of int:a=[1,2];"
        "constraint a[enum2int(A0)]=1;solve satisfy;"
    )
    _assert_sat(int_index)


def test_different_empty_enum_index_sets_are_compatible_for_empty_rank1_array():
    result = _translate(
        "enum EMPTY={};enum OTHER={};"
        "array[EMPTY]of int:values=array1d(OTHER,[]);solve satisfy;"
    )
    _assert_sat(result)


def test_rank2_axes_that_are_both_empty_may_have_different_enum_identity():
    result = _translate(
        "enum ROW_A={};enum ROW_B={};enum COL_A={};enum COL_B={};"
        "array[ROW_A,COL_A]of int:values=array2d(ROW_B,COL_B,[]);"
        "solve satisfy;"
    )
    _assert_sat(result)


def test_rank2_empty_first_axis_relaxes_only_that_axis_identity():
    result = _translate(
        "enum ROW_A={};enum ROW_B={};enum COL={C0,C1};"
        "array[ROW_A,COL]of int:values=array2d(ROW_B,COL,[]);"
        "solve satisfy;"
    )
    _assert_sat(result)


def test_rank2_empty_second_axis_relaxes_only_that_axis_identity():
    result = _translate(
        "enum ROW={R0,R1};enum COL_A={};enum COL_B={};"
        "array[ROW,COL_A]of int:values=array2d(ROW,COL_B,[]);"
        "solve satisfy;"
    )
    _assert_sat(result)


def test_rank2_whole_empty_array_relaxes_nominal_identity_on_all_axes():
    result = _translate(
        "enum ROW_A={};enum ROW_B={};enum COL_A={A};enum COL_B={B};"
        "array[ROW_A,COL_A]of int:values=array2d(ROW_B,COL_B,[]);"
        "solve satisfy;"
    )
    _assert_sat(result)


def test_rank2_nonempty_first_axis_mismatch_is_relaxed_when_other_axis_empty():
    result = _translate(
        "enum ROW_A={A};enum ROW_B={B};enum COL_A={};enum COL_B={};"
        "array[ROW_A,COL_A]of int:values=array2d(ROW_B,COL_B,[]);"
        "solve satisfy;"
    )
    _assert_sat(result)



def test_whole_empty_array_assignment_relaxes_all_index_axes_and_bounds():
    result = _translate(
        "enum ROW_A={};enum ROW_B={};enum COL_A={A};enum COL_B={B};"
        "array[ROW_A,COL_A]of int:values=array2d(ROW_B,COL_B,[]);solve satisfy;"
    )
    _assert_sat(result)
    numeric_bounds = _translate(
        "enum EA={};enum EB={};"
        "array[EA,1..2]of int:values=array2d(EB,4..6,[]);solve satisfy;"
    )
    _assert_sat(numeric_bounds)


def test_whole_empty_assignment_preserves_declared_array_shape_metadata():
    declared = _translate(
        "enum EA={};enum EB={};array[EA,1..2]of int:x=array2d(EB,4..6,[]);"
        "constraint index_set_2of2(x)=1..2;solve satisfy;"
    )
    _assert_sat(declared)
    initializer = _translate(
        "enum EA={};enum EB={};array[EA,1..2]of int:x=array2d(EB,4..6,[]);"
        "constraint index_set_2of2(x)=4..6;solve satisfy;"
    )
    _assert_unsat(initializer)


def test_empty_shape_coercion_requires_same_rank_and_both_sides_empty():
    rank_mismatch = _translate(
        "enum EA={};enum EB={};array[EA]of int:x=array2d(EB,1..0,[]);solve satisfy;"
    )
    _assert_error(rank_mismatch)
    nonempty_target = _translate(
        "array[1..1,1..2]of int:x=array2d(1..0,1..2,[]);solve satisfy;"
    )
    _assert_error(nonempty_target)
    nonempty_initializer = _translate(
        "array[1..0,1..2]of int:x=array2d(1..1,1..2,[5,6]);solve satisfy;"
    )
    _assert_error(nonempty_initializer)

def test_nonempty_enum_index_mismatch_is_still_rejected():
    result = _translate(
        "enum A={A0};enum B={B0};"
        "array[A]of int:values=array1d(B,[1]);solve satisfy;"
    )
    _assert_error(result)


def test_empty_set_alias_keeps_element_enum_identity():
    result = _translate(
        "enum A={A0};enum B={B0};set of B:empty_b={};"
        "set of A:bad=empty_b;solve satisfy;"
    )
    _assert_error(result)
