"""Finite constructed enums checked through forced Boolean consequences.

Constructor and inverse names below follow MiniZinc 2.9.4: the inverse
identifier uses Unicode superscript minus one (``P⁻¹``). Partial constructor
inverse behavior remains an unresolved reference probe; this file asserts
only fixed, in-domain applications and indexed data with complete coverage.
"""
import pytest
import z3
import somtparser as sp


def _translate(source, *, tmp_path=None, data=None):
    kwargs = {"source": source, "language": "minizinc"}
    if data is not None:
        path = tmp_path / "constructed-values.dzn"
        path.write_text(data, encoding="utf-8")
        kwargs["data"] = [str(path)]
    return sp.translate(**kwargs)


def _assert_forced_boolean_values(result, expected_values):
    """Leave unrelated model variables existential while checking each fact."""
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(actual)
    assert solver.check() == z3.sat
    for name, value in expected_values.items():
        solver = z3.Solver()
        solver.add(actual, z3.Bool(name) != value)
        assert solver.check() == z3.unsat, name


def _assert_solver_outcome(result, expected):
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == expected


def test_integer_range_constructor_uses_local_ordinals_and_zero_arg_set():
    result = _translate("""
enum Earlier = {E0, E1, E2, E3};
enum Product = P(1..3);
var bool: p1_is_one;
var bool: p2_is_two;
var bool: p3_is_three;
var bool: inverse_returns_argument;
var bool: p2_is_in_constructor_set;
var bool: constructor_set_has_three_values;
constraint p1_is_one <-> enum2int(P(1)) = 1;
constraint p2_is_two <-> enum2int(P(2)) = 2;
constraint p3_is_three <-> enum2int(P(3)) = 3;
constraint inverse_returns_argument <-> P⁻¹(P(2)) = 2;
constraint p2_is_in_constructor_set <-> P(2) in P();
constraint constructor_set_has_three_values <-> card(P()) = 3;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {
        "p1_is_one": True,
        "p2_is_two": True,
        "p3_is_three": True,
        "inverse_returns_argument": True,
        "p2_is_in_constructor_set": True,
        "constructor_set_has_three_values": True,
    })


def test_shifted_constructor_domain_separates_enum_ordinal_from_argument():
    result = _translate("""
enum Noise = {N0, N1};
enum Shifted = Q(4..6);
var bool: q4_is_local_one;
var bool: q5_is_local_two;
var bool: inverse_returns_five;
constraint q4_is_local_one <-> enum2int(Q(4)) = 1;
constraint q5_is_local_two <-> enum2int(Q(5)) = 2;
constraint inverse_returns_five <-> Q⁻¹(Q(5)) = 5;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {
        "q4_is_local_one": True,
        "q5_is_local_two": True,
        "inverse_returns_five": True,
    })


def test_sparse_constructor_uses_sorted_domain_rank_and_inverse():
    result = _translate("""
enum Sparse = S({-4, 2, 9});
var bool: s_neg4_is_one;
var bool: s2_is_two;
var bool: s9_is_three;
var bool: inverse_returns_nine;
constraint s_neg4_is_one <-> enum2int(S(-4)) = 1;
constraint s2_is_two <-> enum2int(S(2)) = 2;
constraint s9_is_three <-> enum2int(S(9)) = 3;
constraint inverse_returns_nine <-> S⁻¹(S(9)) = 9;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {
        "s_neg4_is_one": True,
        "s2_is_two": True,
        "s9_is_three": True,
        "inverse_returns_nine": True,
    })


def test_chained_constructor_maps_nested_values_and_inverse():
    result = _translate("""
enum Base = {B0, B1};
enum Inner = A(Base);
enum Outer = C(Inner);
var bool: nested_value_is_second;
var bool: inverse_chain_returns_b1;
constraint nested_value_is_second <-> enum2int(C(A(B1))) = 2;
constraint inverse_chain_returns_b1 <-> A⁻¹(C⁻¹(C(A(B1)))) = B1;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {
        "nested_value_is_second": True,
        "inverse_chain_returns_b1": True,
    })


def test_concatenated_constructor_domains_have_consecutive_ordinals():
    result = _translate("""
enum Base = {B0, B1};
enum Combined = Left(Base) ++ Right(Base) ++ {None};
var bool: left_b0_is_one;
var bool: left_b1_is_two;
var bool: right_b0_is_three;
var bool: right_b1_is_four;
var bool: none_is_five;
var bool: right_inverse_returns_b1;
constraint left_b0_is_one <-> enum2int(Left(B0)) = 1;
constraint left_b1_is_two <-> enum2int(Left(B1)) = 2;
constraint right_b0_is_three <-> enum2int(Right(B0)) = 3;
constraint right_b1_is_four <-> enum2int(Right(B1)) = 4;
constraint none_is_five <-> enum2int(None) = 5;
constraint right_inverse_returns_b1 <-> Right⁻¹(Right(B1)) = B1;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {
        "left_b0_is_one": True,
        "left_b1_is_two": True,
        "right_b0_is_three": True,
        "right_b1_is_four": True,
        "none_is_five": True,
        "right_inverse_returns_b1": True,
    })


def test_constructor_enum_domain_can_be_supplied_by_dzn(tmp_path):
    result = _translate("""
enum Product;
var bool: p1_is_one;
var bool: p2_is_two;
var bool: p3_is_three;
constraint p1_is_one <-> enum2int(P(1)) = 1;
constraint p2_is_two <-> enum2int(P(2)) = 2;
constraint p3_is_three <-> enum2int(P(3)) = 3;
solve satisfy;
""", tmp_path=tmp_path, data="Product = P(1..3);")
    _assert_forced_boolean_values(result, {
        "p1_is_one": True,
        "p2_is_two": True,
        "p3_is_three": True,
    })


def test_dzn_constructed_scalar_and_list_values_with_reversed_dependencies(tmp_path):
    result = _translate("""
enum Base;
enum Wrapped = C(Base);
Wrapped: chosen;
array[1..2] of Wrapped: values;
var bool: scalar_is_c_b1;
var bool: first_item_is_c_b0;
var bool: second_item_is_c_b1;
constraint scalar_is_c_b1 <-> chosen = C(B1);
constraint first_item_is_c_b0 <-> values[1] = C(B0);
constraint second_item_is_c_b1 <-> values[2] = C(B1);
solve satisfy;
""", tmp_path=tmp_path,
        data="chosen=C(B1); values=[C(B0),C(B1)]; Base={B0,B1};")
    _assert_forced_boolean_values(result, {
        "scalar_is_c_b1": True,
        "first_item_is_c_b0": True,
        "second_item_is_c_b1": True,
    })


def test_indexed_product_dimension_matrix_uses_named_row_and_column_headers(tmp_path):
    result = _translate("""
enum Product;
enum Dimension = {Length, Width, Height};
array[Product, Dimension] of int: product_size;
var bool: p1_length_is_four;
var bool: p2_width_is_two;
var bool: p3_height_is_four;
constraint p1_length_is_four <-> product_size[P(1), Length] = 4;
constraint p2_width_is_two <-> product_size[P(2), Width] = 2;
constraint p3_height_is_four <-> product_size[P(3), Height] = 4;
solve satisfy;
""", tmp_path=tmp_path, data="""
Product = P(1..3);
product_size = [| Length: Width: Height: |
  P(1): 4, 3, 3
| P(2): 5, 2, 7
| P(3): 7, 3, 4 |];
""")
    _assert_forced_boolean_values(result, {
        "p1_length_is_four": True,
        "p2_width_is_two": True,
        "p3_height_is_four": True,
    })


def test_indexed_matrix_reorders_headers_and_rows_with_their_payload(tmp_path):
    result = _translate("""
enum Product;
enum Dimension = {Length, Width, Height};
array[Product, Dimension] of int: product_size;
var bool: p1_length_is_four;
var bool: p2_height_is_seven;
var bool: p3_width_is_three;
constraint p1_length_is_four <-> product_size[P(1), Length] = 4;
constraint p2_height_is_seven <-> product_size[P(2), Height] = 7;
constraint p3_width_is_three <-> product_size[P(3), Width] = 3;
solve satisfy;
""", tmp_path=tmp_path, data="""
Product = P(1..3);
product_size = [| Height: Length: Width: |
  P(3): 4, 7, 3
| P(1): 3, 4, 3
| P(2): 7, 5, 2 |];
""")
    _assert_forced_boolean_values(result, {
        "p1_length_is_four": True,
        "p2_height_is_seven": True,
        "p3_width_is_three": True,
    })


def test_row_only_indexed_matrix_headers_map_payload(tmp_path):
    result = _translate("""
enum Product;
array[Product, 1..2] of int: row_values;
var bool: p1_second_is_eleven;
var bool: p2_first_is_twenty;
constraint p1_second_is_eleven <-> row_values[P(1), 2] = 11;
constraint p2_first_is_twenty <-> row_values[P(2), 1] = 20;
solve satisfy;
""", tmp_path=tmp_path, data="""
Product = P(1..2);
row_values = [| P(1): 10, 11 | P(2): 20, 21 |];
""")
    _assert_forced_boolean_values(result, {
        "p1_second_is_eleven": True,
        "p2_first_is_twenty": True,
    })


def test_column_only_indexed_matrix_headers_map_payload(tmp_path):
    result = _translate("""
enum Dimension = {Length, Width, Height};
array[1..2, Dimension] of int: column_values;
var bool: row1_width_is_two;
var bool: row2_height_is_six;
constraint row1_width_is_two <-> column_values[1, Width] = 2;
constraint row2_height_is_six <-> column_values[2, Height] = 6;
solve satisfy;
""", tmp_path=tmp_path, data="""
column_values = [| Length: Width: Height: | 1, 2, 3 | 4, 5, 6 |];
""")
    _assert_forced_boolean_values(result, {
        "row1_width_is_two": True,
        "row2_height_is_six": True,
    })


def test_indexed_boolean_matrix_preserves_boolean_payload(tmp_path):
    result = _translate("""
enum Product;
enum Dimension = {Length, Width};
array[Product, Dimension] of bool: enabled;
var bool: p1_length_enabled;
var bool: p2_width_disabled;
constraint p1_length_enabled <-> enabled[P(1), Length];
constraint p2_width_disabled <-> not enabled[P(2), Width];
solve satisfy;
""", tmp_path=tmp_path, data="""
Product = P(1..2);
enabled = [| Length: Width: | P(1): true, false | P(2): false, false |];
""")
    _assert_forced_boolean_values(result, {
        "p1_length_enabled": True,
        "p2_width_disabled": True,
    })


def test_indexed_decision_matrix_underscore_hole_stays_free(tmp_path):
    result = _translate("""
enum Product;
enum Dimension = {Length, Width};
array[Product, Dimension] of var int: values;
var bool: fixed_cell_keeps_its_value;
var bool: other_fixed_cell_keeps_its_value;
var bool: hole_can_be_zero;
constraint fixed_cell_keeps_its_value <-> values[P(2), Width] = 7;
constraint other_fixed_cell_keeps_its_value <-> values[P(1), Length] = 4;
constraint hole_can_be_zero <-> values[P(2), Length] = 0;
solve satisfy;
""", tmp_path=tmp_path, data="""
Product = P(1..2);
values = [| Width: Length: | P(2): 7, _ | P(1): _, 4 |];
""")
    _assert_forced_boolean_values(result, {
        "fixed_cell_keeps_its_value": True,
        "other_fixed_cell_keeps_its_value": True,
    })
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    for value in (True, False):
        solver = z3.Solver()
        solver.add(actual, z3.Bool("hole_can_be_zero") == value)
        assert solver.check() == z3.sat


def test_indexed_string_matrix_reorders_rows_columns_and_payload(tmp_path):
    result = _translate("""
enum Product;
enum Label = {Label0, Label1};
array[Product, Label] of string: labels;
var bool: p1_label0_is_alpha;
var bool: p2_label1_is_delta;
constraint p1_label0_is_alpha <-> labels[P(1), Label0] = "alpha";
constraint p2_label1_is_delta <-> labels[P(2), Label1] = "delta";
solve satisfy;
""", tmp_path=tmp_path, data="""
Product = P(1..2);
labels = [| Label1: Label0: | P(2): "delta", "gamma" | P(1): "beta", "alpha" |];
""")
    _assert_forced_boolean_values(result, {
        "p1_label0_is_alpha": True,
        "p2_label1_is_delta": True,
    })


def test_indexed_same_enum_set_matrix_reorders_set_payload(tmp_path):
    result = _translate("""
enum Product;
enum Dimension = {D0, D1};
enum Colour = {Red, Green, Blue};
array[Product, Dimension] of set of Colour: picks;
var bool: p1_d0_has_blue;
var bool: p2_d1_has_green;
constraint p1_d0_has_blue <-> Blue in picks[P(1), D0];
constraint p2_d1_has_green <-> Green in picks[P(2), D1];
solve satisfy;
""", tmp_path=tmp_path, data="""
Product = P(1..2);
picks = [| D1: D0: | P(2): {Green}, {Blue} | P(1): {Red}, {Blue} |];
""")
    _assert_forced_boolean_values(result, {
        "p1_d0_has_blue": True,
        "p2_d1_has_green": True,
    })


@pytest.mark.parametrize("data", [
    # A row label outside the model's Product index set.
    "Product=P(1..2); values=[| C0: C1: | P(1): 1,2 | P(3): 3,4 |];",
    # A duplicate named row cannot stand in for the missing P(2) row.
    "Product=P(1..2); values=[| C0: C1: | P(1): 1,2 | P(1): 3,4 |];",
    # Sparse row labels leave an index in the declared Product set uncovered.
    "Product=P(1..3); values=[| C0: C1: | P(1): 1,2 | P(3): 3,4 |];",
    # The named column does not belong to the model's Dimension set.
    "Product=P(1..1); values=[| C0: Wrong: | P(1): 1,2 |];",
])
def test_indexed_matrix_rejects_mismatched_duplicate_or_sparse_headers(
    tmp_path, data
):
    source = """
enum Product;
enum Dimension = {C0, C1};
array[Product, Dimension] of int: values;
solve satisfy;
"""
    result = _translate(source, tmp_path=tmp_path, data=data)
    assert not result.ok
    assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)


def test_constructor_over_enum_base_and_appended_none_keep_type_ordinals():
    result = _translate("""
enum Base = {B0, B1};
enum Other = {O0, O1, O2};
enum ActivitiesOrNone = A(Base) ++ {None};
var bool: a_b0_is_one;
var bool: a_b1_is_two;
var bool: none_is_three;
var bool: a_b0_in_constructor_set;
var bool: a_b1_in_constructor_set;
var bool: none_outside_constructor_set;
constraint a_b0_is_one <-> enum2int(A(B0)) = 1;
constraint a_b1_is_two <-> enum2int(A(B1)) = 2;
constraint none_is_three <-> enum2int(None) = 3;
constraint a_b0_in_constructor_set <-> A(B0) in A();
constraint a_b1_in_constructor_set <-> A(B1) in A();
constraint none_outside_constructor_set <-> not (None in A());
solve satisfy;
""")
    _assert_forced_boolean_values(result, {
        "a_b0_is_one": True,
        "a_b1_is_two": True,
        "none_is_three": True,
        "a_b0_in_constructor_set": True,
        "a_b1_in_constructor_set": True,
        "none_outside_constructor_set": True,
    })


@pytest.mark.parametrize("source", [
    # The pinned typechecker requires a one-argument enum constructor.
    "enum Product=P(1..3);constraint P(1,2)=P(1);solve satisfy;",
    # A(Base) cannot be applied to a member of a nominally distinct enum.
    "enum Base={B0,B1};enum Other={O0,O1};enum T=A(Base);"
    "var T:value=A(O0);solve satisfy;",
    # A constructor name cannot be overloaded across different base enums.
    "enum A={A0,A1};enum B={B0,B1};enum X=C(A);enum Y=C(B);"
    "X:x=C(A0);Y:y=C(B1);constraint enum2int(x)=1 /\\ enum2int(y)=2;"
    "solve satisfy;",
])
def test_malformed_constructor_arity_or_nominal_argument_is_rejected(source):
    result = _translate(source)
    assert not result.ok
    assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)


def test_constructor_wrong_ordinal_is_unsatisfiable():
    result = _translate("""
enum Product = P(1..3);
constraint enum2int(P(2)) = 3;
solve satisfy;
""")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("expression, expected", [
    ("P(index) = P(1)", z3.unsat),
    ("not (P(index) = P(1))", z3.sat),
    ("(P(index) default P(1)) = P(1)", z3.sat),
])
def test_out_of_domain_dynamic_constructor_uses_partial_definedness(
    expression, expected
):
    result = _translate(f"""
enum Product = P(1..3);
var int: index;
constraint index = 4;
constraint {expression};
solve satisfy;
""")
    _assert_solver_outcome(result, expected)


@pytest.mark.parametrize("domain, constructor", [
    ("P(1..3)", "P"),
    ("S({-4,2,9})", "S"),
])
@pytest.mark.parametrize("binding, argument", [
    ("Product: value = Outside;", "Outside"),
    ("var Product: value; constraint value = Outside;", "value"),
])
@pytest.mark.parametrize("context, outcome", [
    ("{inverse}=1", z3.unsat),
    ("not ({inverse}=1)", z3.sat),
    ("({inverse} default 99)=99", z3.sat),
])
def test_constructor_inverse_outside_own_image_is_partial(
    domain, constructor, binding, argument, context, outcome
):
    result = _translate(f"""
enum Product = {domain} ++ {{Outside}};
{binding}
constraint {context.format(inverse=f"{constructor}⁻¹({argument})")};
solve satisfy;
""")
    _assert_solver_outcome(result, outcome)


@pytest.mark.parametrize("domain, constructor", [
    ("P(1..3)", "P"),
    ("S({-4,2,9})", "S"),
])
@pytest.mark.parametrize("binding, expected", [
    ("par-scalar-not", "error"),
    ("par-array-not", "error"),
    ("par-scalar-default", "sat"),
    ("par-array-default", "sat"),
    ("let-constant-not", "unsat"),
    ("let-constant-default", "sat"),
])
def test_inverse_definedness_survives_constant_binding_contexts(
    domain, constructor, binding, expected
):
    inverse = f"{constructor}⁻¹(Outside)"
    declaration = ""
    if binding == "par-scalar-not":
        declaration = f"int: inverse_value = {inverse};"
        constraint = "not (inverse_value = 1)"
    elif binding == "par-array-not":
        declaration = f"array[1..1] of int: inverse_value = [{inverse}];"
        constraint = "not (inverse_value[1] = 1)"
    elif binding == "par-scalar-default":
        declaration = f"int: inverse_value = {inverse} default 99;"
        constraint = "inverse_value = 99"
    elif binding == "par-array-default":
        declaration = f"array[1..1] of int: inverse_value = [{inverse} default 99];"
        constraint = "inverse_value[1] = 99"
    elif binding == "let-constant-not":
        constraint = f"let {{ int: inverse_value = {inverse}; }} in not (inverse_value = 1)"
    else:
        constraint = (
            f"let {{ int: inverse_value = {inverse} default 99; }} "
            "in inverse_value = 99"
        )
    result = _translate(f"""
enum Product = {domain} ++ {{Outside}};
{declaration}
constraint {constraint};
solve satisfy;
""")
    if expected == "error":
        assert not result.ok
        assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)
    else:
        _assert_solver_outcome(result, {"sat": z3.sat, "unsat": z3.unsat}[expected])


def test_empty_constructor_part_does_not_shift_later_constructor_ordinals():
    result = _translate("""
enum E = Empty({}) ++ Next(4..5);
var bool: empty_constructor_set;
var bool: first_next_is_one;
var bool: second_next_is_two;
constraint empty_constructor_set <-> card(Empty()) = 0;
constraint first_next_is_one <-> enum2int(Next(4)) = 1;
constraint second_next_is_two <-> enum2int(Next(5)) = 2;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {
        "empty_constructor_set": True,
        "first_next_is_one": True,
        "second_next_is_two": True,
    })


def test_entirely_empty_constructed_enum_can_index_an_empty_array():
    result = _translate("""
enum E = Empty({});
array[E] of int: values = [];
var bool: enum_and_array_are_empty;
constraint enum_and_array_are_empty <-> card(E) = 0;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {"enum_and_array_are_empty": True})


@pytest.mark.parametrize("source", [
    "array[1..0] of int: values = [||]; solve satisfy;",
    "array[1..2, 1..0] of int: values = [|||]; solve satisfy;",
])
def test_empty_matrix_rank_or_row_count_mismatch_is_rejected(source):
    result = _translate(source)
    assert not result.ok
    assert all("E_INTERNAL" not in str(diagnostic.code) for diagnostic in result.diagnostic_items)


def test_explicit_two_dimensional_empty_matrix_literal_is_accepted():
    result = _translate("""
array[1..0, 1..0] of int: values = [||];
solve satisfy;
""")
    _assert_solver_outcome(result, z3.sat)


def test_empty_nominal_row_axis_with_named_column_header_is_accepted():
    result = _translate("""
enum Row = {};
enum Col = {Col0};
array[Row, Col] of int: values = [| Col0: |];
var bool: nominal_row_axis_is_empty;
constraint nominal_row_axis_is_empty <-> card(Row) = 0;
solve satisfy;
""")
    _assert_forced_boolean_values(result, {"nominal_row_axis_is_empty": True})
