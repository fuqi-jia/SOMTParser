"""Shared constant tables preserve each read's values, indices and scope."""
import pytest
import z3
import somtparser as sp


def formula(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


@pytest.mark.parametrize("kind,cells,values,zsort", [
    ("int", "7, 11, -2, 7", [7, 11, -2, 7], z3.IntSort()),
    ("float", "0.5, 1.25, -2.5, 0.5",
     [z3.RealVal("1/2"), z3.RealVal("5/4"), z3.RealVal("-5/2"), z3.RealVal("1/2")], z3.RealSort()),
    ("bool", "false, true, true, false", [False, True, True, False], z3.BoolSort()),
    ("string", '"a", "ab", "c", "a"',
     [z3.StringVal(v) for v in ["a", "ab", "c", "a"]], z3.StringSort()),
])
def test_matrix_lookup_matches_all_values_and_per_dimension_definedness(kind, cells, values, zsort):
    value_decl = 'string: value = "a";' if kind == "string" else f"var {kind}: value;"
    actual = formula(f'''
array[-1..0, 3..4] of {kind}: table = array2d(-1..0, 3..4, [{cells}]);
var int: row; var int: column; {value_decl}
var bool: accepted;
constraint accepted = (table[row, column] = value);
solve satisfy;
''')
    row, column = z3.Ints("row column")
    value = z3.StringVal("a") if kind == "string" else z3.Const("value", zsort)
    relation = z3.Or(*[z3.And(row == -1 + i // 2, column == 3 + i % 2, value == v)
                       for i, v in enumerate(values)])
    expected = z3.Bool("accepted") == relation
    check = z3.Solver()
    check.set(timeout=10000)
    check.add(z3.Xor(actual, expected))
    assert check.check() == z3.unsat


def test_repeated_table_names_and_distinct_string_contents_do_not_alias():
    source = '''
array[1..2] of string: left = ["a", "bc"];
array[1..2] of string: right = ["ab", "c"];
var 1..2: i;
constraint left[i] != right[i];
solve satisfy;
'''
    solver = z3.Solver()
    solver.add(formula(source))
    for i in [1, 2]:
        solver.push()
        solver.add(z3.Int("i") == i)
        assert solver.check() == z3.sat
        solver.pop()


def test_dynamic_enum_table_retains_its_nominal_type():
    source = '''
enum Color = {Red, Blue};
array[1..2] of Color: palette = [Red, Blue];
var 1..2: i;
constraint palette[i] = Blue;
solve satisfy;
'''
    solver = z3.Solver()
    solver.add(formula(source), z3.Int("i") != 2)
    assert solver.check() == z3.unsat


def test_local_parameter_table_name_can_bind_different_contents():
    source = '''
function var int: lookup(int: base, var int: index) =
  let {array[1..2] of int: table = [base, base + 1];} in table[index];
var 1..2: i;
constraint lookup(7, i) + 10 = lookup(17, i);
solve satisfy;
'''
    actual = formula(source)
    check = z3.Solver()
    check.add(z3.Xor(actual, z3.And(z3.Int("i") >= 1, z3.Int("i") <= 2)))
    assert check.check() == z3.unsat


def test_fixed_slice_with_holes_elsewhere_stays_exact():
    source = '''
array[1..2, 1..2] of var int: table = array2d(1..2, 1..2, [7, 11, _, 23]);
var 1..2: i;
constraint table[1, i] = 11;
solve satisfy;
'''
    solver = z3.Solver()
    solver.add(formula(source), z3.Int("i") != 2)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("indices", ["i, 4, k", "-1, j, k", "i, j, 6"])
def test_mixed_fixed_axes_keep_row_major_slice_order(indices):
    source = f'''
array[-1..0, 3..4, 5..6] of int: table = array3d(-1..0, 3..4, 5..6, [2,3,5,7,11,13,17,19]);
var int: i; var int: j; var int: k; var int: value;
var bool: accepted;
constraint accepted = (table[{indices}] = value);
solve satisfy;
'''
    actual = formula(source)
    i, j, k, value = z3.Ints("i j k value")
    coords = {"i": i, "j": j, "k": k, "4": z3.IntVal(4), "-1": z3.IntVal(-1), "6": z3.IntVal(6)}
    terms = [coords[x.strip()] for x in indices.split(",")]
    values = [2, 3, 5, 7, 11, 13, 17, 19]
    expected = z3.Bool("accepted") == z3.Or(*[
        z3.And(terms[0] == -1 + n // 4, terms[1] == 3 + (n // 2) % 2,
               terms[2] == 5 + n % 2, value == v) for n, v in enumerate(values)])
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_out_of_range_read_can_use_default_without_caching_its_guard():
    source = '''
array[1..2] of int: table = [7, 11];
var int: i;
constraint (table[i] default 19) = 19;
constraint table[i + 1] = 7;
solve satisfy;
'''
    solver = z3.Solver()
    solver.add(formula(source))
    assert solver.check() == z3.sat
    solver.add(z3.Int("i") != 0)
    assert solver.check() == z3.unsat
