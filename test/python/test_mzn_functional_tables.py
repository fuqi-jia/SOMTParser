"""Functional tables retain their exact finite relation, not default values."""
import itertools

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _emit(rows, *, boolean=False, negate=False, computed=False):
    count = len(rows[0])
    rows = (rows * ((128 + len(rows) - 1) // len(rows)))[:128]
    payload = ",".join(str(value).lower() for row in rows for value in row)
    typ = "bool" if boolean else "int"
    names = [f"x{column}" for column in range(count)]
    declarations = "\n".join(f"var {typ}: {name};" for name in names)
    if computed:
        declaration = f"array[1..{len(rows) * count}] of {typ}: raw = [{payload}];"
        table = f"array2d(1..{len(rows)},1..{count},[raw[i] | i in index_set(raw)])"
    else:
        declaration = f"array[1..{len(rows)},1..{count}] of {typ}: t = array2d(1..{len(rows)},1..{count},[{payload}]);"
        table = "t"
    result = sp.translate(language="minizinc", source=f"""
        {declarations}
        {declaration}
        constraint {'not ' if negate else ''}table([{','.join(names)}], {table});
        solve satisfy;
    """)
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    target = result.to_smt2(sp.OmtDialect.Z3)
    actual = z3.And(*z3.parse_smt2_string(target))
    variables = [z3.Bool(name) if boolean else z3.Int(name) for name in names]
    expected = z3.Or(*[z3.And(*[variable == value for variable, value in zip(variables, row)]) for row in rows])
    if negate:
        expected = z3.Not(expected)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat, target
    return target


@pytest.mark.parametrize("computed", [False, True])
@pytest.mark.parametrize("negate", [False, True])
@pytest.mark.parametrize("rows", [
    # Includes zero as a real output: absent keys must not inherit zero.
    [(0, -7, 2), (-5, 0, 3), (7, -7, 3)],
    # Repeated equal keys preserve a function; repeated conflicting keys do not.
    [(2, 3), (2, 3), (-1, 0)],
    [(2, 3), (-5, 3), (0, -7)],
    # Signed 64-bit boundary outputs and keys must not be narrowed.
    [(-(2**63), 2**63-1), (2**63-1, -(2**63))],
])
def test_integer_tables_equal_explicit_relation(rows, negate, computed):
    _emit(rows, negate=negate, computed=computed)


@pytest.mark.parametrize("computed", [False, True])
@pytest.mark.parametrize("negate", [False, True])
@pytest.mark.parametrize("rows", [
    [(False, False, True), (True, True, False)],
    [(False, False), (True, False)],
])
def test_boolean_tables_equal_explicit_relation(rows, negate, computed):
    _emit(rows, boolean=True, negate=negate, computed=computed)


def test_functional_cost_table_has_linear_nested_array_size():
    rows = [(x * 17 - y * 3, x, y) for x, y in itertools.product(range(16), range(8))]
    target = _emit(rows)
    # A value array per x, a root array, and shared finite domain arrays.
    assert target.count("define-fun") <= 20


@pytest.mark.parametrize("negate", [False, True])
@pytest.mark.parametrize("partial_column", [0, 1, 2])
def test_partial_function_tuple_closes_at_predicate_boundary(negate, partial_column):
    values = ["0", "3", "4"]
    values[partial_column] = "1 div 0"
    payload = ",".join(["0", "3", "4"] * 128)
    result = sp.translate(language="minizinc", source=f"""
        array[1..128,1..3] of int:t=array2d(1..128,1..3,[{payload}]);
        constraint {'not ' if negate else ''}table([{','.join(values)}],t);
        solve satisfy;
    """)
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == (z3.sat if negate else z3.unsat)


@pytest.mark.parametrize("value", [0, -13])
def test_repeated_cost_is_shared_without_admitting_absent_keys(value):
    target = _emit([(value, key) for key in range(128)])
    # The finite-domain array stores the 128 legal keys. The constant value
    # array needs no stores; arbitrary outside keys still fail equivalence.
    assert target.count("(store ") <= 128
