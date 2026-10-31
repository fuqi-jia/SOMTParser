"""Plain integer array cells preserve full expression/type/domain semantics."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _translate(tmp_path, declaration, literal, constraints, data_file):
    if data_file:
        data = tmp_path / "cells.dzn"
        data.write_text("a=" + literal + ";", encoding="utf-8")
        return sp.translate(source=declaration + ";" + constraints + "solve satisfy;",
                            data=[str(data)], language="minizinc")
    return sp.translate(source=declaration + "=" + literal + ";" + constraints + "solve satisfy;",
                        language="minizinc")


def _exact(result, expected):
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("data_file", [False, True])
def test_literals_and_expression_prefixes_keep_exact_values(tmp_path, data_file):
    values = [0, 15, 63, 7, 8, 9, 2, 6, -3, -(2**63), 2**63-1]
    literal = "[0,0xf,0o77,1+2*3,2^3,9 default 1,5 div 2,(6),-3,-0x8000000000000000,9223372036854775807]"
    constraints = "".join(f"var int:x{i}; constraint x{i}=a[{i+1}];" for i in range(len(values)))
    result = _translate(tmp_path, f"array[1..{len(values)}] of int:a", literal, constraints, data_file)
    _exact(result, z3.And(*[z3.Int(f"x{i}") == v for i, v in enumerate(values)]))


@pytest.mark.parametrize("data_file", [False, True])
def test_matrix_bar_delimiters_and_comments_keep_coordinates(tmp_path, data_file):
    literal = "[|1 /* comma follows */,2|3,4 /* bar follows */|]"
    constraints = "var int:x; constraint x=a[1,1]+10*a[1,2]+100*a[2,1]+1000*a[2,2];"
    _exact(_translate(tmp_path, "array[1..2,1..2] of int:a", literal, constraints, data_file),
           z3.Int("x") == 4321)


@pytest.mark.parametrize("data_file", [False, True])
def test_large_literal_keeps_every_cell_after_cache_capacity(tmp_path, data_file):
    values = [(i*17) % 199 for i in range(10001)]
    literal = "[" + ",".join(map(str, values)) + "]"
    constraints = "var int:x; constraint x=sum(i in 1..10001)(i*a[i]);"
    _exact(_translate(tmp_path, "array[1..10001] of int:a", literal, constraints, data_file),
           z3.Int("x") == sum((i+1)*v for i, v in enumerate(values)))


@pytest.mark.parametrize("data_file", [False, True])
@pytest.mark.parametrize("literal,expected", [("[1,2,3]", 6), ("[1,2.5,3]", "13/2")])
def test_real_array_keeps_integer_promotion(tmp_path, data_file, literal, expected):
    _exact(_translate(tmp_path, "array[1..3] of float:a", literal,
                      "var float:x; constraint x=sum(a);", data_file),
           z3.Real("x") == z3.RealVal(expected))


@pytest.mark.parametrize("declaration,literal", [
    ("array[1..2] of bool:a", "[0,1]"),
    ("array[1..2] of string:a", "[1,2]"),
    ("array[1..2] of int:a", "[1,true]"),
    ("array[1..2] of int:a", "[1,9223372036854775808]"),
    ("array[1..2] of int:a", "[1,-9223372036854775809]"),
    ("array[1..2] of int:a", "[1,2 3]"),
    ("array[1..2] of int:a", "[1,2 /* missing closer"),
])
@pytest.mark.parametrize("data_file", [False, True])
def test_fast_cells_do_not_accept_invalid_types_or_tokens(tmp_path, declaration, literal, data_file):
    result = _translate(tmp_path, declaration, literal, "", data_file)
    assert not result.ok
    assert result.diagnostic_items
