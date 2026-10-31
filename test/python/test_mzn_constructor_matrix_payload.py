"""Explicit arrayNd constructors reshape matrix payloads in row-major order."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("separate_data", [False, True])
@pytest.mark.parametrize("declaration,constructor,indices", [
    ("array[1..2,0..1] of int: a;", "array2d(1..2,0..1,", ["1,0", "1,1", "2,0", "2,1"]),
    ("array[1..1,0..3] of int: a;", "array2d(1..1,0..3,", ["1,0", "1,1", "1,2", "1,3"]),
    ("array[-2..1] of int: a;", "array1d(-2..1,", ["-2", "-1", "0", "1"]),
    ("set of int: R=3..4; set of int: C=-1..0; array[R,C] of int: a;",
     "array2d(R,C,", ["3,-1", "3,0", "4,-1", "4,0"]),
])
def test_constructor_axes_replace_matrix_payload_axes(
        tmp_path, separate_data, declaration, constructor, indices):
    assignment = "a=" + constructor + "[|11,12|21,22|]);\n"
    observations = "array[1..4] of var int: output_values;\n" + "\n".join(
        f"constraint output_values[{i}] = a[{index}];"
        for i, index in enumerate(indices, 1))
    source = declaration + "\n" + observations + "\nsolve satisfy;\n"
    data = []
    if separate_data:
        path = tmp_path / "instance.dzn"
        path.write_text(assignment)
        data.append(str(path))
    else:
        source += assignment
    result = sp.translate(source=source, language="minizinc", data=data)
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    values = z3.Array("output_values", z3.IntSort(), z3.IntSort())
    expected = z3.And(*[values[i] == n for i, n in enumerate([11, 12, 21, 22], 1)])
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("assignment,reason", [
    ("a=array2d(1..2,1..2,[|11,12|21,22|]);", "different index set"),
    ("a=array2d(1..2,0..1,[|11,12|]);", "element(s)"),
    ("a=array2d(1..2,0..1,[|11,12|21|]);", "ragged"),
    ("a=[|11,12|21,22|];", "different index set"),
])
def test_constructor_keeps_shape_and_literal_validation(tmp_path, assignment, reason):
    path = tmp_path / "instance.dzn"
    path.write_text(assignment)
    result = sp.translate(source="array[1..2,0..1] of int: a; solve satisfy;",
                          language="minizinc", data=[str(path)])
    assert not result.ok
    assert any(reason in d.message for d in result.diagnostic_items)
