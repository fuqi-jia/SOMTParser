"""Typed parameter arrays precede evaluation of their dependent constants."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def solve(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=context))
    return str(solver.check())


@pytest.mark.parametrize("array_first", [False, True])
@pytest.mark.parametrize("value,expected", [(0, "unsat"), (1, "sat"), (2, "sat")])
def test_forward_test_uses_typed_array_values(array_first, value, expected):
    # Independently checked with MiniZinc 2.9.4 + Gecode in both item orders.
    array = "array[M] of int:w=array1d(M,[1,2,3]);"
    declarations = "set of M:D;var M:x;constraint x in D;"
    source = "set of int:M=0..2;" + (
        array + declarations if array_first else declarations + array
    )
    source += "test keep(int:i)=w[i]>1;D={i|i in M where keep(i)};"
    source += f"constraint x={value};solve satisfy;"
    assert solve(sp.translate(source=source, language="minizinc")) == expected


def test_deferred_data_constructor_does_not_invent_one_based_indices(tmp_path):
    source = tmp_path / "model.mzn"
    data = tmp_path / "instance.dzn"
    source.write_text(
        "set of int:IDX;IDX=index_set(A);int:first_idx=min(IDX);"
        "array[ROW] of int:A;set of int:ROW;ROW=5..6;"
        "constraint first_idx=5;solve satisfy;"
    )
    data.write_text("A=array1d(ROW,[10,20]);")
    assert solve(sp.translate(str(source), language="minizinc", data=[str(data)])) == "sat"


def test_forward_cell_read_waits_for_deferred_constructor_indices(tmp_path):
    source = tmp_path / "model.mzn"
    data = tmp_path / "instance.dzn"
    source.write_text(
        "set of int:ROW;int:v=A[1];array[ROW] of int:A;ROW=0..1;"
        "constraint v=20;solve satisfy;"
    )
    data.write_text("A=array1d(ROW,[10,20]);")
    assert solve(sp.translate(str(source), language="minizinc", data=[str(data)])) == "sat"


@pytest.mark.parametrize("source", [
    "array[1..2] of int:A=[1,2];array[1..2] of int:A=[3,4];solve satisfy;",
    "array[0..2] of int:A=[1,2];solve satisfy;",
    "array[1..1] of int:A=[B[1]];array[1..1] of int:B=[A[1]];solve satisfy;",
])
def test_invalid_or_cyclic_array_declarations_remain_errors(source):
    assert not sp.translate(source=source, language="minizinc").ok
