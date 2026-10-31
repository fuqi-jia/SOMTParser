"""Indexed array literal layout and partiality, checked against MiniZinc 2.9.4."""
import pytest
import somtparser as sp
import z3


CASES = [('explicit', 'array[2..4]of var int:a=[4:30,2:10,3:20];constraint a[2]=10 /\\ a[3]=20 /\\ a[4]=30;solve satisfy;', 'sat'), ('start_only', 'array[2..4]of var int:a=[2:10,20,30];constraint a[2]=10 /\\ a[3]=20 /\\ a[4]=30;solve satisfy;', 'sat'), ('mixed', 'array[2..4]of var int:a=[2:10,20,4:30];solve satisfy;', 'reject'), ('mixed2', 'array[2..4]of var int:a=[2:10,3:20,30];solve satisfy;', 'reject'), ('enum', 'enum E={a,b,c};array[E]of var int:x=[c:30,a:10,b:20];constraint x[a]=10 /\\ x[b]=20 /\\ x[c]=30;solve satisfy;', 'sat'), ('enum_start', 'enum E={a,b,c};array[E]of var int:x=[a:10,20,30];constraint x[c]=30;solve satisfy;', 'sat'), ('enum_outside', 'enum E={a,b};array[int]of var int:x=[a:10,20,30];solve satisfy;', 'unsat'), ('matrix', 'array[2..3,4..5]of var int:x=[(3,5):4,(2,4):1,(3,4):3,(2,5):2];constraint x[3,4]=3;solve satisfy;', 'sat'), ('hole', 'array[2..3]of var int:x=[2:_,3:4];constraint x[2]=1;solve satisfy;', 'sat'), ('mixed_enum', 'enum E={a,b};enum F={c,d};array[int]of var int:x=[a:1,d:2];solve satisfy;', 'sat')]


@pytest.mark.parametrize("name,source,expected", CASES, ids=[r[0] for r in CASES])
def test_reference_outcomes(name, source, expected):
    result = sp.translate(source=source, language="minizinc")
    if expected == "reject":
        assert not result.ok
        assert any("mixing indexed and non-indexed" in d.message for d in result.diagnostic_items)
        return
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert str(solver.check()) == expected


@pytest.mark.parametrize("literal", ["[4:r,2:p,3:q]", "[2:p,q,r]"])
def test_literal_assignment_is_exact_for_all_element_values(literal):
    source = f"var int:p;var int:q;var int:r;array[2..4] of var int:x={literal};solve satisfy;"
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    p, q, r = z3.Ints("p q r")
    expected = z3.And(x[2] == p, x[3] == q, x[4] == r)
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("literal", ["[2:10,2:20]", "[2:10,4:20]",
                                      "[(1,1):0,(1,3):1,(2,1):0,(2,3):2]",
                                      "[(1,1):0,2:1]"])
def test_invalid_index_layout_is_rejected(literal):
    result = sp.translate(source=f"array[int] of var int:x={literal};solve satisfy;",
                          language="minizinc")
    assert not result.ok
    assert any("duplicate" in d.message or "rectangular" in d.message or
               "inconsistent ranks" in d.message for d in result.diagnostic_items)
