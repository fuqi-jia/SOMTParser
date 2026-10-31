"""MiniZinc finite-array semantics, checked against the 2.9.4 reference compiler."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

_CASES = [('array-different-bounds',
  'array[0..1] of int:a=array1d(0..1,[1,2]);array[1..2] of int:b=[1,2];constraint a=b;solve '
  'satisfy;',
  'reject'),
 ('array-different-length', 'constraint [1,2]=[1];solve satisfy;', 'reject'),
 ('array-different-rank',
  'array[1..2,1..2] of int:a=[|1,2|3,4|];constraint a=[1,2,3,4];solve satisfy;',
  'reject'),
 ('array-matrix-different-shape',
  'array[1..2,1..2] of int:a=[|1,2|3,4|];array[1..1,1..4] of '
  'int:b=array2d(1..1,1..4,[1,2,3,4]);constraint a=b;solve satisfy;',
  'reject'),
 ('array-enum-literal',
  'enum E={A,B};array[E] of int:a=[1,2];constraint a=[1,2];solve satisfy;',
  'sat'),
 ('array-empty-equal', 'array[1..0] of int:a=[];constraint a=[];solve satisfy;', 'sat'),
 ('array-partial-eq', 'var 0..0:d;constraint [1 div d]=[0];solve satisfy;', 'unsat'),
 ('array-partial-ne', 'var 0..0:d;constraint [1 div d]!=[0];solve satisfy;', 'unsat'),
 ('array-partial-not-eq', 'var 0..0:d;constraint not ([1 div d]=[0]);solve satisfy;', 'sat'),
 ('array-bool-partial', 'var 0..0:d;constraint [(1 div d)=0]=[false];solve satisfy;', 'sat'),
 ('array-bool-int', 'constraint [true]=[1];solve satisfy;', 'sat'),
 ('array-array-lt', 'constraint [1,2]<[1,3];solve satisfy;', 'sat'),
 ('array-array-lt-prefix', 'constraint [1,2]<[1,2,3];solve satisfy;', 'reject'),
 ('array-enum-axis-mismatch',
  'enum E={A,B};enum F={C,D};array[E] of int:a=[1,2];array[F] of int:b=[1,2];constraint a=b; solve '
  'satisfy;',
  'sat'),
 ('array-enum-cell-mismatch',
  'enum E={A,B};enum F={C,D};constraint [A,B]=[C,D]; solve satisfy;',
  'reject'),
 ('array-formal-comparison',
  'predicate p(array[int] of var int:a,array[int] of var int:b)=a=b;array[1..2] of var '
  '0..2:x;constraint p(x,[1,2]) /\\ x[1]=0; solve satisfy;',
  'unsat'),
 ('array-formal-slice',
  'predicate p(array[int,int] of var int:a)=a[1,..]=[1,2];array[1..2,1..2] of var '
  '0..2:x;constraint p(x) /\\ x[1,1]=0; solve satisfy;',
  'unsat'),
 ('array-slice-symbolic',
  'array[1..2,1..2] of var 0..2:x;var 1..2:i;constraint x[i,..]=[1,2] /\\ x[i,1]=0; solve satisfy;',
  'reject'),
 ('array-slice-bad-negative',
  'array[1..2,1..2] of var 0..2:x;var 0..0:i;constraint not(x[i,..]=[1,2]); solve satisfy;',
  'reject'),
 ('array-slice-bad-positive',
  'array[1..2,1..2] of var 0..2:x;var 0..0:i;constraint x[i,..]=[1,2]; solve satisfy;',
  'reject'),
 ('array-eq-equivalence',
  'array[1..3] of var 0..2:x;array[1..3] of var 0..2:y;constraint not((x=y) <-> forall(i in '
  '1..3)(x[i]=y[i])); solve satisfy;',
  'unsat'),
 ('array-ne-equivalence',
  'array[1..3] of var 0..2:x;array[1..3] of var 0..2:y;constraint not((x!=y) <-> exists(i in '
  '1..3)(x[i]!=y[i])); solve satisfy;',
  'unsat'),
 ('array-lt-equivalence',
  'array[1..3] of var 0..2:x;array[1..3] of var 0..2:y;constraint not((x<y) <-> exists(i in '
  '1..3)(x[i]<y[i] /\\ forall(j in 1..i-1)(x[j]=y[j]))); solve satisfy;',
  'unsat'),
 ('array-le-equal', 'constraint [1,2]<=[1,2]; solve satisfy;', 'sat'),
 ('array-ge-equal', 'constraint [1,2]>=[1,2]; solve satisfy;', 'sat'),
 ('array-gt-equal', 'constraint [1,2]>[1,2]; solve satisfy;', 'unsat'),
 ('array-empty-lt', 'constraint []<[]; solve satisfy;', 'unsat'),
 ('array-real-coercion', 'constraint [1,2]=[1.0,2.0]; solve satisfy;', 'sat'),
 ('array-string-eq', 'constraint ["a","b"]=["a","b"]; solve satisfy;', 'sat'),
 ('array-string-ne', 'constraint ["a","b"]!=["a","b"]; solve satisfy;', 'unsat')]


@pytest.mark.parametrize("name,source,expected", _CASES, ids=[r[0] for r in _CASES])
def test_reference_semantics(name, source, expected):
    result = sp.translate(source=source, language="minizinc")
    if expected == "reject":
        assert not result.ok
        return
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=context))
    assert str(solver.check()) == expected, solver.reason_unknown()
