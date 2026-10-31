"""MiniZinc standard operators: enum domains, precedence, and name resolution."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

_CASES = [('enum-par-good', 'enum E={A,B,C}; constraint to_enum(E,2)=B; solve satisfy;', 'sat'),
 ('enum-par-subset-hole', 'enum E={A,B,C}; constraint to_enum({A,C},2)=B; solve satisfy;', 'unsat'),
 ('enum-var-subset-hole',
  'enum E={A,B,C}; var 2..2:x; constraint to_enum({A,C},x)=B; solve satisfy;',
  'unsat'),
 ('enum-par-zero-negative',
  'enum E={A,B,C}; constraint not(to_enum(E,0)=B); solve satisfy;',
  'sat'),
 ('enum-var-zero-negative',
  'enum E={A,B,C}; var 0..0:x; constraint not(to_enum(E,x)=B); solve satisfy;',
  'sat'),
 ('enum-var-zero-positive',
  'enum E={A,B,C}; var 0..0:x; constraint to_enum(E,x)=B; solve satisfy;',
  'unsat'),
 ('enum-int-target', 'constraint to_enum(1..3,2)=2; solve satisfy;', 'sat'),
 ('enum-bool', 'enum E={A,B}; constraint to_enum(E,true)=A; solve satisfy;', 'sat'),
 ('enum-other-enum',
  'enum E={A,B}; enum F={C,D}; constraint to_enum(E,D)=B; solve satisfy;',
  'sat'),
 ('chain-negative',
  'include "seq_precede_chain.mzn"; constraint seq_precede_chain([-2,0,1,0,2,3]); solve satisfy;',
  'sat'),
 ('chain-first-two',
  'include "seq_precede_chain.mzn"; constraint seq_precede_chain([2,1]); solve satisfy;',
  'unsat'),
 ('chain-bool',
  'include "seq_precede_chain.mzn"; constraint seq_precede_chain([true,false]); solve satisfy;',
  'sat'),
 ('chain-empty',
  'include "seq_precede_chain.mzn"; constraint seq_precede_chain([]); solve satisfy;',
  'sat'),
 ('chain-div-positive',
  'include "seq_precede_chain.mzn"; var 0..0:d; constraint seq_precede_chain([1 div d]); solve '
  'satisfy;',
  'unsat'),
 ('chain-div-negative',
  'include "seq_precede_chain.mzn"; var 0..0:d; constraint not seq_precede_chain([1 div d]); solve '
  'satisfy;',
  'sat'),
 ('enum-casts-retain-original-type',
  'enum E={A,B};enum F={C,D};var 1..2:x;constraint to_enum(E,x)=A /\\ to_enum(F,x)=C /\\ x=1;solve '
  'satisfy;',
  'sat'),
 ('enum-array-preserves-indices',
  'enum E={A,B};array[-1..0] of var 1..2:x;array[-1..0] of var E:y=to_enum(E,x);constraint y[-1]=A '
  '/\\ y[0]=B /\\ x[-1]=1 /\\ x[0]=2;solve satisfy;',
  'sat'),
 ('enum-array-preserves-matrix',
  'enum E={A,B};array[-1..0,4..5] of var 1..2:x;array[-1..0,4..5] of var '
  'E:y=to_enum(E,x);constraint y[-1,4]=A /\\ x[-1,4]=2;solve satisfy;',
  'unsat'),
 ('enum-array-subset-hole',
  'enum E={A,B,C};array[1..2] of var 2..2:x;array[1..2] of var E:y=to_enum({A,C},x);solve satisfy;',
  'unsat'),
 ('chain-reified-equivalence',
  'include "seq_precede_chain.mzn";array[-2..1] of var -2..4:x;constraint not '
  '(seq_precede_chain(x) <-> forall(j in -2..1,v in 2..4)(x[j]=v -> exists(i in '
  '-2..j-1)(x[i]=v-1)));solve satisfy;',
  'unsat'),
 ('chain-rank-error',
  'include "seq_precede_chain.mzn";array[1..2,1..2] of var 0..2:x;constraint '
  'seq_precede_chain(x);solve satisfy;',
  'reject'),
 ('builtin-array-name-product',
  'array[1..2] of int:product=[1,2];constraint forall(i in 1..2)(product[i]=i);solve satisfy;',
  'sat'),
 ('builtin-array-name-sum',
  'array[1..2] of int:sum=[1,2];constraint forall(i in 1..2)(sum[i]=i);solve satisfy;',
  'sat'),
 ('builtin-array-name-length',
  'array[1..2] of int:length=[1,2];constraint forall(i in 1..2)(length[i]=i);solve satisfy;',
  'sat'),
 ('builtin-array-name-max',
  'array[1..2] of int:max=[1,2];constraint forall(i in 1..2)(max[i]=i);solve satisfy;',
  'sat'),
 ('builtin-array-name-count',
  'array[1..2] of int:count=[1,2];constraint forall(i in 1..2)(count[i]=i);solve satisfy;',
  'sat'),
 ('builtin-scalar-name', 'int:product=3;int:sum=2;constraint product+sum=5;solve satisfy;', 'sat')]


@pytest.mark.parametrize("name,source,expected", _CASES, ids=[r[0] for r in _CASES])
def test_standard_operator_semantics(name, source, expected):
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
