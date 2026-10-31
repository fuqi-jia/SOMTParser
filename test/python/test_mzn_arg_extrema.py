"""MiniZinc finite-array semantics, checked against the 2.9.4 reference compiler."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

_CASES = [('arg_max-ties', 'include "arg_max.mzn";constraint arg_max([4,9,9])=2; solve satisfy;', 'sat'),
 ('arg_max-wrong-tie',
  'include "arg_max.mzn";constraint arg_max([4,9,9])=3; solve satisfy;',
  'unsat'),
 ('arg_max-shifted',
  'include "arg_max.mzn";array[-2..0] of int:a=array1d(-2..0,[4,9,9]);constraint arg_max(a)=-1; '
  'solve satisfy;',
  'sat'),
 ('arg_max-enum',
  'include "arg_max.mzn";enum E={A,B,C};array[E] of var -9..9:a;constraint a[A]=4 /\\ a[B]=9 /\\ '
  'a[C]=9 /\\ arg_max(a)=B; solve satisfy;',
  'sat'),
 ('arg_max-real',
  'include "arg_max.mzn";constraint arg_max([4.0,9.5,9.5])=2; solve satisfy;',
  'sat'),
 ('arg_max-bool',
  'include "arg_max.mzn";constraint arg_max([false,true,false])=2; solve satisfy;',
  'sat'),
 ('arg_max-generator-bool',
  'include "arg_max.mzn";constraint arg_max(i in 1..3)(i=2)=2; solve satisfy;',
  'sat'),
 ('arg_max-empty',
  'include "arg_max.mzn";array[1..0] of var int:a=[];constraint arg_max(a)=1; solve satisfy;',
  'unsat'),
 ('arg_max-empty-negated',
  'include "arg_max.mzn";array[1..0] of var int:a=[];constraint not(arg_max(a)=1); solve satisfy;',
  'sat'),
 ('arg_max-partial',
  'include "arg_max.mzn";var 0..0:d;constraint arg_max([1 div d,2])=1; solve satisfy;',
  'unsat'),
 ('arg_max-partial-negated',
  'include "arg_max.mzn";var 0..0:d;constraint not(arg_max([1 div d,2])=1); solve satisfy;',
  'sat'),
 ('arg_max-bool-partial',
  'include "arg_max.mzn";var 0..0:d;constraint arg_max([(1 div d)=0,true])=2; solve satisfy;',
  'sat'),
 ('arg_max-generator-fixed-filter',
  'include "arg_max.mzn";constraint arg_max(i in 3..5 where i>3)(i)=2; solve satisfy;',
  'sat'),
 ('arg_max-generator-dynamic-filter',
  'include "arg_max.mzn";var 4..4:k;constraint arg_max(i in 3..5 where i>=k)(i)=3; solve satisfy;',
  'sat'),
 ('arg_max-equivalence',
  'include "arg_max.mzn";array[1..3] of var -2..2:x;constraint exists(k in '
  '1..3)(not((arg_max(x)=k) <-> (forall(i in 1..k-1)(x[k]>x[i]) /\\ forall(i in '
  'k+1..3)(x[k]>=x[i])))); solve satisfy;',
  'unsat'),
 ('arg_max-rank',
  'include "arg_max.mzn";array[1..1,1..2] of var 0..2:x;constraint arg_max(x)=1; solve satisfy;',
  'reject'),
 ('arg_min-ties', 'include "arg_min.mzn";constraint arg_min([4,-9,-9])=2; solve satisfy;', 'sat'),
 ('arg_min-wrong-tie',
  'include "arg_min.mzn";constraint arg_min([4,-9,-9])=3; solve satisfy;',
  'unsat'),
 ('arg_min-shifted',
  'include "arg_min.mzn";array[-2..0] of int:a=array1d(-2..0,[4,-9,-9]);constraint arg_min(a)=-1; '
  'solve satisfy;',
  'sat'),
 ('arg_min-enum',
  'include "arg_min.mzn";enum E={A,B,C};array[E] of var -9..9:a;constraint a[A]=4 /\\ a[B]=-9 /\\ '
  'a[C]=-9 /\\ arg_min(a)=B; solve satisfy;',
  'sat'),
 ('arg_min-real',
  'include "arg_min.mzn";constraint arg_min([4.0,-9.5,-9.5])=2; solve satisfy;',
  'sat'),
 ('arg_min-bool',
  'include "arg_min.mzn";constraint arg_min([false,true,false])=1; solve satisfy;',
  'sat'),
 ('arg_min-generator-bool',
  'include "arg_min.mzn";constraint arg_min(i in 1..3)(i=2)=1; solve satisfy;',
  'sat'),
 ('arg_min-empty',
  'include "arg_min.mzn";array[1..0] of var int:a=[];constraint arg_min(a)=1; solve satisfy;',
  'unsat'),
 ('arg_min-empty-negated',
  'include "arg_min.mzn";array[1..0] of var int:a=[];constraint not(arg_min(a)=1); solve satisfy;',
  'sat'),
 ('arg_min-partial',
  'include "arg_min.mzn";var 0..0:d;constraint arg_min([1 div d,2])=1; solve satisfy;',
  'unsat'),
 ('arg_min-partial-negated',
  'include "arg_min.mzn";var 0..0:d;constraint not(arg_min([1 div d,2])=1); solve satisfy;',
  'sat'),
 ('arg_min-bool-partial',
  'include "arg_min.mzn";var 0..0:d;constraint arg_min([(1 div d)=0,true])=1; solve satisfy;',
  'sat'),
 ('arg_min-generator-fixed-filter',
  'include "arg_min.mzn";constraint arg_min(i in 3..5 where i>3)(i)=1; solve satisfy;',
  'sat'),
 ('arg_min-generator-dynamic-filter',
  'include "arg_min.mzn";var 4..4:k;constraint arg_min(i in 3..5 where i>=k)(i)=2; solve satisfy;',
  'sat'),
 ('arg_min-equivalence',
  'include "arg_min.mzn";array[1..3] of var -2..2:x;constraint exists(k in '
  '1..3)(not((arg_min(x)=k) <-> (forall(i in 1..k-1)(x[k]<x[i]) /\\ forall(i in '
  'k+1..3)(x[k]<=x[i])))); solve satisfy;',
  'unsat'),
 ('arg_min-rank',
  'include "arg_min.mzn";array[1..1,1..2] of var 0..2:x;constraint arg_min(x)=1; solve satisfy;',
  'reject')]


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
