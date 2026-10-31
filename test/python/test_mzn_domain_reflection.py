"""Static domain reflection retains the argument's relational definedness."""

import pytest
import z3

import somtparser as sp


@pytest.mark.parametrize("source,expected", [
    ("var -2..4:x; constraint not(x in dom(x));", z3.unsat),
    ("var {1,3}:x; constraint not(x in dom(x));", z3.unsat),
    ("var {1,3}:x; constraint x=2; constraint x in dom(x);", z3.unsat),
    ("array[1..2]of var 1..3:x; constraint forall(j in index_set(x))"
     "(x[j] in dom(x[j]));", z3.sat),
    ("var 1..4:x; constraint let{var int:y=x;}in not(x in dom(y));", z3.unsat),
    ("function set of int: reflected(var int:z)=dom(z); var 1..4:x;"
     " constraint not(x in reflected(x));", z3.unsat),
    ("var 1..3:x; constraint not(2*x+1 in dom(2*x+1));", z3.unsat),
    ("enum E={a,b,c}; var E:x; constraint dom(x)=E;", z3.sat),
    ("array[1..2]of var 1..3:x;var 0..3:i; constraint i=0;"
     " constraint card(dom(x[i]))=3;", z3.unsat),
    ("array[1..2]of var 1..3:x;var 0..3:i; constraint i=1;"
     " constraint card(dom(x[i]))=3;", z3.sat),
    ("var 0..0:d; constraint 0 in dom(1 div d);", z3.unsat),
    ("var -7..8:x;var -3..3:d;constraint d!=0;"
     " constraint not(x div d in dom(x div d));", z3.unsat),
    ("var -7..8:x;var -3..3:d;constraint d!=0;"
     " constraint not(x mod d in dom(x mod d));", z3.unsat),
    ("var 1..3:x; constraint sum(i in dom(x))(i)=6;", z3.sat),
    ("var 1..3:x;set of int:D=dom(x);constraint not(x in D);", z3.unsat),
    ("function set of int:f(var int:z)=dom(z);var 1..2:a;var 7..9:b;"
     "constraint f(a)=1..2 /\\ f(b)=7..9;", z3.sat),
    ("function set of int:f(var int:z)=dom(z+1);"
     "function set of int:g(var int:y)=f(y);var 1..2:x;"
     "constraint g(x)=2..3;", z3.sat),
    ("function set of int:f(array[int]of var int:z)=dom(z[1]);"
     "array[1..2]of var 1..4:x;constraint not(x[1] in f(x));", z3.unsat),
])
def test_domain_reflection_matches_minizinc_294_oracles(source, expected):
    translated = sp.translate(source=source + " solve satisfy;", language="minizinc")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.from_string(translated.to_smt2(sp.OmtDialect.Z3))
    assert solver.check() == expected


def test_ihtc_domain_filter_in_polymorphic_array_predicate():
    # This is the filtering pattern in the official iHTC cumulatives predicate.
    source = """
predicate members(array[$$E]of var int:x) =
  forall(i in 1..3)(
    let {set of int:J = {j | j in index_set(x) where i in dom(x[j])}}
    in forall(j in J)(x[j] != i));
array[1..2]of var 1..3:x;
constraint members(x);
solve satisfy;
"""
    translated = sp.translate(source=source, language="minizinc")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.from_string(translated.to_smt2(sp.OmtDialect.Z3))
    assert solver.check() == z3.unsat


def test_unbounded_domain_does_not_invent_machine_integer_limits():
    translated = sp.translate(
        source="var int:x; constraint x in dom(x); solve satisfy;", language="minizinc")
    assert not translated.ok
    assert any("no proven finite integer bounds" in d.message for d in translated.diagnostic_items)
