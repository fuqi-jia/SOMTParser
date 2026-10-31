"""Clause-local CNF variable sharing preserves quantification and signatures."""

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("source,expected", [
    ("cnf(a,axiom,p(X)). cnf(b,axiom,~p(a)).", z3.unsat),
    ("cnf(a,axiom,p(X,X)). cnf(b,axiom,a != b). "
     "cnf(c,axiom,~p(a,b)).", z3.sat),
    ("cnf(a,axiom,p(X,a)). cnf(b,axiom,~p(b,X)).", z3.unsat),
    ("cnf(a,axiom,(~p(X,X) | q(X))). "
     "cnf(b,axiom,p(a,a)). cnf(c,axiom,~q(a)).", z3.unsat),
])
def test_reused_cnf_variables_have_clause_local_meaning(source, expected):
    result = sp.translate(source=source, language="tptp")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3), ctx=context))
    assert solver.check() == expected
