"""Deep-source and numeric-context regressions; run on the execution host."""
import somtparser as sp
import pytest
import z3


@pytest.mark.parametrize('term', [
    '(ite p 0 r)', '(ite p r 0)', '(ite p i r)',
    '(ite p 0 (ite q 1 r))', '(ite p (ite q 0 1) r)',
])
def test_ite_numeric_context_preserves_assertions(term):
    source = '(set-logic QF_LIRA)(declare-const p Bool)(declare-const q Bool)(declare-const r Real)(declare-const i Int)(assert (= r (/ 3 2)))(assert (= ' + term + ' r))(check-sat)'
    translated = sp.translate(source=source, language='smtlib2', dialect=sp.OmtDialect.Z3)
    assert translated.ok, [(str(d.code), d.message) for d in translated.diagnostic_items]
    converted = translated.to_smt2(sp.OmtDialect.Z3)
    context = z3.Context()
    left = z3.And(*z3.parse_smt2_string(source, ctx=context))
    right = z3.And(*z3.parse_smt2_string(converted, ctx=context))
    solver = z3.Solver(ctx=context)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat
    assert len(sp.parse(converted).assertions) == 2


def test_deep_boolean_lift_does_not_overflow_native_stack():
    depth = 12000
    source = '(set-logic QF_UF)(declare-const p Bool)(declare-const q Bool)(assert ' + '(ite p ' * depth + 'p' + ' q)' * depth + ')(check-sat)'
    translated = sp.translate(source=source, language='smtlib2', dialect=sp.OmtDialect.Z3)
    assert translated.ok, [(str(d.code), d.message) for d in translated.diagnostic_items]
    converted = translated.to_smt2(sp.OmtDialect.Z3)
    assert len(sp.parse(converted).assertions) == 1
