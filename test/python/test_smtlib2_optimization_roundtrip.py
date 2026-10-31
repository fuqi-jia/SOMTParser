"""Optimization meaning survives the HIR reader, including exact soft costs."""
from pathlib import Path
import pytest
import z3
import somtparser as sp


def roundtrip(source):
    result = sp.translate(source=source, language='smtlib2', dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result.to_smt2(sp.OmtDialect.Z3)


@pytest.mark.parametrize('term,value', [('0', '0'), ('5', '5'), ('(- 5)', '-5'),
                                        ('2.5', '5/2'), ('(/ 1 2)', '1/2')])
def test_constant_objective_is_numeric_without_a_declared_variable(term, value):
    source = f'(set-logic ALL)(minimize {term})(check-sat)'
    for _ in range(2):
        source = roundtrip(source)
        solver = z3.Optimize()
        solver.from_string(source)
        assert len(solver.objectives()) == 1
        expected = z3.RealVal(value)
        check = z3.Solver()
        check.add(solver.objectives()[0] != expected)
        assert check.check() == z3.unsat


@pytest.mark.parametrize('weight', ['1', '19', '9007199254740993', '100000000000000000000000003'])
def test_exact_weight_and_soft_feasible_set_survive_two_roundtrips(weight):
    source = ('(declare-const p Bool)(declare-const q Bool)(assert (or p q))'
              f'(assert-soft (not p) :weight {weight} :id costs)'
              '(assert-soft (not q) :weight 7 :id costs)(check-sat)')
    p, q = z3.Bools('p q')
    cost = z3.If(p, z3.IntVal(weight), 0) + z3.If(q, 7, 0)
    for _ in range(2):
        source = roundtrip(source)
        solver = z3.Optimize()
        solver.from_string(source)
        assert len(solver.objectives()) == 1
        check = z3.Solver()
        check.add(solver.objectives()[0] != cost)
        assert check.check() == z3.unsat
        check = z3.Solver()
        check.add(z3.And(*solver.assertions()) != z3.Or(p, q))
        assert check.check() == z3.unsat


@pytest.mark.parametrize('tail', [
    '(assert-soft p :weight 0)', '(assert-soft p :weight -2)',
    '(assert-soft p :weight 0.5)',
    '(assert-soft p :id a)(assert-soft (not p) :id b)',
    '(assert-soft p)(minimize (ite p 1 0))',
    '(set-option :opt.priority pareto)(assert-soft p)',
])
def test_unimplemented_cost_orderings_and_weight_domains_still_refuse(tail):
    result = sp.translate(source='(declare-const p Bool)' + tail, language='smtlib2')
    assert not result.ok
    assert all(d.code != sp.ErrorCode.E_INTERNAL for d in result.diagnostic_items)


def test_original_zero_cost_mps_roundtrips():
    path = Path(__file__).resolve().parents[2] / 'languages/mps/instances/upstream/galenet.mps'
    result = sp.translate(str(path), language='mps')
    assert result.ok and result.report.stats.num_objectives == 1
    again = sp.translate(source=result.to_smt2(sp.OmtDialect.Z3), language='smtlib2')
    assert again.ok and again.report.stats.num_objectives == 1
