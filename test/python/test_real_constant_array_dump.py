"""Real numerals retain their sorts in polymorphic constant-array contexts."""
from fractions import Fraction
import pytest
import z3
import somtparser as sp


@pytest.mark.parametrize('value', ['0', '1', '-1', '123456789012345678901234567890',
                                    '0.0', '-2.000', '7/11'])
@pytest.mark.parametrize('nested', [False, True])
def test_hir_constant_array_real_values_are_independently_parseable(value, nested):
    b = sp.HirBuilder(); b.declare('i', 'Int'); b.declare('r', 'Real')
    array = {'const_array': {'index_sort': 'Int', 'value': {'literal': value, 'sort': 'Real'}}}
    if nested:
        array = {'const_array': {'index_sort': 'Bool', 'value': array}}
        array = {'op': 'select', 'args': [array, {'literal': True, 'sort': 'Bool'}]}
    read = {'op': 'select', 'args': [array, {'var': 'i'}]}
    b.constrain({'op': 'eq', 'args': [{'var': 'r'}, read]})
    result = b.translate(); assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(z3.Xor(actual, z3.Real('r') == z3.RealVal(str(Fraction(value)))))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('value', ['0.0', '1.0', '(- 2.0)', '(/ 3.0 7.0)'])
def test_smtlib_real_constant_array_survives_lifting_and_export(value):
    source = ('(declare-const a (Array Int Real))'
              f'(assert (= a ((as const (Array Int Real)) {value})))'
              '(check-sat)')
    result = sp.translate(source=source, language='smtlib2')
    assert result.ok, [d.message for d in result.diagnostic_items]
    original = z3.And(*z3.parse_smt2_string(source))
    emitted = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(z3.Xor(original, emitted))
    assert solver.check() == z3.unsat
