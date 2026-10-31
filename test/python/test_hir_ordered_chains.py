"""Ordered HIR chains equal their independent adjacent-pair conjunctions."""
import pytest
import z3
from somtparser.hir import HirBuilder, ModelError


@pytest.mark.parametrize('operator,symbol', [('le', '<='), ('lt', '<'), ('ge', '>='), ('gt', '>')])
@pytest.mark.parametrize('sort', ['Int', 'Real'])
@pytest.mark.parametrize('negated', [False, True])
def test_ordered_chain_matches_adjacent_pairs(operator, symbol, sort, negated):
    builder = HirBuilder()
    names = ['a', 'b', 'c', 'd']
    for name in names:
        builder.declare(name, sort)
    chain = {'op': operator, 'args': [{'var': name} for name in names]}
    builder.constrain({'op': 'not', 'args': [chain]} if negated else chain)
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    reference = ''.join(f'(declare-const {name} {sort})' for name in names)
    pairs = '(and ' + ' '.join(f'({symbol} {a} {b})' for a, b in zip(names, names[1:])) + ')'
    reference += '(assert ' + ('(not ' + pairs + ')' if negated else pairs) + ')'
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(translated.to_smt2())),
                     z3.And(*z3.parse_smt2_string(reference))))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('operator', ['le', 'lt', 'ge', 'gt'])
def test_chain_rejects_unary_and_boolean_middle(operator):
    builder = HirBuilder()
    with pytest.raises(ModelError):
        builder.constrain({'op': operator, 'args': [{'literal': 1, 'sort': 'Int'}]})
    with pytest.raises(ModelError):
        builder.constrain({'op': operator, 'args': [
            {'literal': 1, 'sort': 'Int'}, {'literal': True, 'sort': 'Bool'},
            {'literal': 2, 'sort': 'Int'}]})
