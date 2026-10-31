"""Soundness controls for sufficient proofs using shared public products."""
import pytest
import z3

from tools.semantic_checks.common_public_terms import abstract_common_public_products
from tools.semantic_checks.source_oracles.fzn_json_source import Source
from tools.semantic_checks.source_oracles.target_relation import compare


@pytest.mark.parametrize('sort', [z3.IntSort(), z3.RealSort()])
def test_reverse_substitution_recovers_both_complete_relations(sort):
    x, y, cost = z3.Consts('x y cost', sort)
    left = z3.And(x >= 0, y >= 0, cost == x*y)
    right = z3.And(cost == x*y, x+y >= 0)
    result = abstract_common_public_products(left, right, [x, y, cost])
    assert len(result.substitutions) == 1
    reverse = [(value, term) for term, value in result.substitutions]
    assert z3.substitute(result.left, *reverse).eq(left)
    assert z3.substitute(result.right, *reverse).eq(right)
    term, value = result.substitutions[0]
    solver = z3.Solver()
    solver.add(value == term, z3.Or(z3.Xor(left, result.left), z3.Xor(right, result.right)))
    assert solver.check() == z3.unsat


def test_nested_products_use_maximal_common_term_and_restore_exactly():
    x, y, z, cost = z3.Ints('x y z cost')
    inner = x*y
    outer = inner*z
    left = z3.And(cost == outer, inner >= 0)
    right = z3.And(cost == outer, inner <= 9)
    result = abstract_common_public_products(left, right, [x, y, z, cost])
    assert len(result.substitutions) == 1
    assert result.substitutions[0][0].eq(outer)
    reverse = [(value, term) for term, value in result.substitutions]
    assert z3.substitute(result.left, *reverse).eq(left)
    assert z3.substitute(result.right, *reverse).eq(right)


@pytest.mark.parametrize('kind', ['private', 'bound', 'function', 'quantified-condition'])
def test_nonpublic_or_bound_dependencies_are_not_abstracted(kind):
    x, hidden = z3.Ints('x hidden')
    if kind == 'private':
        relation = x*hidden >= 0
    elif kind == 'bound':
        relation = z3.Exists([hidden], x*hidden >= 0)
    elif kind == 'function':
        fun = z3.Function('unmapped', z3.IntSort(), z3.IntSort())
        relation = x*fun(x) >= 0
    else:
        relation = x*z3.If(z3.ForAll([hidden], hidden >= 0), x, 2) >= 0
    result = abstract_common_public_products(relation, relation, [x])
    assert not result.substitutions
    assert result.left.eq(relation) and result.right.eq(relation)


def test_unmatched_products_remain_in_their_original_formulas():
    x, y = z3.Ints('x y')
    left, right = x*y >= 0, x*x >= 0
    result = abstract_common_public_products(left, right, [x, y])
    assert not result.substitutions


@pytest.mark.parametrize('sort', [z3.IntSort(), z3.RealSort()])
def test_linear_negative_coefficients_do_not_create_abstraction(sort):
    x = z3.Const('x', sort)
    left = -3*x >= 0
    result = abstract_common_public_products(left, left, [x])
    assert not result.substitutions


def source_and_observations(constraints, *, hidden=False, direction='minimize'):
    x, y, h = z3.Ints('x y h')
    variables = {'x': x, 'y': y}
    if hidden:
        variables['h'] = h
    model = Source(variables, {}, constraints(x, y, h), x*y, direction, ())
    observations = [dict(name=name, value=value, indices=None, dimensions=[])
                    for name, value in [('x', x), ('y', y)]]
    return model, observations


def target(constraint, direction='minimize'):
    return ('(declare-const x Int)\n(declare-const y Int)\n'
            f'(assert {constraint})\n({direction} (* x y))\n(check-sat)\n(exit)').encode()


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_complete_quantified_relation_and_signed_cost_proved_by_abstraction(direction):
    model, observations = source_and_observations(lambda x,y,h: [h >= x, h < y],
                                                  hidden=True, direction=direction)
    result = compare(model, observations, target('(< x y)', direction), solve=True)
    assert result['equivalent'] and result['solver_answer'] == 'unsat', result
    assert result['public_term_abstraction']['solver_answer'] == 'unsat', result
    assert result['solver_queries'] == 1
    assert result['counterexample'] is None


def test_spurious_abstract_counterexample_requires_original_relation_query(monkeypatch):
    # Exercise the abstraction fallback explicitly even when a different,
    # sufficient conjunction certificate can establish this whole relation.
    monkeypatch.setattr(
        'tools.semantic_checks.source_oracles.target_relation.prove_qf_conjunctions',
        lambda *_: dict(equivalent=None, solver_queries=0))
    # These two finite-domain relations are equivalent. Abstracting their
    # shared product permits x=y=1 together with product=2 on the source side,
    # so SAT of the abstract XOR is spurious and must use the original query.
    model, observations = source_and_observations(
        lambda x,y,h: [x >= 1, x <= 2, y >= 1, y <= 2, x*y == 2])
    result = compare(model, observations,
                     target('(or (and (= x 1) (= y 2)) (and (= x 2) (= y 1)))'),
                     solve=True)
    assert result['public_term_abstraction']['solver_answer'] == 'sat', result
    assert result['equivalent'] and result['solver_answer'] == 'unsat', result
    assert result['conjunction_certificate']['equivalent'] is None
    assert result['solver_queries'] == 2 + result['conjunction_certificate']['solver_queries']
    assert result['counterexample'] is None


def test_real_counterexample_is_reported_only_from_original_relations(monkeypatch):
    # Exercise the abstraction fallback explicitly even when a different,
    # sufficient conjunction certificate can establish this whole relation.
    monkeypatch.setattr(
        'tools.semantic_checks.source_oracles.target_relation.prove_qf_conjunctions',
        lambda *_: dict(equivalent=None, solver_queries=0))
    model, observations = source_and_observations(lambda x,y,h: [x*y == 0])
    result = compare(model, observations, target('(and (= x 0) (= y 0))'), solve=True)
    assert result['public_term_abstraction']['solver_answer'] == 'sat', result
    assert not result['equivalent'] and result['solver_answer'] == 'sat', result
    assert result['conjunction_certificate']['equivalent'] is None
    assert result['solver_queries'] == 2 + result['conjunction_certificate']['solver_queries']
    assert result['counterexample'] is not None


@pytest.mark.parametrize('kind', ['nonboolean', 'duplicate', 'expression'])
def test_invalid_public_coordinate_contract_is_rejected(kind):
    x = z3.Int('x')
    left, right, public = x*x >= 0, x*x <= 1, [x]
    if kind == 'nonboolean':
        left = x
    elif kind == 'duplicate':
        public = [x, x]
    else:
        public = [x+1]
    with pytest.raises(ValueError):
        abstract_common_public_products(left, right, public)
