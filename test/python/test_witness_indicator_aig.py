import pytest
import z3
from tools.semantic_checks.existential_definitions import (
    _aig_indicator_formula, eliminate_existential_definitions)


def exact(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('shape', ['domain', 'implication', 'contradiction'])
def test_gt_indicator_tautologies_release_private_binders(shape):
    b, c = z3.Bools('private_b private_c')
    product = z3.If(b, 1, 0)*z3.If(c, 1, 0)
    body = {'domain': z3.Or(product == 0, product == 1),
            'implication': z3.Or(product == 1, z3.Not(b), z3.Not(c)),
            'contradiction': z3.And(b, c, product == 0)}[shape]
    original = z3.Exists([b, c], body)
    projected = eliminate_existential_definitions(original)
    assert projected.indicator_products > 0
    assert z3.is_false(projected.formula) if shape == 'contradiction' else z3.is_true(projected.formula)
    exact(original, projected.formula)


@pytest.mark.parametrize('real', [False, True])
@pytest.mark.parametrize('separate_context', [False, True])
def test_aig_preserves_complete_cost_and_public_theory_atoms(real, separate_context):
    ctx = z3.Context() if separate_context else None
    b, c = z3.Bools('b c', ctx=ctx)
    number = z3.RealVal if real else z3.IntVal
    sort = z3.RealSort(ctx=ctx) if real else z3.IntSort(ctx=ctx)
    x, cost = z3.Consts('x cost', sort)
    product = z3.If(b, number(1,ctx=ctx), number(0,ctx=ctx))*z3.If(c, number(1,ctx=ctx), number(0,ctx=ctx))
    body = z3.And(z3.Or(product == 1, z3.Not(b), z3.Not(c)), x > 0, cost == -3*x)
    original = z3.Exists([b, c], body)
    projected = eliminate_existential_definitions(original)
    exact(original, projected.formula)
    exact(projected.formula, z3.And(x > 0, cost == -3*x))
    mutation = z3.Solver(ctx=projected.formula.ctx)
    mutation.add(z3.Xor(projected.formula, z3.And(x > 0, cost == -3*x+1)))
    assert mutation.check() == z3.sat


def test_retained_quantifier_is_not_sent_into_aig(monkeypatch):
    b, c = z3.Bools('b c')
    i = z3.Int('i')
    f = z3.Function('f', z3.IntSort(), z3.BoolSort())
    quantified = z3.ForAll([i], f(i))
    product = z3.If(b,1,0)*z3.If(c,1,0)
    original = z3.Exists([b,c],z3.And(quantified,z3.Or(product==1,z3.Not(b),z3.Not(c))))
    tactic = z3.Tactic
    def checked(name, **kwargs):
        inner = tactic(name, **kwargs)
        def apply(goal):
            todo = list(goal)
            while todo:
                term = todo.pop()
                assert not z3.is_quantifier(term)
                todo.extend(term.children())
            return inner(goal)
        return apply
    monkeypatch.setattr(z3, 'Tactic', checked)
    result = eliminate_existential_definitions(original)
    exact(result.formula, quantified)
    exact(original, result.formula)


@pytest.mark.parametrize('failure', ['exception', 'two-goals', 'new-declaration'])
def test_tactic_refusal_retains_complete_exact_input(monkeypatch, failure):
    b, c = z3.Bools('b c')
    formula = z3.And(b, c)
    def replaced(name, **kwargs):
        def apply(goal):
            if failure == 'exception':
                raise z3.Z3Exception('test refusal')
            first = z3.Goal(ctx=formula.ctx)
            first.add(z3.Bool('new_private') if failure == 'new-declaration' else b)
            if failure == 'two-goals':
                second = z3.Goal(ctx=formula.ctx);second.add(c)
                return [first, second]
            return [first]
        return apply
    monkeypatch.setattr(z3, 'Tactic', replaced)
    result = _aig_indicator_formula(formula)
    assert result.eq(formula)
    exact(formula, result)


def test_malformed_quantifier_scope_is_not_entered():
    i = z3.Int('i')
    formula = z3.ForAll([i], i == i)
    assert _aig_indicator_formula(formula).eq(formula)
    loose = z3.Var(0,z3.BoolSort())
    assert _aig_indicator_formula(loose).eq(loose)


def test_shared_indicator_relation_has_no_residual_private_binders():
    variables = z3.Bools(' '.join('shared_'+str(i) for i in range(128)))
    clauses = []
    for i, b in enumerate(variables):
        c = variables[(i+1)%len(variables)]
        product = z3.If(b,1,0)*z3.If(c,1,0)
        clauses.append(z3.Or(product==1,z3.Not(b),z3.Not(c)))
    original = z3.Exists(variables,z3.And(*clauses))
    result = eliminate_existential_definitions(original)
    assert result.indicator_products > 0 and z3.is_true(result.formula)
    exact(original,result.formula)
