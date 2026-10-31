import pytest
import z3

from tools.semantic_checks import boolean_indicator_products as indicator
from tools.semantic_checks.existential_definitions import _normalize_indicator_conjuncts


def exact(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def counted_normalizer(monkeypatch):
    calls = []
    normalize = indicator.normalize_boolean_indicator_products

    def count(formula):
        result = normalize(formula)
        calls.append((formula, result))
        return result

    monkeypatch.setattr(indicator, 'normalize_boolean_indicator_products', count)
    return calls


@pytest.mark.parametrize('kind', ['int', 'real', 'array'])
@pytest.mark.parametrize('separate_context', [False, True])
def test_shared_qf_without_indicator_products_is_scanned_once(monkeypatch, kind, separate_context):
    ctx = z3.Context() if separate_context else None
    sort = z3.RealSort(ctx=ctx) if kind == 'real' else z3.IntSort(ctx=ctx)
    x = z3.Const('shared_x', sort)
    shared = x
    for index in range(64):
        shared = shared * x + index
    if kind == 'array':
        array = z3.Array('shared_array', sort, sort)
        shared = z3.Select(array, shared)
    # Each clause shares the same large arithmetic DAG. No factor is a
    # Boolean indicator, so repeated clause scans perform identical work.
    body = z3.And(*[shared != index for index in range(128)])
    calls = counted_normalizer(monkeypatch)
    result, products = _normalize_indicator_conjuncts(body)
    assert len(calls) == 1
    assert calls[0][1].complete_scan
    assert products == 0 and result.eq(body)
    exact(body, result)


@pytest.mark.parametrize('real', [False, True])
def test_shared_products_still_use_one_complete_scan(monkeypatch, real):
    b, c = z3.Bools('product_b product_c')
    x = z3.Real('product_x') if real else z3.Int('product_x')
    number = z3.RealVal if real else z3.IntVal
    shared = x * z3.If(b, number(1), number(0)) * z3.If(c, number(1), number(0))
    body = z3.And(shared >= -3, shared <= 7, x != 0)
    calls = counted_normalizer(monkeypatch)
    result, products = _normalize_indicator_conjuncts(body)
    assert len(calls) == 1 and calls[0][1].complete_scan
    assert products > 0
    exact(body, result)
    mutation = z3.Solver()
    mutation.add(z3.Xor(result, z3.And(shared >= -3, shared <= 7)))
    assert mutation.check() == z3.sat


def test_nested_binder_refusal_retains_sibling_fallback(monkeypatch):
    i, x = z3.Ints('bound_i public_x')
    b, c = z3.Bools('bound_b bound_c')
    nested = z3.ForAll([i], z3.Or(i <= x, i > x))
    product = z3.If(b, 1, 0) * z3.If(c, 1, 0)
    body = z3.And(nested, product == x, x >= 0)
    calls = counted_normalizer(monkeypatch)
    result, products = _normalize_indicator_conjuncts(body)
    assert not calls[0][1].complete_scan
    assert len(calls) == 4 and products > 0
    assert any(not item.complete_scan and formula.eq(nested) for formula, item in calls[1:])
    exact(body, result)
    exact(z3.Exists([b, c], body), z3.Exists([b, c], result))


def test_loose_bound_variable_marks_incomplete_scan_and_keeps_input():
    loose = z3.Var(0, z3.BoolSort())
    body = z3.And(loose, z3.Bool('free_b'))
    result = indicator.normalize_boolean_indicator_products(body)
    assert not result.complete_scan and result.formula.eq(body)
    assert result.product_nodes == 0
    replacement = z3.Bool('opened_b')
    exact(z3.substitute_vars(body, replacement),
          z3.substitute_vars(result.formula, replacement))
