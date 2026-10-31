"""Whole-formula identities and scope/type boundaries for indicator products."""
import pytest
import z3

from tools.semantic_checks.boolean_indicator_products import normalize_boolean_indicator_products


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat



def no_multiplication(formula):
    # Algebraic normalization must remove these products. Whether Z3's
    # simplifier folds a propositional tautology to a literal is unrelated.
    pending, seen = [formula], set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        assert not z3.is_app_of(node, z3.Z3_OP_MUL)
        pending.extend(node.children())

@pytest.mark.parametrize('real', [False, True])
@pytest.mark.parametrize('reverse', [False, True])
@pytest.mark.parametrize('scale', [-7, 1, 3])
def test_entire_relation_with_unbounded_other_factor_and_signed_cost(real, reverse, scale):
    context = z3.Context(); b, c = z3.Bools('b c', ctx=context)
    number = z3.RealVal if real else z3.IntVal
    sort = z3.RealSort(ctx=context) if real else z3.IntSort(ctx=context)
    x, cost = z3.Consts('x cost', sort)
    first = z3.If(b, number(0 if reverse else 1, ctx=context),
                  number(1 if reverse else 0, ctx=context))
    second = z3.If(c, number(1, ctx=context), number(0, ctx=context))
    original = z3.And(x >= -13, cost == scale * x * first * second + 19)
    result = normalize_boolean_indicator_products(original)
    assert result.product_nodes > 0 and result.formula.ctx == context
    equivalent(original, result.formula)
    expected = z3.And(x >= -13,
                      cost == scale * x * z3.If(z3.And(z3.Not(b) if reverse else b, c),
                                                number(1, ctx=context), number(0, ctx=context)) + 19)
    equivalent(result.formula, expected)
    changed = z3.And(x >= -13, cost == scale * x + 19)
    solver = z3.Solver(ctx=context); solver.add(z3.Xor(result.formula, changed))
    assert solver.check() == z3.sat


@pytest.mark.parametrize('shape', ['range', 'conjunction', 'repeated'])
def test_actual_gt_indicator_tautologies_and_repeated_factor(shape):
    b, c = z3.Bools('b c'); product = z3.If(b, 1, 0) * z3.If(c, 1, 0)
    if shape == 'range':
        formula = z3.Or(product == 0, product == 1)
    elif shape == 'conjunction':
        formula = z3.Or(product == 1, z3.Not(b), z3.Not(c))
    else:
        formula = z3.If(b, 1, 0) * z3.If(b, 1, 0) == z3.If(b, 1, 0)
    result = normalize_boolean_indicator_products(formula)
    assert result.product_nodes > 0
    equivalent(formula, result.formula)
    equivalent(result.formula, z3.BoolVal(True))
    no_multiplication(result.formula)


@pytest.mark.parametrize('value', ['nonbinary', 'bitvector', 'single'])
def test_does_not_invent_boolean_domains_or_change_other_numeric_types(value):
    b, c = z3.Bools('b c'); x = z3.Int('x')
    if value == 'nonbinary':
        formula = z3.If(b, 2, 0) * z3.If(c, 1, 0) == x
    elif value == 'bitvector':
        formula = z3.If(b, z3.BitVecVal(1, 8), z3.BitVecVal(0, 8)) * z3.If(c, z3.BitVecVal(1, 8), z3.BitVecVal(0, 8)) == 0
    else:
        formula = z3.If(b, 1, 0) * x == 0
    result = normalize_boolean_indicator_products(formula)
    assert result.product_nodes == 0 and result.formula.eq(formula)


@pytest.mark.parametrize('scope', ['forall', 'exists', 'loose'])
def test_bound_scopes_leave_the_complete_formula_unchanged(scope):
    b, c = z3.Bools('b c'); product = z3.If(b, 1, 0) * z3.If(c, 1, 0)
    body = product == 1
    scoped = (z3.ForAll([b], body) if scope == 'forall' else
              z3.Exists([b], body) if scope == 'exists' else
              z3.Var(0, z3.IntSort()) == 0)
    formula = z3.And(product >= 0, scoped)
    result = normalize_boolean_indicator_products(formula)
    assert result.product_nodes == 0 and result.formula.eq(formula)


def test_shared_dag_is_rewritten_once_and_contradictory_observations_survive():
    b, c = z3.Bools('b c'); product = z3.If(b, 1, 0) * z3.If(c, 1, 0)
    formula = z3.And(product == 1, product == 0)
    result = normalize_boolean_indicator_products(formula)
    assert result.product_nodes == 1 and result.combined_factors == 1
    equivalent(formula, result.formula)
    equivalent(result.formula, z3.BoolVal(False))
    no_multiplication(result.formula)


def test_nested_products_do_not_recurse_in_python():
    guards = [z3.Bool('indicator_%d' % index) for index in range(192)]
    product = z3.If(guards[0], 1, 0)
    for guard in guards[1:]:
        product = product * z3.If(guard, 1, 0)
    original = product == 1
    result = normalize_boolean_indicator_products(original)
    equivalent(original, result.formula)
    equivalent(result.formula, z3.And(*guards))


def test_non_boolean_input_rejected():
    with pytest.raises(ValueError):
        normalize_boolean_indicator_products(z3.Int('x'))
