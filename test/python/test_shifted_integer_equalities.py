import pytest
import z3

from tools.semantic_checks.shifted_integer_equalities import normalize_shifted_integer_equalities as normalize


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.add(left != right)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('offset', [-13, -1, 0, 1, 8, 10**30])
@pytest.mark.parametrize('context', ['plain', 'not', 'or'])
def test_shifted_source_and_target_match(offset, context):
    x, y, z = z3.Ints('pd[155] aux_gb[1252] cost')
    left, right = x == y - offset, y == x + offset
    wrap = {'plain': lambda a: a, 'not': z3.Not, 'or': lambda a: z3.Or(a, z == 7)}[context]
    left, right = wrap(left), wrap(right)
    a, b = normalize(left), normalize(right)
    assert a.eligible_equalities == b.eligible_equalities == 1
    assert a.formula.eq(b.formula)
    equivalent(left, a.formula)
    equivalent(right, b.formula)


@pytest.mark.parametrize('offset', [-4, 0, 3])
def test_wrong_offset_still_has_counterexample(offset):
    x, y = z3.Ints('x y')
    a, b = normalize(x == y - offset), normalize(y == x + offset + 1)
    solver = z3.Solver()
    solver.add(a.formula != b.formula)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('mode', ['real', 'bv', 'nonlinear', 'three', 'scaled', 'division', 'bound'])
def test_unsupported_atoms_unchanged(mode):
    x, y, z = z3.Ints('x y z')
    a, b = z3.Reals('a b')
    u, v = z3.BitVecs('u v', 8)
    formula = {'real': a == b + 1, 'bv': u == v + 1,
               'nonlinear': x == y*y, 'three': x == y + z,
               'scaled': 2*x == 2*y + 2, 'division': x == y/2,
               'bound': z3.ForAll([x], x == y + 1)}[mode]
    result = normalize(formula)
    assert result.eligible_equalities == 0
    assert result.formula.eq(formula)


def test_affine_reordering_cancellation_and_literal_product():
    x, y, z = z3.Ints('x y z')
    originals = [x == y - 4, -x + y == 4, 4 == y - x,
                 1*x + z == y + z - 2*2, y == x + 4]
    normalized = [normalize(f) for f in originals]
    assert all(r.formula.eq(normalized[0].formula) for r in normalized)
    for f, r in zip(originals, normalized):
        equivalent(f, r.formula)


def test_preserves_all_ordered_cost_constraints():
    x, y, c0, c1 = z3.Ints('x y c0 c1')
    left = z3.And(x == y-1, c0 == x+7, c1 == y-8, x >= 0)
    right = z3.And(y == x+1, x == c0-7, y == c1+8, x >= 0)
    a, b = normalize(left), normalize(right)
    assert a.formula.eq(b.formula)
    equivalent(left, a.formula)
    swapped = normalize(z3.And(y == x+1, y == c0+8, x == c1-7, x >= 0))
    solver = z3.Solver()
    solver.add(a.formula != swapped.formula)
    assert solver.check() == z3.sat


def test_free_equalities_under_binder_keep_bound_coordinate():
    x, y, z = z3.Ints('x y z')
    original = z3.Exists([z], z3.And(x == y-3, z > x))
    result = normalize(original)
    assert result.eligible_equalities == 1
    equivalent(original, result.formula)


def test_nondefault_context():
    ctx = z3.Context()
    x, y = z3.Ints('x y', ctx=ctx)
    a, b = normalize(x == y-2), normalize(y == x+2)
    assert a.formula.eq(b.formula)
    equivalent(x == y-2, a.formula)
