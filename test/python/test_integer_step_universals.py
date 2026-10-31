import itertools
import pytest
import z3
from tools.semantic_checks.integer_step_universals import expand_integer_step_universals


def same(a, b):
    solver = z3.Solver(ctx=a.ctx)
    solver.add(z3.Xor(a, b))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('op', ['lt', 'le', 'gt', 'ge', 'eq', 'ne'])
@pytest.mark.parametrize('reversed_order', [False, True])
def test_each_comparison_both_orders(op, reversed_order):
    t, a, b = z3.Ints('t a b')
    def compare(x, y):
        return dict(lt=lambda:x<y, le=lambda:x<=y, gt=lambda:x>y,
                    ge=lambda:x>=y, eq=lambda:x==y, ne=lambda:x!=y)[op]()
    atom = compare(a, t) if reversed_order else compare(t, a)
    source = z3.ForAll(t, z3.Implies(z3.And(b <= t, t < b + 2), atom))
    result = expand_integer_step_universals(source)
    assert result.expanded_quantifiers == 1
    same(source, result.formula)


@pytest.mark.parametrize('heights', [(3, 4), (-3, 4), (3, -4), (-3, -4), (0, 0)])
@pytest.mark.parametrize('durations', [(2, 3), (0, 2), (-2, 3), (-2, -3)])
def test_cumulative_signed_heights_and_nonpositive_lengths(heights, durations):
    t, a, b, limit = z3.Ints('t a b limit')
    starts = [a, b]
    ends = [s + d for s, d in zip(starts, durations)]
    load = z3.Sum(*[z3.If(z3.And(s <= t, t < e), h, 0)
                    for s, e, h in zip(starts, ends, heights)])
    source = z3.ForAll(t, load <= limit)
    result = expand_integer_step_universals(source)
    expected = z3.And(0 <= limit, *[z3.substitute(load, (t, event)) <= limit
                                  for event in starts + ends])
    assert result.event_instances == 4
    same(result.formula, expected)


def test_whole_integer_line_no_horizon():
    t = z3.Int('t')
    for start in [-10**30, 10**30]:
        source = z3.ForAll(t, z3.Not(z3.And(start <= t, t < start + 1)))
        result = expand_integer_step_universals(source)
        assert z3.is_false(z3.simplify(result.formula))
    source = z3.ForAll(t, z3.If(z3.And(0 <= t, t < 2), 0, 1) <= 0)
    assert z3.is_false(z3.simplify(expand_integer_step_universals(source).formula))


def test_nonmonotone_condition_requires_end_events():
    t = z3.Int('t')
    load = z3.If(z3.And(0 <= t, t < 1), -2, 0) + z3.If(z3.And(0 <= t, t < 2), 1, 0)
    source = z3.ForAll(t, load <= 0)
    assert z3.is_false(z3.simplify(expand_integer_step_universals(source).formula))


@pytest.mark.parametrize('kind', ['arithmetic', 'index', 'function', 'nested', 'exists', 'real', 'multi', 'open'])
def test_unsupported_binder_preserved(kind):
    t, u = z3.Ints('t u')
    arr = z3.Array('a', z3.IntSort(), z3.IntSort())
    fun = z3.Function('f', z3.IntSort(), z3.IntSort())
    real = z3.Real('r')
    source = dict(arithmetic=lambda:z3.ForAll(t, t + 1 <= u),
                  index=lambda:z3.ForAll(t, arr[t] <= 1),
                  function=lambda:z3.ForAll(t, fun(t) <= 1),
                  nested=lambda:z3.ForAll(t, z3.Exists(u, t < u)),
                  exists=lambda:z3.Exists(t, t < u),
                  real=lambda:z3.ForAll(real, real < u),
                  multi=lambda:z3.ForAll([t, u], t < u),
                  open=lambda:z3.ForAll(t, t < z3.Var(1, z3.IntSort()))) [kind]()
    result = expand_integer_step_universals(source)
    assert result.formula.eq(source)
    assert result.expanded_quantifiers == 0


def test_conjuncts_cost_and_public_constraints_retained():
    t, x, cost = z3.Ints('t x cost')
    source = z3.And(x >= 4, cost == -x, z3.ForAll(t, z3.Implies(t < x, t <= x)))
    result = expand_integer_step_universals(source)
    same(result.formula, z3.And(x >= 4, cost == -x))


def test_custom_context_and_vacuous_binder():
    ctx = z3.Context()
    t, x = z3.Ints('t x', ctx=ctx)
    source = z3.ForAll(t, x > 0)
    result = expand_integer_step_universals(source)
    assert result.formula.ctx == ctx and result.expanded_quantifiers == 1
    same(result.formula, x > 0)


def test_shared_dag_and_free_symbols_not_named_away():
    t, source_cumulative_time, bound = z3.Ints('t source_cumulative_time bound')
    leaf = z3.Implies(t < bound, t <= bound)
    body = leaf
    for _ in range(20):
        body = z3.And(body, body)
    source = z3.And(source_cumulative_time == -7, z3.ForAll(t, body))
    result = expand_integer_step_universals(source)
    assert result.expanded_quantifiers == 1
    same(result.formula, source_cumulative_time == -7)


def test_binder_under_disjunction_is_untouched():
    t, x = z3.Ints('t x')
    source = z3.Or(x == 0, z3.ForAll(t, t < x))
    result = expand_integer_step_universals(source)
    assert result.formula.eq(source) and not result.expanded_quantifiers
