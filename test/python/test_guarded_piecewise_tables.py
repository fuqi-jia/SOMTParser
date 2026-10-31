import pytest
import z3

from tools.semantic_checks.guarded_piecewise_tables import normalize_guarded_piecewise_tables


def checked(formula):
    result = normalize_guarded_piecewise_tables(formula)
    solver = z3.Solver(ctx=formula.ctx)
    solver.add(z3.Xor(formula, result.formula))
    assert solver.check() == z3.unsat
    return result


def conjuncts(formula):
    return list(formula.children()) if z3.is_and(formula) else [formula]


def test_equal_legal_tables_ignore_different_infinite_tails_and_holes():
    x, cost = z3.Ints('x cost')
    domain = z3.Or(x == -2, x == 3, x == 5)
    left = z3.If(x < 0, 7, z3.If(x < 5, 9, 11))
    right = z3.If(x == -2, 7, z3.If(x == 3, 9, z3.If(x == 5, 11, -999)))
    a = checked(z3.And(domain, cost == left))
    b = checked(z3.And(domain, cost == right))
    assert a.formula.eq(b.formula)
    assert any(node.eq(domain) for node in conjuncts(a.formula))
    for illegal in [-100, -1, 0, 1, 2, 4, 100]:
        solver = z3.Solver()
        solver.add(a.formula, x == illegal)
        assert solver.check() == z3.unsat


def test_emitted_tail_default_is_an_attained_value_not_zero():
    x, cost = z3.Ints('x cost')
    domain = z3.Or(x == 1, x == 4)
    out = checked(z3.And(domain, cost == z3.If(x == 1, 8, 9))).formula
    definition = next(n for n in conjuncts(out) if z3.is_eq(n))
    table = definition.arg(1)
    for illegal in [-100, 0, 2, 3, 5, 100]:
        assert z3.simplify(z3.substitute(table, (x, z3.IntVal(illegal)))).as_long() == 8


@pytest.mark.parametrize('shape', ['not', 'or', 'implies', 'reified', 'forall', 'exists'])
def test_conditional_domains_are_never_global_premises(shape):
    x, y = z3.Ints('x y')
    p = z3.Bool('p')
    domain = z3.Or(x == 1, x == 3)
    forms = dict(not_=z3.Not(domain), or_=z3.Or(p, domain),
                 implies=z3.Implies(p, domain), reified=p == domain,
                 forall=z3.ForAll(y, z3.Implies(y > 0, domain)),
                 exists=z3.Exists(y, z3.And(y > 0, domain)))
    clause = forms[{'not': 'not_', 'or': 'or_'}.get(shape, shape)]
    original = z3.And(clause, z3.If(x == 1, 8, 99) > 10)
    report = checked(original)
    assert report.domain_count == 0
    assert report.formula.eq(original)


def test_quantifier_body_kept_even_with_external_same_named_domain():
    x = z3.Int('x')
    q = z3.ForAll(x, z3.If(x == 1, 8, 9) >= 8)
    out = checked(z3.And(z3.Or(x == 1, x == 3), q)).formula
    assert any(n.eq(q) for n in conjuncts(out))


@pytest.mark.parametrize('values', [[], [3], [-2, 3], [-2, 3, 4, 5], [0, 1, 2], [10**80, -10**80]])
def test_domains_and_sparse_holes(values):
    x, cost = z3.Ints('x cost')
    domain = z3.Or(*[x == n for n in values])
    formula = z3.And(domain, cost == z3.If(x < 3, -7, x * 2 + 1))
    out = checked(formula).formula
    assert any(n.eq(domain) for n in conjuncts(out))


def test_intersected_domains_both_remain_exact():
    x, cost = z3.Ints('x cost')
    a, b = z3.Or(x == 1, x == 3), z3.Or(x == 3, x == 5)
    out = checked(z3.And(a, b, cost == z3.If(x == 3, 17, -900))).formula
    assert any(n.eq(a) for n in conjuncts(out)) and any(n.eq(b) for n in conjuncts(out))
    assert any(n.eq(cost == 17) for n in conjuncts(out))


def test_contradictory_domains_do_not_justify_rewrites():
    x, cost = z3.Ints('x cost')
    f = z3.And(x == 1, x == 3, cost == z3.If(x == 3, 17, -900))
    out = checked(f)
    assert out.formula.eq(f) and out.domain_count == 0


def test_false_guard_and_nested_conjunction_preserved():
    x, cost = z3.Ints('x cost')
    d = z3.Or(x == 1, x == 2)
    f = z3.And(z3.And(d, z3.BoolVal(False)), cost == z3.If(x < 2, 3, 5))
    assert z3.is_false(z3.simplify(checked(f).formula))


@pytest.mark.parametrize('op', ['le', 'lt', 'ge', 'gt', 'eq', 'ne'])
def test_constant_boolean_domain_conditions(op):
    x = z3.Int('x')
    v = z3.If(x == -2, 7, 9)
    clause = dict(le=v <= 9, lt=v < 10, ge=v >= 7, gt=v > 6, eq=v == v, ne=v != 0)[op]
    out = checked(z3.And(z3.Or(x == -2, x == 5), clause)).formula
    assert z3.is_true(out.arg(1))


def test_multiple_indices_not_mistaken_for_one():
    x, y, cost = z3.Ints('x y cost')
    d = z3.And(z3.Or(x == 1, x == 3), z3.Or(y == 2, y == 4))
    f = z3.And(d, cost == z3.If(x == 1, 2, 4) + z3.If(y == 2, 7, 9))
    out = checked(f)
    assert out.domain_count == 2
    solver = z3.Solver()
    solver.add(out.formula, x == 1, y == 4, cost != 11)
    assert solver.check() == z3.unsat


def test_mixed_index_disjunction_not_a_domain():
    x, y = z3.Ints('x y')
    f = z3.And(z3.Or(x == 1, y == 2), z3.If(x == 1, 7, 9) > 8)
    assert checked(f).domain_count == 0


def test_reversed_equality_and_dynamic_array_cell_domain():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, cost = z3.Ints('i cost')
    d = z3.Or(z3.IntVal(-2) == a[i], z3.IntVal(5) == a[i])
    out = checked(z3.And(d, cost == z3.If(a[i] <= 0, 7, 9)))
    assert out.domain_count == 1


def test_uninterpreted_function_and_unsupported_division_keep_semantics():
    x, cost = z3.Ints('x cost')
    fun = z3.Function('f', z3.IntSort(), z3.IntSort())
    term = fun(z3.If(x == 1, 7, 9)) + z3.If(x == 1, 3, 5) / x
    checked(z3.And(z3.Or(x == 1, x == 3), cost == term))


def test_real_domain_not_coerced_to_integers():
    x = z3.Real('x')
    f = z3.And(z3.Or(x == 1, x == 3), z3.If(x == 1, 3, 5) > 0)
    assert checked(f).domain_count == 0


def test_not_using_target_bound_as_its_own_premise():
    x, cost = z3.Ints('x cost')
    f = z3.And(z3.Or(x == 1, x == 3), cost <= 7, cost == z3.If(x == 1, 7, 9))
    out = checked(f).formula
    assert any(n.eq(cost <= 7) for n in conjuncts(out))
    solver = z3.Solver()
    solver.add(out, x == 3)
    assert solver.check() == z3.unsat


def test_retained_definition_and_ordered_objective_coordinates():
    x, first, second = z3.Ints('x first second')
    f = z3.And(z3.Or(x == 1, x == 3), first == z3.If(x == 1, 7, 9), second == -first)
    out = checked(f).formula
    solver = z3.Solver()
    solver.add(out, first == 7, second != -7)
    assert solver.check() == z3.unsat
    assert sum(z3.is_eq(n) for n in conjuncts(out)) == 2


def test_reification_with_actual_global_domain_is_safe():
    x = z3.Int('x')
    p = z3.Bool('p')
    checked(z3.And(z3.Or(x == 1, x == 3), p == (z3.If(x < 2, 4, 9) == 9)))


def test_shared_dag_does_not_expand_exponentially():
    x, cost = z3.Ints('x cost')
    term = z3.If(x == 1, 7, 9)
    for _ in range(150):
        term = term + term
    result = checked(z3.And(z3.Or(x == 1, x == 3), cost == term))
    assert result.visited_nodes < 180


def test_context_audit_and_original_domain_bytes():
    ctx = z3.Context()
    x = z3.Int('x', ctx)
    d = z3.Or(x == -2, x == 3)
    events = []
    f = z3.And(d, z3.If(x < 0, 8, 9) > 0)
    result = normalize_guarded_piecewise_tables(f, audit_callback=events.append)
    assert result.formula.ctx == ctx
    assert events == [dict(index='x', values=[-2, 3], retained_domain_indices=[0])]
    assert result.formula.arg(0).sexpr() == d.sexpr()
    checked(f)


def test_idempotence():
    x, cost = z3.Ints('x cost')
    f = z3.And(z3.Or(x == -2, x == 3), cost == z3.If(x < 0, 7, 9))
    first = checked(f).formula
    assert normalize_guarded_piecewise_tables(first).formula.eq(first)


def test_compound_integer_index_domain_is_valid_and_retained():
    x, cost = z3.Ints('x cost')
    index = z3.If(x == 1, 7, 9)
    domain = index == 9
    result = checked(z3.And(domain, cost == z3.If(index <= 7, 3, 5)))
    assert result.domain_count == 1
    assert any(n.eq(domain) for n in conjuncts(result.formula))
    assert any(n.eq(cost == 5) for n in conjuncts(result.formula))
