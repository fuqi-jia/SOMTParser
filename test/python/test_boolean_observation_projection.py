"""Full projected relation controls; run on the server, never by sampling."""
import pytest
import z3

from tools.semantic_checks.boolean_observation_projection import eliminate_boolean_observations


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def project(body, bridges):
    return eliminate_boolean_observations(body, bridges)


@pytest.mark.parametrize('yes,no', [(1, 0), (-7, 11), (0, -19), (7, 7),
                                    (10**100 + 37, -(10**95 + 9))])
def test_integer_cost_complete_relation(yes, no):
    b = z3.Bool('b')
    o, cost = z3.Ints('o cost')
    encoded = z3.If(b, 1, 0)
    body = z3.And(o == encoded, cost == z3.If(b, yes, no))
    result = project(body, [(o, encoded)])
    expected = z3.And(o >= 0, o <= 1, cost == no + (yes - no) * o)
    equivalent(z3.Exists([b], body), result.body)
    equivalent(result.body, expected)
    assert result.observed_boolean_cells == 1
    assert result.eliminated_roots == ('b',)


@pytest.mark.parametrize('yes,no', [('1/3', '-7/11'), ('-123456789012345678901/19', '8/5'),
                                    ('0', '0'), ('2', '1')])
def test_rational_cost_complete_relation(yes, no):
    b, o, cost = z3.Bool('b'), z3.Int('o'), z3.Real('cost')
    a, c = z3.RealVal(yes), z3.RealVal(no)
    encoded = z3.If(b, 1, 0)
    body = z3.And(o == encoded, cost == z3.If(b, a, c))
    result = project(body, [(o, encoded)])
    equivalent(z3.Exists([b], body), result.body)
    equivalent(result.body, z3.And(o >= 0, o <= 1, cost == c + (a-c)*o))


def test_duplicate_integer_and_boolean_aliases_retain_all_relations():
    b, flag = z3.Bools('b flag')
    first, second, cost = z3.Ints('first second cost')
    encoded = z3.If(b, 1, 0)
    bridges = [(first, encoded), (second, encoded), (flag, b)]
    body = z3.And(*(alias == term for alias, term in bridges), cost == z3.If(b, -5, 12))
    result = project(body, bridges)
    expected = z3.And(first >= 0, first <= 1, second == first,
                      flag == (first == 1), cost == 12 - 17*first)
    equivalent(z3.Exists([b], body), result.body)
    equivalent(result.body, expected)
    assert result.observed_boolean_cells == 1


def test_full_body_hard_constraints_and_signed_objective():
    a, b = z3.Bools('a b')
    x, y, signed_cost = z3.Ints('x y signed_cost')
    ax, by = z3.If(a, 1, 0), z3.If(b, 1, 0)
    body = z3.And(x == ax, y == by, z3.Or(a, b), z3.Not(z3.And(a, b)),
                  signed_cost == -(z3.If(a, 7, 0) + z3.If(b, -2, 0)))
    result = project(body, [(x, ax), (y, by)])
    expected = z3.And(x >= 0, x <= 1, y >= 0, y <= 1, x+y == 1,
                      signed_cost == -7*x + 2*y)
    equivalent(z3.Exists([a, b], body), result.body)
    equivalent(result.body, expected)
    wrong = z3.And(x >= 0, x <= 1, y >= 0, y <= 1, x+y == 1,
                   signed_cost == 7*x - 2*y)
    solver = z3.Solver()
    solver.add(z3.Xor(result.body, wrong))
    assert solver.check() == z3.sat


def test_nonliteral_branches_preserve_ite():
    b = z3.Bool('b')
    o, u, v, cost = z3.Ints('o u v cost')
    encoded = z3.If(b, 1, 0)
    body = z3.And(o == encoded, cost == z3.If(b, u*u, v))
    result = project(body, [(o, encoded)])
    equivalent(z3.Exists([b], body), result.body)
    equivalent(result.body, z3.And(o>=0, o<=1, cost == z3.If(o==1, u*u, v)))


def test_boolean_in_uf_and_store_is_substituted_everywhere():
    b = z3.Bool('b')
    o = z3.Int('o')
    f = z3.Function('f', z3.BoolSort(), z3.IntSort())
    array = z3.Array('a', z3.IntSort(), z3.BoolSort())
    encoded = z3.If(b, 1, 0)
    body = z3.And(o == encoded, f(b) == 3, z3.Select(z3.Store(array, 2, b), 3))
    result = project(body, [(o, encoded)])
    equivalent(z3.Exists([b], body), result.body)
    assert result.eliminated_roots == ('b',)


def test_two_concrete_array_cells_complete_projection():
    a = z3.Array('a', z3.IntSort(), z3.BoolSort())
    p, q = z3.Select(a, -2), z3.Select(a, 4)
    x, y, cost = z3.Ints('x y cost')
    px, qy = z3.If(p, 1, 0), z3.If(q, 1, 0)
    body = z3.And(x == px, y == qy, p == z3.Not(q), cost == z3.If(p, -2, 3))
    result = project(body, [(x, px), (y, qy)])
    equivalent(z3.Exists([a], body), result.body)
    equivalent(result.body, z3.And(x>=0, x<=1, y>=0, y<=1, x+y==1, cost==3-5*x))
    assert result.eliminated_roots == ('a',)


@pytest.mark.parametrize('escape', ['symbolic', 'unobserved', 'whole-array', 'array-uf', 'store'])
def test_escaping_array_rolls_back_entire_root(escape):
    a, other = z3.Array('a', z3.IntSort(), z3.BoolSort()), z3.Array('other', z3.IntSort(), z3.BoolSort())
    i, o = z3.Ints('i o')
    encoded = z3.If(z3.Select(a, 0), 1, 0)
    f = z3.Function('f', a.sort(), z3.BoolSort())
    extra = {'symbolic': z3.Select(a, i), 'unobserved': z3.Select(a, 1),
             'whole-array': a == other, 'array-uf': f(a),
             'store': z3.Store(a, 2, False) == other}[escape]
    body = z3.And(o == encoded, extra)
    result = project(body, [(o, encoded)])
    assert result.body.eq(body)
    assert not result.eliminated_roots and result.retained_roots == ('a',)


def test_one_escaping_root_does_not_block_independent_scalar():
    a = z3.Array('a', z3.IntSort(), z3.BoolSort())
    b, x, y, i = z3.Bool('b'), z3.Int('x'), z3.Int('y'), z3.Int('i')
    ax, by = z3.If(z3.Select(a, 0), 1, 0), z3.If(b, 1, 0)
    body = z3.And(x == ax, y == by, z3.Select(a, i), z3.Not(b))
    result = project(body, [(x, ax), (y, by)])
    equivalent(z3.Exists([b], body), result.body)
    assert result.eliminated_roots == ('b',) and result.retained_roots == ('a',)


@pytest.mark.parametrize('shape', ['missing', 'disjunction', 'negated', 'reversed-encoding', 'computed-condition', 'quantifier'])
def test_nonqualified_bridge_is_preserved(shape):
    b, o = z3.Bool('b'), z3.Int('o')
    encoded = z3.If(b, 1, 0)
    bridge = o == encoded
    if shape == 'missing': body = z3.And(b, o == 8)
    elif shape == 'disjunction': body = z3.Or(bridge, o == 8)
    elif shape == 'negated': body = z3.Not(bridge)
    elif shape == 'reversed-encoding':
        encoded = z3.If(b, 0, 1)
        body = o == encoded
    elif shape == 'computed-condition':
        encoded = z3.If(z3.Not(b), 1, 0)
        body = o == encoded
    else: body = z3.Exists([b], bridge)
    result = project(body, [(o, encoded)])
    assert result.body.eq(body) and result.observed_boolean_cells == 0


def test_outside_binary_domain_remains_impossible():
    b, o = z3.Bool('b'), z3.Int('o')
    encoded = z3.If(b, 1, 0)
    result = project(o == encoded, [(o, encoded)])
    for bad in [-100, -1, 2, 100]:
        solver = z3.Solver()
        solver.add(result.body, o == bad)
        assert solver.check() == z3.unsat


def test_adapter_preserves_two_integer_aliases_and_bool_alias():
    from tools.semantic_checks.checker_adapter import candidate_projection
    b, flag = z3.Bools('b flag')
    x, y, cost = z3.Ints('x y cost')
    encoded = z3.If(b, 1, 0)
    result = candidate_projection([], [(x, encoded), (y, encoded), (flag, b)],
                                  (cost, z3.If(b, -3, 5)), guarded_bool_budget_ms=None)
    expected = z3.And(x>=0, x<=1, y==x, flag==(x==1), cost==5-8*x)
    equivalent(result.formula, expected)
    assert result.optimization.boolean_observation_cells == 1


def test_adapter_full_bool_array_relation_matches_integer_reference():
    from tools.semantic_checks.checker_adapter import check_relation_equivalence
    a = z3.Array('a', z3.IntSort(), z3.BoolSort())
    x, y, ox, oy, oz, signed_cost = z3.Ints('x y ox oy oz signed_cost')
    p, q = z3.Select(a, 0), z3.Select(a, 1)
    ref = [x>=0, x<=1, y>=0, y<=1, x+y==1]
    cand = [z3.If(p, 1, 0)+z3.If(q, 1, 0)==1]
    result = check_relation_equivalence(ref, cand,
        reference_bridges=[(ox, x), (oy, y)],
        candidate_bridges=[(ox, z3.If(p, 1, 0)), (oy, z3.If(q, 1, 0))],
        reference_cost_bridge=(signed_cost, -7*x+2*y),
        candidate_cost_bridge=(signed_cost, -z3.If(p, 7, 0)+z3.If(q, 2, 0)),
        total_timeout_ms=None, per_obligation_timeout_ms=None, preprocessing_budget_ms=None)
    assert result.comparison.equivalent is True
    assert result.candidate.optimization.boolean_observation_cells == 2
    assert not z3.is_quantifier(result.candidate.formula)


def test_no_encoded_bridge_never_scans_body(monkeypatch):
    import tools.semantic_checks.projection as projection
    x, observed = z3.Ints('x observed')
    body = z3.And(x>=0, x<=100, observed==x)
    def forbidden(*args, **kwargs):
        raise AssertionError('an inapplicable rule traversed the body')
    monkeypatch.setattr(projection, 'contains_quantifier', forbidden)
    monkeypatch.setattr(projection, 'free_constants', forbidden)
    result = project(body, [(observed, x)])
    assert result.body.eq(body) and result.bridges == ((observed, x),)
