"""Full-relation controls for exact compression of ordinary binary tables."""
from itertools import permutations, product
import pytest
import z3

from tools.semantic_checks.table_cliques import CliqueTable, plan_clique_table
from tools.semantic_checks.source_oracles.xcsp_source import Reader


def rows(pairs):
    return [tuple(((v, v),) for v in pair) for pair in pairs]


def grid_points():
    # Deliberately sparse, signed and wider than int64; no grid labels or
    # bounds are provided to the planner.
    values = [-10**40, -8, -2, 0, 3, 9, 17, 31, 45, 86, 103, 10**40]
    coordinates = list(product(range(3), range(4)))
    return values, {(values[i], values[j]) for i, a in enumerate(coordinates)
                    for j, b in enumerate(coordinates)
                    if i != j and (a[0] == b[0] or a[1] == b[1])}


def flat_relation(xs, pairs):
    return z3.Or(*[z3.And(xs[0] == a, xs[1] == b) for a, b in pairs])


def equivalent(a, b):
    solver = z3.Solver()
    solver.add(z3.Xor(a, b))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('scope', ['plain', 'reverse', 'repeat', 'arithmetic'])
@pytest.mark.parametrize('negative', [False, True])
def test_complete_unbounded_relation_matches_independent_literal_rows(scope, negative):
    _, pairs = grid_points()
    plan = plan_clique_table(2, rows(pairs))
    assert plan is not None
    a, b = z3.Ints('clique_a clique_b')
    xs = {'plain': [a, b], 'reverse': [b, a], 'repeat': [a, a],
          'arithmetic': [a + 2, b - 7]}[scope]
    relation = CliqueTable(plan).relation(xs)
    reference = flat_relation(xs, pairs)
    equivalent(z3.Not(relation) if negative else relation,
               z3.Not(reference) if negative else reference)


@pytest.mark.parametrize('mutation', ['duplicate', 'reverse', 'interleave', 'disconnected'])
def test_exact_reconstruction_and_order_independence(mutation):
    _, pairs = grid_points()
    ordered = sorted(pairs)
    if mutation == 'duplicate':
        ordered += ordered
    elif mutation == 'reverse':
        ordered.reverse()
    elif mutation == 'interleave':
        ordered = ordered[::2] + ordered[1::2]
    else:
        ordered += list(permutations([1001, 1003, 1008], 2))
    plan = plan_clique_table(2, rows(ordered))
    assert plan is not None
    reconstructed = {(a, b) for family in plan for group in family
                     for a in group for b in group if a != b}
    assert reconstructed == set(ordered)
    for family in plan:
        assert len([x for group in family for x in group]) == len({x for group in family for x in group})


@pytest.mark.parametrize('bad', ['width', 'tuple_width', 'empty', 'wildcard',
                                  'interval', 'set', 'empty_cell', 'loop',
                                  'asymmetric', 'odd_cycle', 'sparse'])
def test_unrepresentable_tables_retain_general_fallback(bad):
    _, pairs = grid_points()
    data = rows(sorted(pairs))
    width = 2
    if bad == 'width': width = 3
    elif bad == 'tuple_width': data.append((((1, 1),),))
    elif bad == 'empty': data = []
    elif bad == 'wildcard': data.append((None, ((1, 1),)))
    elif bad == 'interval': data.append((((0, 2),), ((1, 1),)))
    elif bad == 'set': data.append((((0, 0), (2, 2)), ((1, 1),)))
    elif bad == 'empty_cell': data.append(((), ((1, 1),)))
    elif bad == 'loop': data += rows([(0, 0)])
    elif bad == 'asymmetric': data.pop()
    elif bad == 'odd_cycle': data = rows({(i, (i + d) % 5) for i in range(5) for d in [-1, 1]})
    elif bad == 'sparse': data = rows([(0, 1), (1, 0)])
    assert plan_clique_table(width, data) is None


@pytest.mark.parametrize('negative', [False, True])
def test_xml_groups_keep_all_domains_scopes_and_objective(negative):
    values = list(range(6))
    pairs = {(a, b) for a in values for b in values if a != b and (a // 3 == b // 3 or a % 3 == b % 3)}
    text = ''.join(f'({a},{b})' for a, b in sorted(pairs))
    polarity = 'conflicts' if negative else 'supports'
    xml = ('<instance format="XCSP3" type="COP"><variables>'
           '<var id="a">-1 0..2 4..7</var><var id="b">-3..8</var>'
           '<var id="c">0..10</var></variables><constraints>'
           '<group><extension><list>%0 %1</list>'
           f'<{polarity}>{text}</{polarity}></extension>'
           '<args>a b</args><args>b c</args><args>c a</args><args>a a</args>'
           '</group></constraints><objectives><maximize>add(a,b,c,17)</maximize>'
           '</objectives></instance>')
    reader = Reader()
    source = reader.read(xml)
    assert list(source.variables) == ['a', 'b', 'c']
    assert source.constraint_count == 4 and len(source.constraints) == 7
    assert source.private_variables == ()
    assert len(reader.extension_cliques) == 1
    assert next(iter(reader.extension_cliques.values())) is not None
    a, b, c = [source.variables[n] for n in 'abc']
    constraints = [flat_relation(xs, pairs) for xs in [(a, b), (b, c), (c, a), (a, a)]]
    if negative: constraints = list(map(z3.Not, constraints))
    domains = [z3.Or(a == -1, z3.And(a >= 0, a <= 2), z3.And(a >= 4, a <= 7)),
               z3.And(b >= -3, b <= 8), z3.And(c >= 0, c <= 10)]
    equivalent(source.relation, z3.And(*domains, *constraints))
    assert source.objectives[0][0] == 'maximize'
    assert z3.is_true(z3.simplify(source.objectives[0][1] == a + b + c + 17))


@pytest.mark.parametrize('polarity', ['supports', 'conflicts'])
@pytest.mark.parametrize('text', ['(*,1)(2,*)', '(0..2,1)(1,0..3)',
                                  '(0,0)(0,1)(1,0)', '(0,1)'])
def test_xml_nonclique_fallback_preserves_every_tuple(polarity, text):
    xml = ('<instance format="XCSP3" type="CSP"><variables>'
           '<var id="a">-1..4</var><var id="b">-1..4</var>'
           '</variables><constraints><extension><list>a b</list>'
           f'<{polarity}>{text}</{polarity}></extension></constraints></instance>')
    reader = Reader(); source = reader.read(xml)
    assert next(iter(reader.extension_cliques.values())) is None
    a, b = [source.variables[n] for n in 'ab']
    relation = {'(*,1)(2,*)': z3.Or(b == 1, a == 2),
                '(0..2,1)(1,0..3)': z3.Or(z3.And(a >= 0, a <= 2, b == 1), z3.And(a == 1, b >= 0, b <= 3)),
                '(0,0)(0,1)(1,0)': z3.Or(z3.And(a == 0, b == 0), z3.And(a == 0, b == 1), z3.And(a == 1, b == 0)),
                '(0,1)': z3.And(a == 0, b == 1)}[text]
    if polarity == 'conflicts': relation = z3.Not(relation)
    equivalent(source.relation, z3.And(a >= -1, a <= 4, b >= -1, b <= 4, relation))


def test_scope_cache_reuses_the_same_variable_across_positions():
    _, pairs = grid_points()
    table = CliqueTable(plan_clique_table(2, rows(pairs)))
    a, b, c = z3.Ints('cache_a cache_b cache_c')
    first = table.relation([a, b]); second = table.relation([b, c])
    assert all(len(cache) == 3 for cache in table.codes)
    equivalent(z3.And(first, second), z3.And(flat_relation([a, b], pairs), flat_relation([b, c], pairs)))


def test_independent_contexts_never_share_ast_identifiers():
    _, pairs = grid_points()
    table = CliqueTable(plan_clique_table(2, rows(pairs)))
    for context in [z3.Context(), z3.Context()]:
        a, b = z3.Ints('a b', ctx=context)
        relation = table.relation([a, b])
        solver = z3.Solver(ctx=context)
        solver.add(relation, a == b)
        assert solver.check() == z3.unsat
    assert all(len(cache) == 4 for cache in table.codes)


@pytest.mark.parametrize('groups', [[[0, 2, 3], [1, 2, 3]],
                                  [[0, 1, 2, 3, 4]],
                                  [[-9, 0, 4], [0, 4, 17, 99]]])
def test_overlapping_cliques_are_accepted_only_with_exact_literal_relation(groups):
    pairs = {(a, b) for group in groups for a, b in permutations(group, 2)}
    plan = plan_clique_table(2, rows(pairs))
    assert plan is not None
    a, b = z3.Ints('overlap_a overlap_b')
    equivalent(CliqueTable(plan).relation([a, b]), flat_relation([a, b], pairs))


@pytest.mark.parametrize('negative', [False, True])
@pytest.mark.parametrize('removed', [0, 1, 2])
def test_feasible_xml_group_retains_each_scope_and_joint_ordered_cost(negative, removed):
    pairs = {(a, b) for a in range(6) for b in range(6)
             if a != b and (a // 3 == b // 3 or a % 3 == b % 3)}
    text = ''.join(f'({a},{b})' for a, b in sorted(pairs))
    polarity = 'conflicts' if negative else 'supports'
    xml = ('<instance format="XCSP3" type="COP"><variables>'
           '<var id="a">-1 0..2 4..7</var><var id="b">-3..8</var>'
           '<var id="c">0..10</var></variables><constraints>'
           '<group><extension><list>%0 %1</list>'
           f'<{polarity}>{text}</{polarity}></extension>'
           '<args>a b</args><args>b c</args><args>c a</args>'
           '</group></constraints><objectives><maximize>add(a,b,c,17)</maximize>'
           '</objectives></instance>')
    model = Reader().read(xml)
    a, b, c = [model.variables[n] for n in 'abc']
    clauses = [flat_relation(xs, pairs) for xs in [(a, b), (b, c), (c, a)]]
    if negative: clauses = list(map(z3.Not, clauses))
    domains = [z3.Or(a == -1, z3.And(a >= 0, a <= 2), z3.And(a >= 4, a <= 7)),
               z3.And(b >= -3, b <= 8), z3.And(c >= 0, c <= 10)]
    cost = z3.Int('observed_signed_cost')
    actual = z3.And(model.relation, cost == -model.objectives[0][1])
    expected = z3.And(*domains, *clauses, cost == -(a + b + c + 17))
    equivalent(actual, expected)
    feasible = z3.Solver(); feasible.add(actual)
    assert feasible.check() == z3.sat
    dropped = z3.And(*domains, *[clause for i, clause in enumerate(clauses) if i != removed],
                     cost == -(a + b + c + 17))
    mutation = z3.Solver(); mutation.add(z3.Xor(actual, dropped))
    assert mutation.check() == z3.sat


def test_many_disconnected_cliques_preserve_all_edges_and_no_cross_edges():
    groups = [list(range(7 * i, 7 * i + 3)) for i in range(2500)]
    pairs = {(a, b) for group in groups for a, b in permutations(group, 2)}
    plan = plan_clique_table(2, rows(pairs))
    assert plan is not None
    reconstructed = {(a, b) for family in plan for group in family
                     for a in group for b in group if a != b}
    assert reconstructed == pairs
    assert len(plan) == 1 and len(plan[0]) == len(groups)
    assert (0, 7) not in reconstructed and (0, 0) not in reconstructed


def test_classifier_templates_are_built_once_for_two_hundred_scopes(monkeypatch):
    from tools.semantic_checks import table_cliques as module
    _, pairs = grid_points()
    plan = plan_clique_table(2, rows(pairs))
    table = CliqueTable(plan)
    calls = []
    original = module._member
    def observed(value, group):
        calls.append(group)
        return original(value, group)
    monkeypatch.setattr(module, '_member', observed)
    variables = [z3.Int('many_scope_' + str(i)) for i in range(201)]
    formulas = [table.relation(variables[i:i + 2]) for i in range(200)]
    assert len(calls) == sum(len(family) for family in plan)
    assert all(len(cache) == 201 for cache in table.codes)
    assert all(len(templates) == 1 for templates in table.templates)
    equivalent(formulas[0], flat_relation(variables[:2], pairs))
    equivalent(formulas[-1], flat_relation(variables[-2:], pairs))
