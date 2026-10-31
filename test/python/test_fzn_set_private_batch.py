"""Keep finite-set projection exact without repeatedly scanning all witnesses."""
import itertools
from types import SimpleNamespace

import pytest
import z3

from tools.semantic_checks.source_oracles import fzn_json_source as module


def literal(values):
    result = z3.EmptySet(z3.IntSort())
    for value in values:
        result = z3.SetAdd(result, value)
    return result


def subsets(values):
    return [members for n in range(len(values)+1)
            for members in itertools.combinations(values, n)]


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_two_carriers_relations_observations_and_signed_cost(direction):
    source = module.read_source(dict(version='1.0', variables={
        'a': dict(type='set of int', domain=[[-1, 1]]),
        'b': dict(type='set of int', domain=[[0, 2]]),
        'ca': dict(type='int', domain=[[0, 3]]),
        'cb': dict(type='int', domain=[[0, 3]]),
        'cost': dict(type='int', domain=[[0, 6]])}, arrays={}, constraints=[
        dict(id='set_card', args=['a', 'ca']),
        dict(id='set_card', args=['b', 'cb']),
        dict(id='set_subset', args=['a', 'b']),
        dict(id='set_ne', args=['b', {'set': []}]),
        dict(id='int_plus', args=['ca', 'cb', 'cost'])], output=['a', 'b'],
        solve=dict(method=direction, objective='cost')))
    a, b = [z3.FreshConst(z3.SetSort(z3.IntSort()), name) for name in ['a', 'b']]
    cost = z3.FreshInt('cost')
    actual = source.projected([(a, source.variables['a']), (b, source.variables['b'])],
                              signed_cost=cost)
    sign = 1 if direction == 'minimize' else -1
    expected = z3.Or(*[z3.And(a == literal(x), b == literal(y),
                              cost == sign*(len(x)+len(y)))
                       for x in subsets([-1, 0, 1]) for y in subsets([0, 1, 2])
                       if set(x) <= set(y) and y])
    equivalent(actual, expected)
    for wrong in [z3.IsMember(-1, b), z3.IsMember(2, a), cost == sign*7]:
        solver = z3.Solver(); solver.add(actual, wrong)
        assert solver.check() == z3.unsat


def test_empty_carrier_and_unbounded_set_remain_distinct():
    empty, unrestricted = [z3.FreshConst(z3.SetSort(z3.IntSort()), name)
                           for name in ['empty', 'unrestricted']]
    source = module.Source({'empty': empty, 'unrestricted': unrestricted}, {},
                           [empty == literal([]), z3.IsMember(17, unrestricted)],
                           None, 'satisfy', (), finite_set_domains={empty.get_id(): ()})
    a, b = [z3.FreshConst(z3.SetSort(z3.IntSort()), name) for name in ['a', 'b']]
    actual = source.projected([(a, empty), (b, unrestricted)])
    equivalent(actual, z3.And(a == literal([]), z3.IsMember(17, b)))


def capture_projection(monkeypatch):
    captured = {}
    def capture(body, private, public):
        captured.update(body=body, private=list(private), public=list(public))
        return SimpleNamespace(body=body, private_variables=tuple(private))
    monkeypatch.setattr(module, 'project_observed_constants', capture)
    return captured


@pytest.mark.parametrize('aliases', [False, True])
def test_private_order_member_append_order_and_freshness(monkeypatch, aliases):
    scalar = [z3.FreshInt('scalar') for _ in range(3)]
    a, b = [z3.FreshConst(z3.SetSort(z3.IntSort()), name) for name in ['a', 'b']]
    variables = {'u0': scalar[0], 'a': a, 'u1': scalar[1], 'b': b, 'u2': scalar[2]}
    if aliases:
        variables['alias_a'] = a
    source = module.Source(variables, {}, [], None, 'satisfy', (),
                           finite_set_domains={a.get_id(): (-2, 3), b.get_id(): (7,)})
    captured = capture_projection(monkeypatch)
    created = []
    fresh = z3.FreshConst
    def record(sort, prefix='c'):
        value = fresh(sort, prefix)
        created.append(value)
        return value
    monkeypatch.setattr(z3, 'FreshConst', record)
    source.projected([])
    assert [v.get_id() for v in captured['private']] == [v.get_id() for v in scalar+created]
    assert len(created) == (5 if aliases else 3)
    assert len({v.get_id() for v in created}) == len(created)
    assert all(z3.is_bool(v) for v in created)
    assert not {v.get_id() for v in variables.values()} & {v.get_id() for v in created}


def test_many_set_carriers_do_not_rescan_appended_members(monkeypatch):
    variables = {f's{i}': z3.FreshConst(z3.SetSort(z3.IntSort()), 'set') for i in range(96)}
    variables.update({f'x{i}': z3.FreshInt('scalar') for i in range(96)})
    carriers = {v.get_id(): tuple(range(16)) for name, v in variables.items() if name.startswith('s')}
    source = module.Source(variables, {}, [], None, 'satisfy', (), finite_set_domains=carriers)
    captured = capture_projection(monkeypatch)
    calls = 0
    original = z3.AstRef.eq
    def count(self, other):
        nonlocal calls
        calls += 1
        return original(self, other)
    monkeypatch.setattr(z3.AstRef, 'eq', count)
    source.projected([])
    # The old successive removal scanned over 85,000 private/member terms.
    assert calls <= 4*(len(variables)+sum(map(len, carriers.values())))
    assert len(captured['private']) == 96 + 96*16
