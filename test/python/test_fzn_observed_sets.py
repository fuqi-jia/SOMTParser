"""Whole-set observation bridges eliminate only their own private witnesses."""
from types import SimpleNamespace

import pytest
import z3

from tools.semantic_checks.source_oracles import fzn_json_source as module


def literal(values):
    result = z3.EmptySet(z3.IntSort())
    for value in values:
        result = z3.SetAdd(result, value)
    return result


def source(variables, constraints=(), solve=None):
    return module.read_source(dict(version='1.0', variables=variables,
        arrays={}, constraints=list(constraints), output=list(variables),
        solve=solve or dict(method='satisfy')))


def check(formula, expected):
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == expected


def capture(monkeypatch):
    recorded = {}
    def projected(body, private, public):
        recorded.update(body=body, private=list(private), public=list(public))
        return SimpleNamespace(body=body, private_variables=tuple(private))
    monkeypatch.setattr(module, 'project_observed_constants', projected)
    return recorded


def test_two_public_aliases_keep_equality_and_complete_carrier():
    flat = source({'s': dict(type='set of int', domain=[[-1, 1]])})
    a, b = [z3.FreshConst(z3.SetSort(z3.IntSort()), name) for name in ('a', 'b')]
    actual = flat.projected([(a, flat.variables['s']), (b, flat.variables['s'])])
    expected = z3.And(a == b, z3.IsSubset(a, literal([-1, 0, 1])))
    check(z3.Xor(actual, expected), z3.unsat)
    check(z3.And(actual, a != b), z3.unsat)
    check(z3.And(actual, z3.IsMember(2, a)), z3.unsat)
    check(z3.And(actual, a == literal([-1, 1]), b == literal([-1, 1])), z3.sat)


@pytest.mark.parametrize('carrier', [(), (-2, 4)])
def test_metadata_only_carrier_stays_complete(carrier):
    private, public = [z3.FreshConst(z3.SetSort(z3.IntSort()), name)
                       for name in ('private', 'public')]
    flat = module.Source({'s': private}, {}, [], None, 'satisfy', (),
                         finite_set_domains={private.get_id(): carrier})
    actual = flat.projected([(public, private)])
    check(z3.Xor(actual, z3.IsSubset(public, literal(carrier))), z3.unsat)
    check(z3.And(actual, z3.IsMember(17, public)), z3.unsat)


@pytest.mark.parametrize('direction,sign', [('minimize', 1), ('maximize', -1)])
def test_signed_cost_and_cross_set_relation_remain_complete(direction, sign):
    flat = source({'a': dict(type='set of int', domain=[[0, 2]]),
                   'b': dict(type='set of int', domain=[[1, 3]]),
                   'ca': dict(type='int', domain=[[0, 3]]),
                   'cb': dict(type='int', domain=[[0, 3]]),
                   'cost': dict(type='int', domain=[[0, 6]])}, [
        dict(id='set_subset', args=['a', 'b']),
        dict(id='set_card', args=['a', 'ca']),
        dict(id='set_card', args=['b', 'cb']),
        dict(id='int_plus', args=['ca', 'cb', 'cost'])],
        dict(method=direction, objective='cost'))
    a, b = [z3.FreshConst(z3.SetSort(z3.IntSort()), name) for name in ('a', 'b')]
    cost = z3.FreshInt('cost')
    actual = flat.projected([(a, flat.variables['a']), (b, flat.variables['b'])],
                            signed_cost=cost)
    valid = z3.And(a == literal([1]), b == literal([1, 3]))
    check(z3.And(actual, valid, cost == sign*3), z3.sat)
    check(z3.And(actual, valid, cost != sign*3), z3.unsat)
    check(z3.And(actual, a == literal([0]), b == literal([1])), z3.unsat)
    check(z3.And(actual, z3.IsMember(3, a)), z3.unsat)


@pytest.mark.parametrize('public_values,expected', [([], False), ([0], True),
                                                   ([1], True), ([0, 1], True)])
def test_unobserved_set_keeps_its_existential_witness(public_values, expected):
    flat = source({'observed': dict(type='set of int', domain=[[0, 1]]),
                   'hidden': dict(type='set of int', domain=[[0, 1]])}, [
        dict(id='set_subset', args=['hidden', 'observed']),
        dict(id='set_card', args=['hidden', 1])])
    public = z3.FreshConst(z3.SetSort(z3.IntSort()), 'public')
    actual = flat.projected([(public, flat.variables['observed'])])
    check(z3.And(actual, public == literal(public_values)), z3.sat if expected else z3.unsat)


@pytest.mark.parametrize('form', ['union', 'conditional', 'indexed'])
def test_compound_observation_does_not_define_private_set(monkeypatch, form):
    flat = source({'s': dict(type='set of int', domain=[[0, 1]])})
    public = z3.FreshConst(z3.SetSort(z3.IntSort()), 'public')
    recorded = capture(monkeypatch)
    value = flat.variables['s']
    if form == 'union':
        value = z3.SetUnion(value, literal([2]))
    elif form == 'conditional':
        value = z3.If(z3.FreshBool('condition'), value, literal([2]))
    else:
        table = z3.Store(z3.K(z3.IntSort(), literal([2])), 0, value)
        value = z3.Select(table, z3.FreshInt('index'))
    flat.projected([(public, value)])
    assert len(recorded['private']) == 2
    assert all(z3.is_bool(term) for term in recorded['private'])
    assert not any(term.eq(public) for term in recorded['private'])


def test_unbounded_set_stays_on_existing_projection_path(monkeypatch):
    private, public = [z3.FreshConst(z3.SetSort(z3.IntSort()), name)
                       for name in ('private', 'public')]
    flat = module.Source({'s': private}, {}, [z3.IsMember(17, private)],
                         None, 'satisfy', ())
    recorded = capture(monkeypatch)
    flat.projected([(public, private)])
    assert len(recorded['private']) == 1 and recorded['private'][0].eq(private)


def test_direct_observation_generator_and_repeated_private_alias(monkeypatch):
    flat = source({'s': dict(type='set of int', domain=[[0, 1]])})
    flat.variables['alias'] = flat.variables['s']
    a, b = [z3.FreshConst(z3.SetSort(z3.IntSort()), name) for name in ('a', 'b')]
    recorded = capture(monkeypatch)
    actual = flat.projected(iter([(a, flat.variables['s']), (b, flat.variables['alias'])]))
    assert not recorded['private']
    check(z3.And(actual, a != b), z3.unsat)
    check(z3.And(actual, a == literal([0]), b == literal([0])), z3.sat)


def test_many_observed_carriers_create_no_member_witnesses(monkeypatch):
    flat = source({f's{i}': dict(type='set of int', domain=[[0, 15]]) for i in range(96)})
    public = [z3.FreshConst(z3.SetSort(z3.IntSort()), 'public') for _ in range(96)]
    recorded = capture(monkeypatch)
    def unexpected(*args, **kwargs):
        raise AssertionError('direct set observations need no fresh membership witnesses')
    monkeypatch.setattr(z3, 'FreshConst', unexpected)
    flat.projected(zip(public, flat.variables.values()))
    assert not recorded['private']
    assert len(recorded['public']) == 96
