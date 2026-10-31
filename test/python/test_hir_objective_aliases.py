"""Objective aliases are recorded spellings, never inferred objectives."""
from copy import deepcopy
import hashlib
import json

import pytest
import z3

import somtparser as sp
from somtparser.hir import hir_schema
from somtparser.hir_canonical import canonicalize_hir
from somtparser.natural_language import Candidate, ModelError
from test_hir_provider_forms import replay_ledger


def model(sense):
    return {
        'schema': 'somt-hir-model-v1', 'language': 'hir',
        'decision': 'optimization',
        'declarations': [dict(name='x', sort='Int', lower=-2, upper=3)],
        'functions': [], 'constraints': [],
        'objectives': [dict(sense=sense, expr={'var': 'x'}, span=[0, 12])],
        'objective_order': 'single', 'goal': None,
        'assumptions': [], 'unresolved': [],
    }


@pytest.mark.parametrize('alias,canonical,optimum', [
    ('min', 'minimize', -2), ('max', 'maximize', 3),
])
def test_exact_objective_alias_keeps_direction_digest_and_replay(alias, canonical, optimum):
    raw = model(alias)
    before = deepcopy(raw)
    fixed, ledger = canonicalize_hir(raw)
    assert raw == before
    assert fixed['objectives'][0]['sense'] == canonical
    assert replay_ledger(raw, ledger) == fixed
    assert canonicalize_hir(fixed) == (fixed, [])
    assert ledger == [dict(path='/objectives/0/sense',
                           rule='explicit-objective-sense-alias',
                           before=alias, after=canonical)]
    candidate = sp.propose_nl('x' * 12, language='hir', provider=lambda _: raw)
    assert candidate.valid, candidate.diagnostics
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert restored.normalization_ledger == ledger
    result = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert result.ok, result.diagnostics
    solver = z3.Optimize()
    solver.from_string(result.to_smt2())
    assert solver.check() == z3.sat
    assert solver.model().eval(z3.Int('x')).as_long() == optimum
    tampered = json.loads(candidate.to_json())
    tampered['normalization_ledger'][0]['after'] = (
        'maximize' if canonical == 'minimize' else 'minimize')
    with pytest.raises(ModelError, match='digest'):
        Candidate.from_json(json.dumps(tampered))


@pytest.mark.parametrize('sense', [
    'minimum', 'less', 'MIN', 'maximize?', True, None, {'min': True},
])
def test_unknown_or_ambiguous_objective_directions_are_not_guessed(sense):
    raw = model(sense)
    fixed, ledger = canonicalize_hir(raw)
    assert fixed == raw and not ledger
    assert not sp.propose_nl('x' * 12, language='hir', provider=lambda _: raw).valid


def test_objective_normalization_does_not_rewrite_context_or_infer_an_objective():
    raw = model('min')
    raw['context'] = {'sense': 'max'}
    raw['data'] = {'sense': 'min'}
    fixed, ledger = canonicalize_hir(raw)
    assert fixed['context'] == raw['context'] and fixed['data'] == raw['data']
    assert [entry['path'] for entry in ledger] == ['/objectives/0/sense']
    raw['objectives'] = []
    raw['decision'] = 'satisfiability'
    assert canonicalize_hir(raw) == (raw, [])
    raw = model('min')
    raw['unresolved'] = ['The text did not specify an objective.']
    candidate = sp.propose_nl('x' * 12, language='hir', provider=lambda _: raw)
    assert not candidate.valid
    assert candidate.model['unresolved'] == raw['unresolved']


def test_published_objective_schema_names_canonical_directions():
    item = hir_schema()['properties']['objectives']['items']
    assert item['properties']['sense']['enum'] == ['minimize', 'maximize']


@pytest.mark.parametrize('alias', ['min', 'max'])
def test_loading_an_archived_candidate_does_not_apply_new_alias_rules(alias):
    raw = model(alias)
    source = 'x' * 12
    payload = dict(source=source, model=raw, provider='frozen-provider')
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True,
                                      separators=(',', ':')).encode()).hexdigest()
    envelope = dict(payload, schema='somt-nl-candidate-v1', digest=digest,
                    source_sha256=hashlib.sha256(source.encode()).hexdigest())
    restored = Candidate.from_json(json.dumps(envelope))
    assert restored.digest == digest
    assert restored.model == raw
    assert not restored.normalization_ledger
    assert not restored.valid


def test_mixed_lexicographic_directions_keep_order_and_independent_optimum():
    raw = model('min')
    raw['declarations'].append(dict(name='y', sort='Int', lower=-2, upper=3))
    raw['objectives'].append(dict(sense='max', expr={'var': 'y'}, span=[0, 12]))
    raw['objective_order'] = 'lexicographic'
    raw['constraints'] = [dict(expr={'op': 'eq', 'args': [
        {'op': 'add', 'args': [{'var': 'x'}, {'var': 'y'}]},
        {'literal': 1, 'sort': 'Int'}]}, span=[0, 12])]
    received = []

    def provider(request):
        received.append(request['schema']['properties']['objectives']['items'])
        return raw

    candidate = sp.propose_nl('x' * 12, language='hir', provider=provider)
    assert candidate.valid, candidate.diagnostics
    assert received[0]['properties']['sense']['enum'] == ['minimize', 'maximize']
    assert [entry['path'] for entry in candidate.normalization_ledger] == [
        '/objectives/0/sense', '/objectives/1/sense']
    translated = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert translated.ok, translated.diagnostics
    solver = z3.Optimize()
    solver.from_string(translated.to_smt2())
    assert solver.check() == z3.sat
    assert solver.model().eval(z3.Int('x')).as_long() == -2
    assert solver.model().eval(z3.Int('y')).as_long() == 3


def test_conflicting_objective_metadata_is_not_normalized_away():
    raw = model('min')
    raw['objectives'][0]['direction'] = 'maximize'
    assert canonicalize_hir(raw) == (raw, [])
    assert not sp.propose_nl('x' * 12, language='hir', provider=lambda _: raw).valid
