"""Provider scalar syntax preserves exact sorts, expression slots and snapshots."""
from copy import deepcopy
import hashlib
import json
import shutil
import subprocess

import pytest
import z3

import somtparser as sp
from somtparser.hir import build_hir
from somtparser.hir_canonical import canonicalize_hir
from somtparser.hir_provider_forms import adapt_provider_forms
from somtparser.natural_language import Candidate, ModelError
from test_hir_provider_forms import replay_ledger


SOURCE = 'Selected formal interpretation.'


def model(expr, declarations=None):
    return dict(schema='somt-hir-model-v1', language='hir',
                decision='satisfiability', declarations=declarations or [],
                functions=[], constraints=[dict(expr=expr, span=[0, len(SOURCE)])],
                objectives=[], objective_order='single', goal=None,
                assumptions=[], unresolved=[], context={})


def op(name, *args):
    return {'op': name, 'args': list(args)}


def candidate_for(raw):
    # Context belongs to the caller, not a provider-controlled model field.
    # Keep the original model intact for canonicalization/digest comparisons.
    proposed = deepcopy(raw)
    context = proposed.pop('context', {})
    return sp.propose_nl(SOURCE, language='hir', context=context,
                         provider=lambda _: proposed)


def propose(raw):
    candidate = candidate_for(raw)
    assert candidate.valid, candidate.diagnostics
    assert Candidate.from_json(candidate.to_json()).digest == candidate.digest
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert result.ok, result.diagnostics
    return candidate, result


def same(script, expected):
    actual = z3.And(*z3.parse_smt2_string(script))
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat, solver.reason_unknown()


@pytest.mark.parametrize('value,sort', [
    (0, 'Int'), (-7, 'Int'), (10**100, 'Int'), (True, 'Bool'), (False, 'Bool'),
])
def test_exact_scalar_expression_type_value_and_snapshot(value, sort):
    raw = model(op('eq', {'var': 'x'}, value), [dict(name='x', sort=sort)])
    before = deepcopy(raw)
    fixed, ledger = canonicalize_hir(raw)
    assert raw == before
    assert ledger == [dict(path='/constraints/0/expr/args/1',
                           rule='exact-JSON-scalar-expression', before=value,
                           after=dict(literal=value, sort=sort))]
    assert replay_ledger(raw, ledger) == fixed
    assert canonicalize_hir(fixed) == (fixed, [])
    candidate, result = propose(raw)
    assert candidate.model == fixed
    assert candidate.normalization_ledger == ledger
    x = z3.Bool('x') if sort == 'Bool' else z3.Int('x')
    same(result.to_smt2(), x == value)
    modified = json.loads(candidate.to_json())
    modified['normalization_ledger'][0]['after']['literal'] = 'changed'
    with pytest.raises(ModelError, match='digest'):
        Candidate.from_json(json.dumps(modified))


@pytest.mark.parametrize('value', [1.5, '5', 'true', None, [], [5]])
def test_ambiguous_or_inexact_expression_payloads_are_not_guessed(value):
    raw = model(op('eq', {'var': 'x'}, value), [dict(name='x', sort='Int')])
    assert canonicalize_hir(raw) == (raw, [])
    assert not candidate_for(raw).valid


@pytest.mark.parametrize('value,sort', [({'var': 'x'}, 'Int'), (True, 'Int'), (1, 'Bool')])
def test_explicit_typed_literals_are_not_reinterpreted(value, sort):
    raw = model(op('eq', {'var': 'x'}, dict(literal=value, sort=sort)),
                [dict(name='x', sort='Int')])
    assert canonicalize_hir(raw) == (raw, [])
    assert not candidate_for(raw).valid


def test_numeric_and_boolean_metadata_and_opaque_data_are_unchanged():
    expr = dict(cp='table', items=[{'var': 'x'}, 2], tuples=[[1, 2], [3, 4]], positive=True)
    raw = model(expr, [dict(name='x', sort='Int', lower=-4, upper=9)])
    raw['data'] = {'opaque': [True, 1, 1.5, '7', {'op': 'add', 'args': [1, 2]}]}
    raw['context'] = {'meaning': '7 remains text'}
    fixed, ledger = adapt_provider_forms(raw)
    assert fixed['data'] == raw['data']
    assert fixed['context'] == raw['context']
    assert fixed['declarations'] == raw['declarations']
    assert fixed['constraints'][0]['span'] == raw['constraints'][0]['span']
    assert fixed['constraints'][0]['expr']['tuples'] == [[1, 2], [3, 4]]
    assert fixed['constraints'][0]['expr']['positive'] is True
    assert [entry['path'] for entry in ledger] == ['/constraints/0/expr/items/1']
    assert replay_ledger(raw, ledger) == fixed
    _, result = propose(raw)
    same(result.to_smt2(), z3.Int('x') == 1)


def test_unknown_or_malformed_parent_objects_remain_untouched():
    for expr in [{'mystery': [5, True]}, {'op': 'unknown', 'args': [5, True]},
                 {'op': 'eq', 'args': [5]}, {'literal': {'add': [1, 2]}, 'sort': 'Int'},
                 {'const_array': {'value': 5}}, {'tuple': 5}]:
        raw = model(expr)
        assert adapt_provider_forms(raw) == (raw, [])


def test_fold_wrapper_and_arithmetic_keep_exact_integer_values():
    fold = {'finite_fold': dict(fold='sum', var='i', range=[0, 3], body=5)}
    raw = model(op('eq', {'var': 'x'}, fold), [dict(name='x', sort='Int')])
    fixed, ledger = canonicalize_hir(raw)
    assert replay_ledger(raw, ledger) == fixed
    assert fixed['constraints'][0]['expr']['args'][1]['range'] == [0, 3]
    _, result = propose(raw)
    same(result.to_smt2(), z3.Int('x') == 15)


@pytest.mark.parametrize('value', [True, False])
@pytest.mark.parametrize('tagged', [True, False])
def test_quantifier_constructor_aliases_preserve_boolean_body(value, tagged):
    binders = [dict(name='i', sort='Int')]
    expr = (dict(op='forall', binders=binders, body=value) if tagged
            else dict(forall=binders, body=value))
    raw = model(expr)
    fixed, ledger = canonicalize_hir(raw)
    assert replay_ledger(raw, ledger) == fixed
    assert fixed['constraints'][0]['expr']['binders'] == binders
    _, result = propose(raw)
    same(result.to_smt2(), z3.BoolVal(value))


@pytest.mark.parametrize('value', [True, False])
def test_unary_boolean_alias_has_one_explicit_boolean_operand(value):
    raw = model({'not': value})
    fixed, ledger = canonicalize_hir(raw)
    assert replay_ledger(raw, ledger) == fixed
    _, result = propose(raw)
    same(result.to_smt2(), z3.BoolVal(not value))


def test_lookup_default_and_index_use_expression_types_only():
    raw = model(op('eq', {'var': 'x'}, {
        'data_lookup': dict(data='table', indices=[2], default=-7)}),
        [dict(name='x', sort='Int')])
    raw['data'] = {'table': [4, 8]}
    fixed, ledger = canonicalize_hir(raw)
    assert fixed['data'] == raw['data']
    assert replay_ledger(raw, ledger) == fixed
    _, result = propose(raw)
    same(result.to_smt2(), z3.Int('x') == -7)


def test_constant_array_constructor_recurses_only_into_value():
    raw = model(op('eq', op('select', {
        'const_array': {'index_sort': 'Int', 'value': 7}}, {'var': 'i'}), 7),
        [dict(name='i', sort='Int')])
    fixed, ledger = canonicalize_hir(raw)
    assert replay_ledger(raw, ledger) == fixed
    assert fixed['constraints'][0]['expr']['args'][0]['args'][0]['const_array']['index_sort'] == 'Int'
    _, result = propose(raw)
    same(result.to_smt2(), z3.BoolVal(True))


@pytest.mark.parametrize('indices', [[], [1, 0, 1]])
def test_tuple_projection_indices_remain_metadata(indices):
    value = {'tuple': [True, 7]}
    projection = {'op_indexed': dict(op='tuple.project', indices=indices, args=[value])}
    expected = {'tuple': [7, True, 7]} if indices else {'tuple_unit': True}
    raw = model(op('not', op('eq', projection, expected)))
    fixed, ledger = canonicalize_hir(raw)
    assert replay_ledger(raw, ledger) == fixed
    rewritten = fixed['constraints'][0]['expr']['args'][0]['args'][0]['op_indexed']
    assert rewritten['indices'] == indices
    assert all('/indices/' not in item['path'] for item in ledger)
    assert all('tuple_unit' not in item['path'] for item in ledger)
    _, result = propose(raw)
    executable = shutil.which('cvc5')
    if executable is None:
        pytest.skip('cvc5 is required to independently check native tuple semantics')
    check = subprocess.run([executable, '--lang=smt2', '--tlimit=5000'],
                           input=result.to_smt2(), capture_output=True, text=True, timeout=10)
    assert check.returncode == 0, check.stdout + check.stderr
    assert [line for line in check.stdout.splitlines()
            if line in {'sat', 'unsat', 'unknown'}] == ['unsat']


@pytest.mark.parametrize('value,sort', [(7, 'Int'), (True, 'Bool')])
def test_archived_candidate_loading_keeps_original_scalar_syntax(value, sort):
    raw = model(op('eq', {'var': 'x'}, value), [dict(name='x', sort=sort)])
    payload = dict(source=SOURCE, model=raw, provider='frozen-provider')
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True,
                                      separators=(',', ':')).encode()).hexdigest()
    envelope = dict(payload, schema='somt-nl-candidate-v1', digest=digest,
                    source_sha256=hashlib.sha256(SOURCE.encode()).hexdigest())
    restored = Candidate.from_json(json.dumps(envelope))
    assert restored.model == raw
    assert restored.digest == digest
    assert not restored.valid and not restored.normalization_ledger
    with pytest.raises(ModelError, match='expression must be an object'):
        build_hir(raw, SOURCE)


def test_integer_in_boolean_context_is_still_a_type_error():
    raw = model(op('and', 1, True))
    candidate = candidate_for(raw)
    assert not candidate.valid
    assert candidate.model['constraints'][0]['expr']['args'][0] == dict(literal=1, sort='Int')


@pytest.mark.parametrize('operator,arguments,expected,sort', [
    ('sum', [2, 3], 5, 'Int'), ('min', [-2, 3], -2, 'Int'),
    ('minimum', [-2, 3], -2, 'Int'), ('max', [-2, 3], 3, 'Int'),
    ('maximum', [-2, 3], 3, 'Int'), ('abs', [-3], 3, 'Int'),
    ('allDifferent', [2, 3], True, 'Bool'),
])
def test_canonical_operator_aliases_visit_exact_scalar_operands(operator, arguments, expected, sort):
    raw = model(op('eq', {'var': 'x'}, op(operator, *arguments)),
                [dict(name='x', sort=sort)])
    fixed, ledger = canonicalize_hir(raw)
    assert replay_ledger(raw, ledger) == fixed
    assert canonicalize_hir(fixed) == (fixed, [])
    _, result = propose(raw)
    x = z3.Bool('x') if sort == 'Bool' else z3.Int('x')
    same(result.to_smt2(), x == expected)
