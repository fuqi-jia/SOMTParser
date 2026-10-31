"""Structured repair locates validator evidence without choosing source meaning."""
import copy

import pytest

from somtparser._nl_feedback import validation_feedback
from somtparser.natural_language import Candidate, _candidate, propose_nl_with_repair


SOURCE = '猫：Choose integer x equal to 3.'


def model():
    return dict(schema='somt-hir-model-v1', language='hir', decision='satisfiability',
                declarations=[dict(name='x', sort='Int')], functions=[],
                constraints=[dict(expr={'op': 'eq', 'args': [
                    {'var': 'x'}, {'literal': 3, 'sort': 'Int'}]}, span=[2, len(SOURCE)])],
                objectives=[], objective_order='single', goal=None,
                assumptions=[], unresolved=[])


@pytest.mark.parametrize('case,path,pointer,value_type', [
    ('literal', 'constraints[0].expr.args[1].literal', '/constraints/0/expr/args/1/literal', 'boolean'),
    ('condition', 'constraints[0].expr.args[1].args[0]', '/constraints/0/expr/args/1/args/0', 'object'),
])
def test_real_hir_repair_gets_exact_field_and_unicode_source_annotation(case, path, pointer, value_type):
    bad = model()
    if case == 'literal':
        bad['constraints'][0]['expr']['args'][1]['literal'] = True
    else:
        bad['constraints'][0]['expr']['args'][1] = {'op': 'ite', 'args': [
            {'var': 'x'}, {'literal': 3, 'sort': 'Int'}, {'literal': 3, 'sort': 'Int'}]}
    original = copy.deepcopy(bad)
    seen = []

    def provider(request):
        seen.append(copy.deepcopy(request))
        if 'repair' not in request:
            return bad
        repair = request['repair']
        detail, = repair['diagnostic_details']
        assert detail['kind'] == 'construction'
        assert detail['path'] == path and detail['json_pointer'] == pointer
        assert detail['value_present'] and detail['value_type'] == value_type
        assert detail['source_span'] == [2, len(SOURCE)]
        assert detail['source_excerpt'] == SOURCE[2:]
        assert detail['source_span_origin'] == 'candidate-annotation'
        assert repair['diagnostics'][detail['diagnostic_index']].startswith(path + ': ')
        if case == 'literal':
            assert detail['value'] is True
        assert not {'gold', 'reference', 'reference_model', 'solver', 'counterexample'} & request.keys()
        detail['path'] = 'provider mutation'
        return model()

    trace = propose_nl_with_repair(SOURCE, provider=provider, max_attempts=2,
                                  context={'domain': 'Unbounded exact integers.'})
    assert not trace.attempts[0].valid and trace.attempts[1].valid
    assert trace.attempts[0].diagnostic_details[0]['path'] == path
    assert seen[0]['source'] == seen[1]['source'] == SOURCE
    assert seen[0]['context'] == seen[1]['context']
    assert trace.attempts[0].model['constraints'] == original['constraints']
    assert bad == original


@pytest.mark.parametrize('prefix', [
    'model: unresolved interpretation: ',
    'unresolved: unresolved interpretations: ',
    'model: unresolved: ',
])
def test_all_existing_refusal_formats_keep_individual_entries_without_splitting_text(prefix):
    value = model()
    value['unresolved'] = ['scope A; scope B: both remain possible', 'A different existence reading']
    saved = copy.deepcopy(value)
    messages = [prefix + '; '.join(value['unresolved'])]
    details = validation_feedback(SOURCE, value, messages)
    assert [d['path'] for d in details] == ['unresolved[0]', 'unresolved[1]']
    assert [d['json_pointer'] for d in details] == ['/unresolved/0', '/unresolved/1']
    assert [d['message'] for d in details] == value['unresolved']
    assert all(d['diagnostic_index'] == 0 and d['kind'] == 'unresolved_interpretation' for d in details)
    assert all(d['source_span'] is None for d in details)
    assert value == saved


def test_notes_do_not_remove_or_reclassify_a_refusal_and_attempt_limit_still_applies():
    value = model()
    value['unresolved'] = ['Two quantifier scopes remain.']
    value['interpretation_notes'] = ['This sentence explains the selected syntax.']
    calls = []

    def provider(request):
        calls.append(copy.deepcopy(request))
        return value

    trace = propose_nl_with_repair(SOURCE, provider=provider, max_attempts=2)
    assert len(trace.attempts) == 2 and trace.stop_reason == 'attempt-limit'
    assert all(not c.valid and c.model['unresolved'] == value['unresolved'] for c in trace.attempts)
    assert calls[1]['repair']['diagnostic_details'][0]['kind'] == 'unresolved_interpretation'
    assert calls[1]['repair']['previous_candidate']['interpretation_notes'] == value['interpretation_notes']


def test_explanatory_unresolved_text_is_not_automatically_removed():
    value = model()
    value['unresolved'] = ['The explicitly stated existence sentence uses an existential quantifier.']
    candidate = _candidate(SOURCE, value, 'test')
    assert not candidate.valid
    assert candidate.model['unresolved'] == value['unresolved']
    assert candidate.diagnostic_details[0]['message'] == value['unresolved'][0]
    assert candidate.diagnostic_details[0]['kind'] == 'unresolved_interpretation'


def test_details_are_fresh_derived_views_and_legacy_envelope_digest_is_unchanged():
    value = model()
    value['constraints'][0]['expr']['args'][1]['literal'] = True
    candidate = _candidate(SOURCE, value, 'test')
    envelope, digest = candidate.to_json(), candidate.digest
    details = candidate.diagnostic_details
    details[0]['source_span'][0] = 999
    details[0]['message'] = 'mutated'
    restored = Candidate.from_json(envelope)
    assert restored.digest == digest and restored.to_json() == envelope
    assert restored.diagnostic_details == candidate.diagnostic_details
    assert candidate.diagnostic_details[0]['source_span'][0] == 2
    assert 'diagnostic_details' not in __import__('json').loads(envelope)


@pytest.mark.parametrize('span', [[-1, 5], [0, 9999], [3, 2], [True, 3], [0, 1.5]])
def test_invalid_candidate_annotations_do_not_produce_a_source_excerpt(span):
    value = model()
    value['constraints'][0]['span'] = span
    details = validation_feedback(SOURCE, value, ['constraints[0].expr.args[1]: bad operand'])
    assert details[0]['source_span'] is None
    assert 'source_excerpt' not in details[0]


@pytest.mark.parametrize('message', [
    'native-file.cpp: cannot construct expression',
    'constraints[__import__("os")]: malformed index',
    'failure mentions constraints[0].expr: no validator location',
])
def test_unrecognized_paths_remain_unlocated_instead_of_guessing_or_executing(message):
    detail, = validation_feedback(SOURCE, model(), [message])
    assert detail['path'] is None and detail['json_pointer'] is None
    assert detail['message'] == message and not detail['value_present']
    assert detail['source_span'] is None


def test_missing_field_retains_its_pointer_and_containing_annotation():
    detail, = validation_feedback(SOURCE, model(), ['constraints[0].expr.missing: expected field'])
    assert detail['json_pointer'] == '/constraints/0/expr/missing'
    assert not detail['value_present']
    assert detail['source_span'] == [2, len(SOURCE)]


def test_large_annotation_is_explicitly_truncated_without_changing_its_coordinates():
    source = '猫' * 800
    value = model()
    value['constraints'][0]['span'] = [0, len(source)]
    detail, = validation_feedback(source, value, ['constraints[0].expr: invalid expression'])
    assert detail['source_span'] == [0, 800]
    assert detail['source_excerpt'] == '猫' * 512 and detail['source_excerpt_truncated']
    assert detail['value_type'] == 'object' and 'value' not in detail
