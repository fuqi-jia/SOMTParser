"""Naming failures remain rejections with precise, repairable feedback."""
import copy

import pytest
from somtparser._nl_model import ModelError, name
from somtparser.hir import HirBuilder, build_hir, hir_api
from somtparser.natural_language import propose_nl_with_repair


def minimal():
    return dict(schema='somt-hir-model-v1', language='hir', decision='satisfiability',
                declarations=[], functions=[], constraints=[], objectives=[],
                objective_order='single', goal=None, assumptions=[], unresolved=[])


@pytest.mark.parametrize('identifier', ['2sum', '4sum'])
def test_digit_start_reports_original_json_path_and_bad_name(identifier):
    model = minimal()
    model['declarations'] = [dict(name=identifier, sort='Int')]
    saved = copy.deepcopy(model)
    with pytest.raises(ModelError) as caught:
        build_hir(model, 'x')
    assert caught.value.path == 'declarations[0].name'
    assert repr(identifier) in str(caught.value)
    assert 'cannot start with a digit' in str(caught.value)
    assert model == saved


@pytest.mark.parametrize('identifier', ['hyrax', '_2sum', '变量', 'épreuve', 'x' * 128])
def test_existing_legal_identifier_spellings_remain_accepted(identifier):
    assert name(identifier, 'name') == identifier


@pytest.mark.parametrize('identifier,detail', [('', 'must not be empty'),
    ('x' * 129, 'length is 129'), ('bad name', 'Unicode identifier syntax'),
    (3, 'must be a string, got int'), ('TRUE', 'reserved expression identifier')])
def test_other_rejection_reasons_remain_explicit(identifier, detail):
    with pytest.raises(ModelError) as caught:
        name(identifier, 'declarations[2].name')
    assert caught.value.path == 'declarations[2].name'
    assert detail in str(caught.value)


@pytest.mark.parametrize('first,second', [('declaration', 'function'), ('function', 'declaration')])
def test_cross_kind_collision_names_the_existing_binding_and_does_not_mutate(first, second):
    builder = HirBuilder()
    def add(kind, identifier):
        if kind == 'function':
            builder.declare_function(identifier, ['Int'], 'Bool', path='functions[4]')
        else:
            builder.declare(identifier, 'Int', path='declarations[0]')
    add(first, 'hyrax')
    before = (set(builder.symbols), set(builder.functions))
    with pytest.raises(ModelError) as caught:
        add(second, 'hyrax')
    assert caught.value.path == ('functions[4].name' if second == 'function' else 'declarations[0].name')
    assert "name collision: " + second + " 'hyrax'" in str(caught.value)
    assert 'existing ' + first in str(caught.value)
    assert 'one namespace' in str(caught.value)
    assert before == (set(builder.symbols), set(builder.functions))
    add(second, 'is_hyrax' if second == 'function' else 'hyrax_entity')
    assert builder.translate().ok


@pytest.mark.parametrize('kind', ['declaration', 'function'])
def test_same_kind_duplicates_retain_classification(kind):
    builder = HirBuilder()
    def add():
        if kind == 'function':
            builder.declare_function('same', ['Int'], 'Bool')
        else:
            builder.declare('same', 'Int')
    add()
    with pytest.raises(ModelError, match='duplicate ' + kind + ': same'):
        add()


@pytest.mark.parametrize('identifier,kind', [('mkBox', 'datatype constructor'), ('unbox', 'datatype selector')])
def test_datatype_term_collisions_name_the_correct_kind(identifier, kind):
    builder = HirBuilder()
    builder.declare_datatype(dict(name='Box', constructors=[dict(name='mkBox', fields=[dict(name='unbox', sort='Int')])]))
    with pytest.raises(ModelError, match='existing ' + kind):
        builder.declare_function(identifier, ['Int'], 'Bool')


def test_public_api_exposes_unicode_names_and_namespace_without_unique_name_assumption():
    semantics = hir_api()['semantics']
    assert 'str.isidentifier()' in semantics['identifiers']
    assert 'one term namespace' in semantics['term_namespace']
    assert 'unique-name assumption' in semantics['term_namespace']


def test_existing_repair_api_passes_precise_feedback_without_renaming_original():
    original = minimal()
    original['declarations'] = [dict(name='2sum', sort='Int')]
    context = {'source_note': '2sum is the source name'}
    seen = []
    def provider(request):
        seen.append(copy.deepcopy(request))
        if 'repair' not in request:
            return original
        feedback = request['repair']
        assert feedback['previous_candidate']['declarations'][0]['name'] == '2sum'
        assert 'declarations[0].name' in feedback['diagnostics'][0]
        assert 'cannot start with a digit' in feedback['diagnostics'][0]
        replacement = copy.deepcopy(feedback['previous_candidate'])
        replacement['declarations'][0]['name'] = 'two_sum'
        return replacement
    trace = propose_nl_with_repair('Choose integer 2sum.', provider=provider,
                                   context=context, language='hir', max_attempts=2)
    assert len(trace.attempts) == 2
    assert not trace.attempts[0].valid and trace.attempts[1].valid
    assert original['declarations'][0]['name'] == '2sum'
    assert seen[0]['context'] == seen[1]['context'] == context
    assert 'cannot start with a digit' in seen[0]['instruction']
    assert 'unique-name assumption' in seen[0]['instruction']
    assert trace.attempts[0].digest != trace.attempts[1].digest
