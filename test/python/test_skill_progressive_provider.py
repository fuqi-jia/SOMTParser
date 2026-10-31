"""Demand-driven reads, unchanged source, bounded billing and complete accounting."""
from copy import deepcopy
import itertools
import json
from pathlib import Path
import sys

import jsonschema
import pytest

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'skills/somtparser-nl-smtlib/scripts'))
import progressive_provider as agent


class Backend:
    model='test-model'
    def __init__(self,replies):
        self.replies=iter(replies)
        self.requests=[]
        self.last_request=self.last_response_content=self.last_metadata=None
    def __call__(self,request):
        self.requests.append(deepcopy(request))
        self.last_request={'messages':[{'content':json.dumps(request)}]}
        self.last_response_content=self.last_metadata=None
        reply=next(self.replies)
        if isinstance(reply,Exception): raise reply
        self.last_response_content=json.dumps(reply)
        self.last_metadata={'usage':{'prompt_tokens':10,'completion_tokens':5,'total_tokens':15}}
        return deepcopy(reply)


@pytest.fixture
def protocol(monkeypatch):
    known={'core','arithmetic','arrays','omt','repair'}
    monkeypatch.setattr(agent,'capability_index',lambda route,request:[{'id':n} for n in sorted(known)])
    def packet(route,ids,request):
        if set(ids)-known:raise ValueError('unknown resource')
        view=deepcopy(request)
        view['instruction']='Keep the candidate contract.'
        view['schema']={'$defs':{'value':{'type':'integer'}},'type':'object','properties':{'n':{'$ref':'#/$defs/value'}},'required':['n'],'additionalProperties':False}
        return {'request':view,'loaded':list(ids),'snippets':{n:'only '+n for n in ids}}
    monkeypatch.setattr(agent,'materialize_capabilities',packet)
    clock=itertools.count(0,100)
    monkeypatch.setattr(agent.time,'monotonic',lambda:next(clock))
    return {'source':'Keep all original requirements.','source_sha256':'fixed','context':{'domain':'Int'},'language':'hir','schema':{}}


def test_select_then_generate_materializes_only_chosen_resources(tmp_path,protocol):
    backend=Backend([{'action':'lookup','resources':['core']},{'n':4}])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    assert wrapper(protocol)=={'n':4}
    first,second=backend.requests
    assert first['phase']=='resource_selection' and 'snippets' not in first
    assert second['resource_packet']['snippets']=={'core':'only core'}
    assert wrapper.last_metadata['usage']['total_tokens']==30
    assert wrapper.last_metadata['provider_calls']==2
    jsonschema.validate({'n':4},second['schema'])
    assert second['schema']['oneOf'][0]['required']==['n']
    assert 'action' not in second['schema']['oneOf'][0]['properties']
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate({'action':'candidate','model':{'n':4}},second['schema'])
    assert len(list((tmp_path/'skill-rounds').glob('*/provider-metadata.json')))==2
    for request in backend.requests:
        assert request['protocol']=='somt-skill-agent-v2'
        assert request['source']==protocol['source'] and request['context']==protocol['context']


def test_generation_index_and_lookup_schema_exclude_loaded_resources(tmp_path,protocol):
    backend=Backend([{'action':'lookup','resources':['core','arithmetic']},{'n':4}])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    wrapper(protocol)
    first,second=backend.requests
    assert not any(item['loaded'] for item in first['resource_index'])
    assert {item['id'] for item in second['resource_index'] if item['loaded']}=={'core','arithmetic'}
    lookup=second['schema']['oneOf'][1]
    assert set(lookup['properties']['resources']['items']['enum'])=={'arrays','omt','repair'}
    jsonschema.validate({'action':'lookup','resources':['arrays']},second['schema'])
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate({'action':'lookup','resources':['arithmetic']},second['schema'])


def test_repeated_small_model_lookup_has_actionable_diagnostic(tmp_path,protocol):
    selection={'action':'lookup','resources':['arithmetic','arrays','omt']}
    backend=Backend([selection,selection])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    with pytest.raises(agent.ProgressiveProtocolError,match='Resources already loaded') as caught:
        wrapper(protocol)
    message=str(caught.value)
    assert all(name in message for name in selection['resources'])
    assert 'contents are already included' in message and 'candidate directly' in message
    assert wrapper.last_metadata['provider_calls']==2
    assert len(backend.requests)==2


def test_all_resources_loaded_disables_lookup_branch(tmp_path,protocol):
    selection={'action':'lookup','resources':['core','arithmetic','arrays','omt','repair']}
    backend=Backend([selection,{'n':4}])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    assert wrapper(protocol)=={'n':4}
    schema=backend.requests[-1]['schema']
    assert schema['oneOf'][1] is False
    jsonschema.Draft202012Validator.check_schema(schema)
    jsonschema.validate({'n':4},schema)


def test_malformed_hybrid_wrapper_explains_correct_nesting_and_can_be_repaired(tmp_path,protocol):
    malformed={'action':'candidate','model':{'hir':{}},'smt_constraints':[]}
    native={'schema':'somt-nl-hybrid-v1','hir':{},'smt_constraints':[]}
    backend=Backend([{'action':'lookup','resources':['core']},malformed,native])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    proposal=dict(protocol,language='hybrid')
    with pytest.raises(agent.ProgressiveProtocolError,match='Malformed legacy candidate wrapper') as caught:
        wrapper(proposal)
    message=str(caught.value)
    assert 'smt_constraints' in message and 'inside model' in message
    assert 'expected a lookup' not in message
    repaired=deepcopy(proposal)
    repaired['repair']={'previous_candidate':malformed,'diagnostics':[message]}
    assert wrapper(repaired)==native
    assert wrapper.last_metadata['provider_calls']==1
    assert wrapper.last_metadata['total_provider_calls']==3
    assert backend.requests[-1]['repair']['previous_candidate']==malformed


def test_unwrapped_candidate_is_handed_to_native_authority_unchanged(tmp_path,protocol):
    # Deliberately ill-formed HIR is compiler feedback, not a lookup failure.
    native={'constraints':[{'expr':{'op':'var','args':['x']}}]}
    backend=Backend([{'action':'lookup','resources':['core']},native])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    assert wrapper(protocol)==native
    assert json.loads(wrapper.last_response_content)==native


@pytest.mark.parametrize('response',[
    {'action':'candidate','model':[]},
    {'action':'candidate'},
    {'action':'something_else','model':{}},
])
def test_other_wrapper_failures_do_not_masquerade_as_lookup_errors(tmp_path,protocol,response):
    backend=Backend([{'action':'lookup','resources':['core']},response])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    with pytest.raises(agent.ProgressiveProtocolError) as caught:
        wrapper(protocol)
    assert 'candidate' in str(caught.value)
    assert 'expected a lookup' not in str(caught.value)


def test_additional_lookup_and_outer_repair_preserve_source_and_count_each_call_once(tmp_path,protocol):
    backend=Backend([{'action':'lookup','resources':['core']},{'action':'lookup','resources':['arithmetic']},
                     {'action':'candidate','model':{'n':4}},{'action':'candidate','model':{'n':5}}])
    wrapper=agent.ProgressiveProvider(backend,tmp_path,max_calls=5)
    assert wrapper(protocol)=={'n':4}
    first=wrapper.last_metadata['usage']['total_tokens']
    repair=deepcopy(protocol)
    repair['repair']={'previous_candidate':{'n':4},'diagnostics':['construction error']}
    assert wrapper(repair)=={'n':5}
    second=wrapper.last_metadata['usage']['total_tokens']
    assert (first,second)==(45,15)
    assert wrapper.last_metadata['total_provider_calls']==4
    assert backend.requests[-1]['repair']==repair['repair']
    assert 'only arithmetic' in str(backend.requests[-1])


def test_repeated_or_unknown_lookup_stops_without_extra_calls(tmp_path,protocol):
    for name,replies in [('repeat',[{'action':'lookup','resources':['core']}]*2),
                         ('unknown',[{'action':'lookup','resources':['invented']}])]:
        backend=Backend(replies)
        wrapper=agent.ProgressiveProvider(backend,tmp_path/name)
        with pytest.raises(ValueError):wrapper(protocol)
        assert len(backend.requests)==len(replies)


def test_network_failure_is_not_retried(tmp_path,protocol):
    backend=Backend([TimeoutError('connection unknown')])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    with pytest.raises(TimeoutError):wrapper(protocol)
    assert len(backend.requests)==1
    assert wrapper.last_metadata['usage_unknown_calls']==1


def test_selection_repair_receives_bad_selection_diagnostic(tmp_path, protocol):
    backend=Backend([{'action':'lookup','resources':['invented']},
                     {'action':'lookup','resources':['core']},
                     {'action':'candidate','model':{'n':4}}])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    with pytest.raises(agent.ProgressiveProtocolError,match='unknown'):
        wrapper(protocol)
    repaired=deepcopy(protocol)
    repaired['repair']={'diagnostics':['unknown resource: invented'],
                        'instruction':'Return a replacement candidate.'}
    assert wrapper(repaired)=={'n':4}
    assert backend.requests[1]['phase']=='resource_selection'
    assert backend.requests[1]['repair']=={'diagnostics':['unknown resource: invented']}
    assert 'Keep the candidate contract.' in backend.requests[2]['instruction']


def test_budget_is_shared_with_repairs_and_binding_cannot_change(tmp_path,protocol):
    backend=Backend([{'action':'lookup','resources':['core']},{'action':'candidate','model':{'n':4}}])
    wrapper=agent.ProgressiveProvider(backend,tmp_path,max_calls=2)
    wrapper(protocol)
    with pytest.raises(agent.ProgressiveProtocolError,match='budget'):
        wrapper(protocol)
    assert wrapper.last_metadata['provider_calls'] == 0
    assert wrapper.last_metadata['usage_unknown_calls'] == 0
    assert wrapper.last_metadata['usage']['total_tokens'] == 0
    changed=dict(protocol,source='Replaced source.')
    with pytest.raises(agent.ProgressiveProtocolError,match='changed'):
        wrapper(changed)
    assert len(backend.requests)==2


def test_dialect_is_visible_at_selection_and_bound_across_repairs(tmp_path, protocol):
    proposal=dict(protocol,dialect='optimathsat')
    backend=Backend([{'action':'lookup','resources':['core']},{'action':'candidate','model':{'n':4}}])
    wrapper=agent.ProgressiveProvider(backend,tmp_path)
    wrapper(proposal)
    assert all(r['dialect']=='optimathsat' for r in backend.requests)
    with pytest.raises(agent.ProgressiveProtocolError,match='changed'):
        wrapper(dict(proposal,dialect='z3'))
    assert len(backend.requests)==2


@pytest.mark.parametrize('route', ['hir', 'hybrid', 'smtlib2'])
def test_real_capability_documents_reach_model_without_full_schema(tmp_path, monkeypatch, route):
    from ir2smt import get_request
    clock = itertools.count(0, 100)
    monkeypatch.setattr(agent.time, 'monotonic', lambda: next(clock))
    proposal = get_request('Choose an integer x at least 2.', {}, route, request_profile='compact')
    backend = Backend([{'action': 'lookup', 'resources': ['arithmetic', 'bool', 'semantics.core', 'template']},
                       {'action': 'candidate', 'model': {}}])
    wrapper = agent.ProgressiveProvider(backend, tmp_path / route)
    wrapper(proposal)
    request = backend.requests[-1]
    resources = {item['id']: item for item in request['loaded_resources']}
    assert set(resources) == {'semantics.core', 'template'}
    assert all(item['text'] and item['sha256'] for item in resources.values())
    assert 'template' in request['loaded_resource_ids']
    assert request['source'] == proposal['source']
    assert 'constructor_api' not in request['schema']
    jsonschema.Draft202012Validator.check_schema(request['schema'])


@pytest.mark.parametrize('route', ['hir','hybrid','smtlib2'])
def test_real_native_candidates_validate_at_generation_schema_root(tmp_path,monkeypatch,route):
    from ir2smt import get_request
    clock=itertools.count(0,100)
    monkeypatch.setattr(agent.time,'monotonic',lambda:next(clock))
    source='A condition holds.'
    proposal=get_request(source,{},route,request_profile='compact')
    hir=dict(schema='somt-hir-model-v1',language='hir',decision='satisfiability',
             declarations=[],functions=[],constraints=[{
                 'expr':{'literal':True,'sort':'Bool'},'span':[0,len(source)]}],
             objectives=[],objective_order='single',goal=None,assumptions=[],unresolved=[])
    if route=='hir':
        native=hir
    elif route=='hybrid':
        native=dict(schema='somt-nl-hybrid-v1',hir=hir,smt_constraints=[])
    else:
        native=dict(schema='somt-nl-formal-v1',language='smtlib2',decision='satisfiability',
                    program='(assert true)',links=[{'span':[0,len(source)],'fragment':'(assert true)'}],
                    assumptions=[],unresolved=[])
    backend=Backend([{'action':'lookup','resources':['core']},native])
    wrapper=agent.ProgressiveProvider(backend,tmp_path/route)
    assert wrapper(proposal)==native
    schema=backend.requests[-1]['schema']
    assert 'model' not in schema['oneOf'][0]['properties']
    jsonschema.validate(native,schema)
    if route!='smtlib2':
        assert '$defs' in schema and '$defs' not in schema['oneOf'][0]
