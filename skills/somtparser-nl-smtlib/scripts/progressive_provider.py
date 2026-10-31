"""Bounded, caller-injected LLM loop for demand-driven skill resource reads.

No credentials, network transport or solver is owned here. An explicit provider
callable is injected by an agent/harness; each lookup and candidate call is kept.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import time

from capability_pack import capability_index, materialize_capabilities


class ProgressiveProtocolError(ValueError):
    pass


def canonical(value):
    return json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(',',':'))


def save(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x',encoding='utf-8') as stream:
        stream.write(json.dumps(value,ensure_ascii=False,indent=2)+'\n')


class ProgressiveProvider:
    """Keep source/context invariant while looking up selected skill resources.

    The call budget covers selection, additional lookups, candidates and outer
    construction repairs together. A timeout is never automatically repeated.
    """
    def __init__(self,provider,directory,max_calls=5,tokens_per_minute=50000):
        if type(max_calls) is not int or max_calls<2:
            raise ValueError('at least two calls are required for selection and generation')
        self.provider,self.directory=provider,Path(directory)
        self.max_calls,self.tokens_per_minute=max_calls,tokens_per_minute
        self.loaded=[]
        self.calls=0
        self.binding=None
        self.not_before=0
        self.last_request=self.last_response_content=self.last_metadata=None
        self.call_records=[]
        self.call_start=0

    def __getattr__(self,name):
        return getattr(self.provider,name)

    def _exchange(self,request,phase):
        if self.calls>=self.max_calls:
            raise ProgressiveProtocolError('skill agent call budget exhausted')
        while time.monotonic()<self.not_before:
            time.sleep(min(10,self.not_before-time.monotonic()))
        self.calls+=1
        root=self.directory/'skill-rounds'/f'{self.calls:03d}'
        save(root/'proposal.json',request)
        save(root/'started.json',dict(phase=phase,round=self.calls,loaded_resources=self.loaded.copy()))
        try:
            response=self.provider(request)
            save(root/'response.json',response)
            return response
        finally:
            self.last_request=self.provider.last_request
            self.last_response_content=self.provider.last_response_content
            metadata=self.provider.last_metadata
            if self.last_request is not None: save(root/'provider-request.json',self.last_request)
            if self.last_response_content is not None: save(root/'provider-content.json',self.last_response_content)
            save(root/'provider-metadata.json',metadata)
            self.call_records.append(dict(phase=phase,metadata=metadata))
            usage=(metadata or {}).get('usage',{})
            # Account for all model calls, including resource selection/lookup.
            current_records=self.call_records[self.call_start:]
            sums={key:sum((x['metadata'] or {}).get('usage',{}).get(key,0) for x in current_records)
                  for key in ('prompt_tokens','completion_tokens','total_tokens')}
            unknown=sum('total_tokens' not in (x['metadata'] or {}).get('usage',{}) for x in current_records)
            self.last_metadata=dict(provider='progressive-skill-agent',requested_model=self.provider.model,
                usage=sums,usage_unknown_calls=unknown,provider_calls=len(current_records),total_provider_calls=self.calls,
                loaded_resources=self.loaded.copy(),max_calls=self.max_calls,
                rounds=[dict(phase=x['phase'],metadata=x['metadata']) for x in current_records])
            self.not_before=time.monotonic()+max(1,60*usage.get('total_tokens',0)/self.tokens_per_minute)

    def __call__(self,proposal):
        self.call_start=len(self.call_records)
        self.last_request=self.last_response_content=None
        # A local budget/binding rejection makes zero transport calls. Keep an
        # explicit empty total so the caller cannot bill it as an unknown call.
        self.last_metadata=dict(provider='progressive-skill-agent',requested_model=self.provider.model,
            usage=dict(prompt_tokens=0,completion_tokens=0,total_tokens=0),
            usage_unknown_calls=0,provider_calls=0,total_provider_calls=self.calls,
            loaded_resources=self.loaded.copy(),max_calls=self.max_calls,rounds=[])
        route=proposal['language']
        identity=canonical({k:proposal.get(k) for k in ('source','source_sha256','context','language','dialect')})
        if self.binding is not None and self.binding!=identity:
            raise ProgressiveProtocolError('source/context/route/dialect changed between calls')
        self.binding=identity
        index=capability_index(route,proposal)
        base={k:deepcopy(proposal[k]) for k in ('source','source_sha256','context','language','dialect') if k in proposal}
        base.update(protocol='somt-skill-agent-v2',resource_index=self._index_with_state(index))
        lookup_schema=self._lookup_schema(index)
        if not self.loaded:
            request=dict(base,phase='resource_selection',schema=lookup_schema,
                instruction='Honor the fixed route and target dialect. Read the original task and choose the resource IDs needed for its semantics, '
                            'API constructs, macros and dialect. Return action=lookup and resources; '
                            'do not translate yet. Select only relevant IDs from the index.')
            if 'repair' in proposal:
                request['repair']={k:deepcopy(v) for k,v in proposal['repair'].items() if k!='instruction'}
            response=self._exchange(request,'select')
            self._load(response,route,proposal)
        while self.calls<self.max_calls:
            packet=materialize_capabilities(route,self.loaded,proposal)
            view=packet['request']
            candidate_schema=deepcopy(view['schema'])
            definitions=candidate_schema.pop('$defs',None)
            # Generation uses the route's own envelope. A second candidate
            # wrapper made small models put hybrid fields at the wrong level.
            # All local #/$defs references still resolve from the action root.
            action_schema={'oneOf':[candidate_schema,self._lookup_schema(index)]}
            if definitions is not None:
                action_schema['$defs']=definitions
            # The packet is a view of available syntax, never an authority to
            # drop a source clause that needs an unloaded capability.
            request=dict(view,protocol='somt-skill-agent-v2',phase='resource_generation',resource_index=self._index_with_state(index),
                loaded_resource_ids=self.loaded.copy(),resource_packet={k:v for k,v in packet.items() if k!='request'},
                schema=action_schema,
                instruction=view['instruction']+'\nUse the retrieved resources to translate every clause of the original source. '
                            'Return the complete native route candidate object directly, with no action or model wrapper. '
                            'For hybrid, schema, hir and smt_constraints are fields of that single candidate object. '
                            'If another rule/API/template/dialect guide is needed, return action=lookup with '
                            'only additional resource IDs marked loaded=false in the index. Resources marked '
                            'loaded=true have already been supplied in this request: use them and generate the candidate, '
                            'rather than requesting them again. An unloaded API is not an unsupported source feature; '
                            'request it instead of weakening the model. Never omit a source requirement to '
                            'fit the loaded subset. Keep all caller context and observables. '
                            'Use exact quote anchors for source locations. Do not solve or consult answers.')
            if 'repair' in proposal: request['repair']=deepcopy(proposal['repair'])
            response=self._exchange(request,'generate')
            if isinstance(response,dict) and 'action' not in response:
                # The native compiler owns candidate fields and semantics.
                self.last_response_content=canonical(response)
                return response
            if isinstance(response,dict) and response.get('action')=='candidate':
                if set(response)!={'action','model'} or not isinstance(response.get('model'),dict):
                    raise ProgressiveProtocolError(
                        'Malformed legacy candidate wrapper: it must contain exactly action="candidate" and an object model. '
                        'Every candidate field, including hybrid smt_constraints, belongs inside model in that legacy form. '
                        'Prefer returning the complete native '+route+' candidate directly, without action/model wrappers.')
                self.last_response_content=canonical(response['model'])
                return response['model']
            if isinstance(response,dict) and response.get('action')=='lookup':
                self._load(response,route,proposal)
            else:
                raise ProgressiveProtocolError(
                    'Return the complete native '+route+' candidate object directly, or action="lookup" with '
                    'unloaded resource IDs; do not add a different action or an extra candidate wrapper.')
        raise ProgressiveProtocolError('skill agent call budget exhausted before a candidate')

    def _index_with_state(self,index):
        return [dict(item,loaded=item['id'] in self.loaded) for item in index]

    def _lookup_schema(self,index):
        available=[item['id'] for item in index if item['id'] not in self.loaded]
        if not available:
            # An empty enum is not portable across schema consumers. Disable
            # the lookup branch once every indexed resource has been supplied.
            return False
        return dict(type='object',required=['action','resources'],additionalProperties=False,
            properties=dict(action={'const':'lookup'},resources={'type':'array',
                'items':{'type':'string','enum':available},'minItems':1,'uniqueItems':True}))

    def _load(self,response,route,proposal):
        if not isinstance(response,dict) or set(response)!= {'action','resources'} or response['action']!='lookup':
            raise ProgressiveProtocolError('expected a lookup action with resource IDs')
        ids=response['resources']
        if not isinstance(ids,list) or not ids or any(not isinstance(x,str) for x in ids):
            raise ProgressiveProtocolError('resources must be a nonempty list of IDs')
        repeated=sorted(set(ids)&set(self.loaded))
        if repeated:
            raise ProgressiveProtocolError(
                'Resources already loaded: '+', '.join(repeated)+'. Their API/document contents are already '
                'included in the current request. Use those contents and return the native '+route+
                ' candidate directly; request only genuinely missing IDs marked loaded=false.')
        chosen=list(dict.fromkeys(self.loaded+ids))
        # Validate every ID; don't silently expand or ignore an unknown request.
        try:
            packet=materialize_capabilities(route,chosen,proposal)
        except ValueError as error:
            raise ProgressiveProtocolError(str(error)) from error
        self.loaded=packet['loaded']
        save(self.directory/'skill-rounds'/f'{self.calls:03d}'/'retrieved.json',packet)
