"""Provider isolation/provenance contracts; fake transport only."""
import io
import json
from urllib import error

import pytest

from somtparser.compatible_provider import CompatibleProvider, CompatibleProviderError

KEY = "unit-test-key-never-a-real-credential"
URL = "https://token-plan.cn-beijing.maas.aliyuncs.com/compatible-mode/v1"


def provider(**kwargs):
    return CompatibleProvider(base_url=URL, api_key=KEY, model="test-model", **kwargs)


def transport(monkeypatch, content="{}", finish="stop", failure=None):
    calls = []
    class Opener:
        def open(self, req, timeout):
            calls.append(req)
            if failure is not None:
                raise failure
            return io.BytesIO(json.dumps(dict(model="returned-test-model", choices=[dict(
                finish_reason=finish, message=dict(content=content))],
                usage=dict(prompt_tokens=11, completion_tokens=7, total_tokens=18))).encode())
    monkeypatch.setattr("somtparser.compatible_provider.request.build_opener", lambda *a:Opener())
    return calls


def test_explicit_endpoint_skill_and_credential_isolation(monkeypatch):
    calls=transport(monkeypatch)
    p=provider(skill="Preserve exact rational objectives.")
    assert p({"source":"a test problem", "language":"smtlib2"}) == {}
    req=calls[0]
    assert req.full_url == URL + "/chat/completions"
    assert req.get_header("Authorization") == "Bearer " + KEY
    assert KEY not in req.data.decode()+repr(p)+json.dumps(p.last_metadata)
    assert "Preserve exact rational objectives." in p.last_request["messages"][0]["content"]
    assert p.last_metadata["usage"]["total_tokens"] == 18
    assert p.last_metadata["returned_model"] == "returned-test-model"


def test_incomplete_output_preserves_billable_usage(monkeypatch):
    transport(monkeypatch,content="{",finish="length")
    p=provider()
    with pytest.raises(CompatibleProviderError,match="incomplete"):
        p({"source":"test"})
    assert p.last_metadata["usage"]["total_tokens"] == 18


def test_http_error_body_cannot_leak_credentials(monkeypatch):
    calls=transport(monkeypatch,failure=error.HTTPError(URL,401,KEY,{},io.BytesIO(KEY.encode())))
    p=provider()
    with pytest.raises(CompatibleProviderError) as exc:
        p({"source":"test"})
    assert exc.value.status == 401
    assert KEY not in str(exc.value)
    assert len(calls) == 1


def test_rejects_credential_in_prompt_or_response(monkeypatch):
    calls=transport(monkeypatch)
    with pytest.raises(CompatibleProviderError,match="prompt"):
        provider()({"source":KEY})
    assert not calls
    transport(monkeypatch,content=json.dumps({"echo":KEY}))
    p=provider()
    with pytest.raises(CompatibleProviderError,match="response"):
        p({"source":"test"})
    assert p.last_response_content is None


@pytest.mark.parametrize("url",["http://example.com", "https://u:secret@example.com",
                                "https://example.com/?key=secret", "https://example.com/#secret"])
def test_rejects_unsafe_endpoint(url):
    with pytest.raises(ValueError):
        CompatibleProvider(base_url=url,api_key=KEY,model="test-model")


@pytest.mark.parametrize('language', ['hir', 'hybrid'])
def test_route_specific_contract_is_not_direct_smt(monkeypatch, language):
    transport(monkeypatch)
    p = provider()
    p({'source': 'Choose x.', 'language': language})
    system = p.last_request['messages'][0]['content']
    assert 'Each links fragment' not in system
    assert ('typed HIR' if language == 'hir' else 'hybrid envelope') in system


def test_json_mode_is_explicit_and_recorded(monkeypatch):
    calls=transport(monkeypatch)
    p=provider(response_format='json_object')
    p({'source':'A test.', 'language':'hir'})
    assert json.loads(calls[0].data)['response_format']=={'type':'json_object'}
    assert p.last_metadata['response_format']=='json_object'
    with pytest.raises(ValueError):
        provider(response_format='unsupported')


@pytest.mark.parametrize('language', ['hir', 'hybrid', 'smtlib2'])
def test_progressive_protocol_overrides_candidate_only_contract(monkeypatch, language):
    transport(monkeypatch, content='{"action":"lookup","resources":["core"]}')
    p = provider(response_format='json_object')
    assert p({'source': 'Choose x.', 'language': language,
              'protocol': 'somt-skill-agent-v1', 'phase': 'resource_selection'})['action'] == 'lookup'
    system = p.last_request['messages'][0]['content']
    assert 'lookup' in system and 'candidate' in system
    assert 'Each links fragment' not in system
    assert 'Emit typed HIR JSON' not in system


@pytest.mark.parametrize('phase', ['resource_selection', 'resource_generation'])
def test_progressive_v2_uses_phase_specific_native_candidate_contract(monkeypatch, phase):
    transport(monkeypatch)
    p = provider(response_format='json_object')
    p({'source':'Choose x.', 'language':'hybrid', 'dialect':'z3',
       'protocol':'somt-skill-agent-v2', 'phase':phase})
    system = p.last_request['messages'][0]['content']
    assert ('Do not return a candidate in this selection phase' in system) == (phase=='resource_selection')
    assert ('complete native route candidate directly' in system) == (phase=='resource_generation')
