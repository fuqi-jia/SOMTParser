import io
import json
import pytest
from somtparser.deepseek_reasoning import DeepSeekReasoningProvider
from somtparser.deepseek import DeepSeekError
from somtparser.hir import hir_schema


def test_reasoning_body_metadata_and_credential_redaction(monkeypatch):
    seen = []

    class Opener:
        def open(self, req, timeout):
            seen.append(json.loads(req.data))
            return io.BytesIO(
                json.dumps(
                    dict(
                        model="deepseek-flash",
                        choices=[
                            dict(
                                finish_reason="stop",
                                message=dict(
                                    content='{"schema":"example"}',
                                    reasoning_content="private rationale",
                                ),
                            )
                        ],
                        usage=dict(
                            prompt_tokens=3, completion_tokens=4, total_tokens=7
                        ),
                    )
                ).encode()
            )

    monkeypatch.setattr(
        "somtparser.deepseek_reasoning.request.build_opener", lambda *a: Opener()
    )
    provider = DeepSeekReasoningProvider(api_key="unit-test-token")
    assert provider(
        dict(language="hir", source="x", schema=hir_schema(), context={})
    ) == dict(schema="example")
    assert provider.last_metadata["prompt_version"] == "somt-hir-thinking-v4"
    system = provider.last_request["messages"][0]["content"]
    assert '"op":"all_different","args":[{"var":"array_name"}]' in system
    assert "final array axis" in system
    assert "requires the Boolean field positive" in system
    assert "every source domain, instance-data row, independent constraint" in system
    assert seen[0]["thinking"] == dict(type="enabled")
    assert "temperature" not in seen[0]
    assert provider.last_metadata["temperature"] is None
    assert "unit-test-token" not in repr(provider) + json.dumps(
        provider.last_metadata
    ) + json.dumps(provider.last_request)
    assert (
        "private rationale"
        not in json.dumps(provider.last_metadata) + provider.last_response_content
    )


@pytest.mark.parametrize("limit", [0, 819.5, True, 65537])
def test_reasoning_budget_validation(limit):
    with pytest.raises(DeepSeekError):
        DeepSeekReasoningProvider(api_key="test", max_tokens=limit)


def test_truncation_and_duplicate_json_keys_are_not_accepted(monkeypatch):
    for finish, content in [("length", "{}"), ("stop", '{"x":1,"x":2}')]:

        class Opener:
            def open(self, req, timeout):
                return io.BytesIO(
                    json.dumps(
                        dict(
                            choices=[
                                dict(
                                    finish_reason=finish, message=dict(content=content)
                                )
                            ]
                        )
                    ).encode()
                )

        monkeypatch.setattr(
            "somtparser.deepseek_reasoning.request.build_opener", lambda *a: Opener()
        )
        with pytest.raises(DeepSeekError):
            DeepSeekReasoningProvider(api_key="test")(
                dict(language="hir", source="x", schema={}, context={})
            )
