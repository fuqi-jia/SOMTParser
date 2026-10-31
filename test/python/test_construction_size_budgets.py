import pytest

import somtparser as sp
from somtparser.natural_language import Candidate


def _provider(request):
    assert request["language"] == "smtlib2"
    return {
        "schema": "somt-nl-formal-v1",
        "language": "smtlib2",
        "program": "(set-logic QF_LIA)(declare-const x Int)(assert (= x 0))",
        "decision": "satisfiability",
        "assumptions": ["a" * 256],
        "unresolved": [],
        "links": [{"span": [0, 1], "fragment": "(declare-const x Int)"}],
    }


def test_explicit_source_model_and_envelope_budgets_apply_across_public_flow():
    source = "S" * 140
    with pytest.raises(ValueError, match="caller's source-character budget"):
        with sp.construction_limits(max_source_chars=100):
            sp.propose_nl(source, provider=_provider, language="smtlib2")

    with sp.construction_limits(
        max_source_chars=None, max_model_json_chars=4096, max_envelope_json_chars=8192
    ):
        candidate = sp.propose_nl(source, provider=_provider, language="smtlib2")
        assert candidate.source == source
        assert candidate.valid
        envelope = candidate.to_json()
        loaded = Candidate.from_json(envelope)
        assert loaded.digest == candidate.digest
        compiled = sp.compile_candidate(loaded, accept_digest=loaded.digest)
        assert compiled.candidate.digest == candidate.digest
        assert compiled.ok

    with pytest.raises(ValueError, match="candidate JSON exceeds"):
        with sp.construction_limits(max_source_chars=None, max_model_json_chars=128):
            sp.propose_nl(source, provider=_provider, language="smtlib2")

    with pytest.raises(ValueError, match="candidate JSON exceeds"):
        with sp.construction_limits(
            max_source_chars=None, max_model_json_chars=4096, max_envelope_json_chars=128
        ):
            Candidate.from_json(envelope)

    with pytest.raises(ValueError, match="candidate envelope exceeds"):
        with sp.construction_limits(
            max_source_chars=None, max_model_json_chars=4096, max_envelope_json_chars=64
        ):
            candidate.to_json()


def test_budget_values_require_positive_exact_integers_or_none():
    for field in ("max_model_json_chars", "max_formal_program_chars",
                  "max_envelope_json_chars"):
        for value in (0, -1, True, 1.5):
            with pytest.raises(ValueError):
                with sp.construction_limits(**{field: value}):
                    pass


def test_limits_nest_restore_and_do_not_leak_to_other_threads():
    from concurrent.futures import ThreadPoolExecutor

    baseline = sp.current_construction_limits()
    with sp.construction_limits(max_model_json_chars=1234):
        assert sp.current_construction_limits().max_model_json_chars == 1234
        with sp.construction_limits(max_envelope_json_chars=None):
            current = sp.current_construction_limits()
            assert current.max_model_json_chars == 1234
            assert current.max_envelope_json_chars is None
        assert sp.current_construction_limits().max_envelope_json_chars == baseline.max_envelope_json_chars
        with ThreadPoolExecutor(max_workers=1) as pool:
            other = pool.submit(sp.current_construction_limits).result()
        assert other == baseline
    assert sp.current_construction_limits() == baseline


def test_default_source_and_model_budgets_still_reject_oversized_inputs():
    from somtparser._nl_model import MAX_TEXT

    with pytest.raises(ValueError, match="128 Ki-character limit"):
        sp.propose_nl("S" * (MAX_TEXT + 1), provider=_provider, language="smtlib2")

    oversized = {
        "schema": "somt-nl-formal-v1",
        "language": "smtlib2",
        "program": "x" * (16 * 1024 * 1024 + 1),
        "decision": "satisfiability",
        "assumptions": [],
        "unresolved": [],
        "links": [{"span": [0, 1], "fragment": "x"}],
    }
    with pytest.raises(ValueError, match="candidate JSON exceeds"):
        sp.propose_nl(
            "source", provider=lambda request: oversized, language="smtlib2"
        )


def test_explicitly_raised_model_budget_allows_complete_large_candidate_flow():
    from somtparser.natural_language import MAX_MODEL_JSON

    source = "A large but fixed source statement."
    # The long payload is an SMT-LIB comment, so it exercises serialization,
    # candidate hashing, and parsing without adding a large semantic formula.
    program = (
        "(set-logic QF_LIA)\n;"
        + "x" * (MAX_MODEL_JSON + 1)
        + "\n(declare-const x Int)(assert (= x 0))"
    )
    model = {
        "schema": "somt-nl-formal-v1",
        "language": "smtlib2",
        "program": program,
        "decision": "satisfiability",
        "assumptions": [],
        "unresolved": [],
        "links": [{"span": [0, len(source)], "fragment": source}],
    }

    with pytest.raises(ValueError, match="caller's source-character budget"):
        with sp.construction_limits(max_source_chars=len(source) - 1):
            sp.propose_nl(source, provider=lambda request: model, language="smtlib2")

    with sp.construction_limits(
        max_source_chars=None,
        max_model_json_chars=MAX_MODEL_JSON + 512 * 1024,
        max_formal_program_chars=MAX_MODEL_JSON + 512 * 1024,
        max_envelope_json_chars=MAX_MODEL_JSON + 1024 * 1024,
    ):
        fragment = "(set-logic QF_LIA)"
        source = "S" * 140000 + fragment
        model["links"] = [{"span": [140000, len(source)], "fragment": fragment}]
        candidate = sp.propose_nl(source, provider=lambda request: model, language="smtlib2")
        assert candidate.valid
        encoded = candidate.to_json()
        loaded = Candidate.from_json(encoded)
        compiled = sp.compile_candidate(loaded, accept_digest=loaded.digest)
        assert compiled.ok
        assert compiled.to_smt2().startswith("(set-logic ALL)")

    with pytest.raises(ValueError, match="candidate JSON exceeds"):
        candidate.to_json()



def test_formal_program_budget_remains_128k_by_default_and_is_independently_raiseable():
    from somtparser._nl_model import MAX_TEXT

    source = "A bounded source statement."
    program = (
        "(set-logic QF_LIA)\n;"
        + "x" * (MAX_TEXT + 1)
        + "\n(declare-const x Int)(assert (= x 0))"
    )
    model = {
        "schema": "somt-nl-formal-v1",
        "language": "smtlib2",
        "program": program,
        "decision": "satisfiability",
        "assumptions": [],
        "unresolved": [],
        "links": [{"span": [0, len(source)], "fragment": "(set-logic QF_LIA)"}],
    }

    candidate = sp.propose_nl(
        source, provider=lambda request: model, language="smtlib2"
    )
    assert not candidate.valid
    assert any("bounded formal program" in item for item in candidate.diagnostics)
    assert len(candidate.to_json()) > 0  # model/envelope budgets are independent

    with sp.construction_limits(max_formal_program_chars=MAX_TEXT + 1024):
        raised = sp.propose_nl(
            source, provider=lambda request: model, language="smtlib2"
        )
        assert raised.valid
        loaded = Candidate.from_json(raised.to_json())
        compiled = sp.compile_candidate(loaded, accept_digest=loaded.digest)
        assert compiled.ok
