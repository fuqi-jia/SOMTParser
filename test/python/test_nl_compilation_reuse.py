"""Compile accepted snapshots once without weakening validation or options."""
import json

import pytest
import z3
import somtparser as sp
import somtparser.natural_language as nl
from somtparser.hir import HirBuilder


def snapshot():
    source = "Choose an integer x between zero and ten; maximize x."
    model = dict(
        schema="somt-hir-model-v1", language="hir", decision="optimization",
        declarations=[dict(name="x", sort="Int", lower=0, upper=10)],
        functions=[], constraints=[],
        objectives=[dict(sense="maximize", expr={"var": "x"}, span=[0, len(source)])],
        objective_order="single", goal=None, assumptions=[], unresolved=[],
    )
    # Direct construction must exercise the same validation as a loaded proposal.
    return nl.Candidate(source, json.dumps(model), "test", ())


@pytest.mark.parametrize("dialect", [None, sp.OmtDialect.Z3])
def test_default_compilation_constructs_and_lowers_once(monkeypatch, dialect):
    builds, lowerings = [], []
    original_build, original_translate = nl.build_hir, HirBuilder.translate

    def build(*args, **kwargs):
        builds.append(True)
        return original_build(*args, **kwargs)

    def translate(self, **kwargs):
        lowerings.append(kwargs)
        return original_translate(self, **kwargs)

    monkeypatch.setattr(nl, "build_hir", build)
    monkeypatch.setattr(HirBuilder, "translate", translate)
    candidate = snapshot()
    for _ in range(2):
        result = sp.compile_candidate(candidate, accept_digest=candidate.digest, dialect=dialect)
        assert result.ok, result.diagnostics
        solver = z3.Optimize()
        solver.from_string(result.to_smt2())
        assert solver.check() == z3.sat
        assert solver.model().eval(z3.Int("x")).as_long() == 10
    # Revalidation is per call, while duplicate construction within a call is gone.
    assert len(builds) == len(lowerings) == 2


def test_requested_bounded_profile_is_not_replaced_by_default_validation():
    candidate = snapshot()
    bounded = sp.compile_candidate(candidate, accept_digest=candidate.digest, profile="bv32")
    assert bounded.ok, bounded.diagnostics
    assert bounded.translation.report.fidelity.bounds
    exact = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert exact.ok, exact.diagnostics
    assert not exact.translation.report.fidelity.bounds


def test_requested_dialect_is_not_replaced_by_default_validation():
    candidate = snapshot()
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest,
                                  dialect=sp.OmtDialect.NONE)
    assert not result.ok
    assert result.diagnostics


def test_direct_snapshot_cannot_bypass_hir_contract():
    candidate = snapshot()
    model = candidate.model
    model["objectives"][0]["expr"] = {"var": "undeclared"}
    invalid = nl.Candidate(candidate.source, json.dumps(model), candidate.provider, ())
    assert invalid.valid  # diagnostics supplied by callers are not trusted
    result = sp.compile_candidate(invalid, accept_digest=invalid.digest)
    assert not result.ok
    assert result.translation is None


def test_preparation_retains_controlled_projection_and_replay():
    source = "Let x be an integer between 0 and 10.\nx is at least 3.\nMinimize x.\n"
    candidate = sp.propose_nl(source)
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert result.ok, result.diagnostics
    assert result.project_assignment({"nl_s0": 3}) == {"x": 3}
    assert result.replay_assignment({"x": 3})["holds"]
    assert not result.replay_assignment({"x": 2})["holds"]
