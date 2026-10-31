"""Candidate validation checks HIR; only compilation selects target lowering."""
import pytest
import z3

import somtparser as sp
from somtparser.hir import HirBuilder
from somtparser.natural_language import Candidate


def model():
    return dict(schema="somt-hir-model-v1", language="hir", decision="optimization",
                declarations=[dict(name="x", sort="Int", lower=-5, upper=9)],
                functions=[], constraints=[],
                objectives=[dict(sense="maximize", expr={"var": "x"}, span=[0, 1])],
                objective_order="single", goal=None, assumptions=[], unresolved=[])


@pytest.mark.parametrize("profile", ["default", "quantified", "bv32"])
def test_proposal_and_snapshot_load_do_not_lower_before_selected_profile(monkeypatch, profile):
    lowerings = []
    original = HirBuilder.translate

    def record(self, **options):
        lowerings.append(options)
        assert options["profile"] == profile
        return original(self, **options)

    monkeypatch.setattr(HirBuilder, "translate", record)
    candidate = sp.propose_nl("x", language="hir", provider=lambda request: model())
    assert candidate.valid, candidate.diagnostics
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert lowerings == []
    result = sp.compile_candidate(restored, accept_digest=restored.digest, profile=profile)
    assert result.ok, result.diagnostics
    assert len(lowerings) == 1
    assert lowerings[0]["profile"] == profile
    ctx = z3.Context()
    target = z3.Optimize(ctx=ctx)
    target.from_string(result.to_smt2())
    assert len(target.objectives()) == 1
    assert target.check() == z3.sat
    # The exact profiles retain the source's full interval and signed cost.
    if profile != "bv32":
        x = z3.Int("x", ctx=ctx)
        proof = z3.Solver(ctx=ctx)
        proof.add(z3.Or(z3.Xor(z3.And(*target.assertions()), z3.And(x >= -5, x <= 9)),
                        target.objectives()[0] != -x))
        assert proof.check() == z3.unsat, proof.reason_unknown()


@pytest.mark.parametrize("failure", ["undeclared", "wrong_sort"])
def test_candidate_validation_still_rejects_invalid_hir_without_lowering(monkeypatch, failure):
    def unexpected(*args, **kwargs):
        raise AssertionError("invalid HIR must be rejected before target lowering")

    monkeypatch.setattr(HirBuilder, "translate", unexpected)
    raw = model()
    raw["objectives"][0]["expr"] = ({"var": "missing"} if failure == "undeclared"
                                           else {"literal": True, "sort": "Bool"})
    candidate = sp.propose_nl("x", language="hir", provider=lambda request: raw)
    assert not candidate.valid
    assert candidate.diagnostics
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert not result.ok
    assert result.translation is None
