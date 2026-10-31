"""Explicit caller budgets retain defaults and cannot cross task boundaries."""
import asyncio
import pytest
import somtparser as sp
from somtparser.natural_language import Candidate
from somtparser.hir import HirBuilder, ModelError
from somtparser.construction_limits import construction_limits, current_construction_limits


def expression():
    return {"op": "and", "args": [{"literal": True, "sort": "Bool"} for _ in range(6)]}


def test_default_restoration_and_builder_budget_snapshot():
    baseline = current_construction_limits()
    with construction_limits(max_hir_nodes=2):
        tiny = HirBuilder()
        with pytest.raises(ModelError, match="budget"):
            tiny.expr(expression())
        with construction_limits(max_hir_nodes=None):
            large = HirBuilder()
            assert repr(large.expr(expression()).sort) == "Bool"
        assert current_construction_limits().max_hir_nodes == 2
        assert repr(large.expr(expression()).sort) == "Bool"
    assert current_construction_limits() == baseline
    with pytest.raises(RuntimeError):
        with construction_limits(max_source_chars=10):
            raise RuntimeError("caller error")
    assert current_construction_limits() == baseline


@pytest.mark.parametrize("value", [0, -1, True, 1.5, "100000"])
def test_limits_are_caller_integers_or_explicit_unlimited(value):
    with pytest.raises(ValueError):
        with construction_limits(max_hir_nodes=value):
            pass


def test_concurrent_async_tasks_have_independent_limits():
    async def worker(limit):
        with construction_limits(max_hir_nodes=limit):
            await asyncio.sleep(0)
            return HirBuilder().max_nodes
    async def run():
        return await asyncio.gather(worker(10), worker(None))
    assert asyncio.run(run()) == [10, None]
    assert current_construction_limits().max_hir_nodes == 100000


def test_large_source_roundtrip_uses_explicit_caller_policy():
    source = "x" * 131073
    raw = dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
               declarations=[], functions=[], constraints=[dict(expr={"literal": True, "sort": "Bool"}, span=[0, 1])],
               objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])
    with pytest.raises(ModelError, match="128 Ki"):
        sp.propose_nl(source, language="hir", provider=lambda request: raw)
    with construction_limits(max_source_chars=None):
        candidate = sp.propose_nl(source, language="hir", provider=lambda request: raw)
        assert candidate.valid, candidate.diagnostics
        restored = Candidate.from_json(candidate.to_json())
        assert restored.digest == candidate.digest
        assert sp.compile_candidate(restored, accept_digest=restored.digest).ok
    with pytest.raises(ModelError, match="128 Ki"):
        Candidate.from_json(candidate.to_json())
