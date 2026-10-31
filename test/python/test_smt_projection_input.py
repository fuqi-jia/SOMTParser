import pytest
import z3

from tools.semantic_checks.smt_projection_input import check_smt_relation_equivalence

REF = "(declare-const r Int) (assert (= r 2)) (minimize r)"
CAND = ("(define-fun-rec h ((p Int)) Int (+ p 1)) "
        "(declare-const x Int) (assert (= x 1)) (minimize (h x))")


def _bridges(candidate_sign=1):
    def build(ref, cand):
        ctx = ref.ctx
        visible = z3.Int('same_public', ctx=ctx)
        signed_cost = z3.Real('same_signed_cost', ctx=ctx)
        return {
            'reference_bridges': [(visible, ref.assertions()[0].arg(0))],
            'candidate_bridges': [(visible, cand.objectives()[0])],
            'reference_cost_bridge': (signed_cost, z3.ToReal(ref.objectives()[0])),
            'candidate_cost_bridge': (signed_cost, candidate_sign * z3.ToReal(cand.objectives()[0])),
        }
    return build


def test_parse_and_projection_entry_preserves_relation_and_signed_min_cost():
    result = check_smt_relation_equivalence(
        REF, CAND, z3=z3, bridge_builder=_bridges(),
        total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.comparison.equivalent


def test_parse_and_projection_entry_rejects_wrong_signed_cost_direction():
    result = check_smt_relation_equivalence(
        REF, CAND, z3=z3, bridge_builder=_bridges(-1),
        total_timeout_ms=None, per_obligation_timeout_ms=None)
    assert result.comparison.status == 'counterexample'


def _observable_only(_ref, _cand):
    return {'reference_bridges': [], 'candidate_bridges': []}


def _one_sided_cost(ref, cand):
    ctx = ref.ctx
    cost = z3.Real('one_sided_cost', ctx=ctx)
    return {'reference_bridges': [], 'candidate_bridges': [],
            'reference_cost_bridge': (cost, z3.ToReal(ref.objectives()[0]))}


def _both_costs(ref, cand):
    ctx = ref.ctx
    cost = z3.Real('both_costs', ctx=ctx)
    return {'reference_bridges': [], 'candidate_bridges': [],
            'reference_cost_bridge': (cost, z3.ToReal(ref.objectives()[0])),
            'candidate_cost_bridge': (cost, z3.ToReal(cand.objectives()[0]))}


def test_objective_cannot_be_silently_omitted_from_bridge():
    with pytest.raises(ValueError, match='both signed cost bridges are required'):
        check_smt_relation_equivalence(
            REF, CAND, z3=z3, bridge_builder=_observable_only,
            total_timeout_ms=None, per_obligation_timeout_ms=None)


def test_objective_cannot_have_only_one_cost_bridge():
    with pytest.raises(ValueError, match='both signed cost bridges are required'):
        check_smt_relation_equivalence(
            REF, CAND, z3=z3, bridge_builder=_one_sided_cost,
            total_timeout_ms=None, per_obligation_timeout_ms=None)


def test_multiple_objectives_are_rejected_instead_of_truncated():
    ref = REF + ' (maximize r)'
    cand = CAND + ' (maximize (h x))'
    with pytest.raises(ValueError, match='multiple objectives are unsupported'):
        check_smt_relation_equivalence(
            ref, cand, z3=z3, bridge_builder=_both_costs,
            total_timeout_ms=None, per_obligation_timeout_ms=None)


def test_reference_candidate_objective_count_mismatch_is_rejected():
    with pytest.raises(ValueError, match='objective counts differ'):
        check_smt_relation_equivalence(
            REF, CAND.replace(' (minimize (h x))', ''), z3=z3,
            bridge_builder=_both_costs,
            total_timeout_ms=None, per_obligation_timeout_ms=None)


def _unexpected_costs(_ref, _cand):
    ctx = _ref.ctx
    cost = z3.Real('unexpected_feasibility_cost', ctx=ctx)
    return {'reference_bridges': [], 'candidate_bridges': [],
            'reference_cost_bridge': (cost, z3.RealVal(1, ctx=ctx)),
            'candidate_cost_bridge': (cost, z3.RealVal(1, ctx=ctx))}


def test_cost_bridges_are_rejected_for_satisfaction_only_models():
    ref = '(declare-const r Int) (assert (= r 2))'
    cand = '(declare-const x Int) (assert (= x 2))'
    with pytest.raises(ValueError, match='cost bridges are forbidden'):
        check_smt_relation_equivalence(
            ref, cand, z3=z3, bridge_builder=_unexpected_costs,
            total_timeout_ms=None, per_obligation_timeout_ms=None)
