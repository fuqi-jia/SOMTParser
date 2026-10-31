"""Shared adapter for candidate and reference relation projections.

Both sides use the same exact, proof-gated projection algorithm. Every source
assertion and observable/cost bridge remains in the constructed relation.
"""
from dataclasses import dataclass
from typing import Optional
import time

from .projection import (existential_projection, free_constants,
                         optimize_observation_projection)


@dataclass(frozen=True)
class CandidateProjection:
    formula: object
    optimization: object


@dataclass(frozen=True)
class RelationEquivalenceCheck:
    """Projection and exact-comparison result under one shared wall budget."""
    reference: CandidateProjection
    candidate: CandidateProjection
    comparison: object
    total_budget_ms: Optional[int]
    preprocessing_budget_ms: Optional[int]
    preprocessing_elapsed_ms: int
    directional_budget_ms: Optional[int]
    total_elapsed_ms: int
    reference_projection_elapsed_ms: int = 0
    candidate_projection_elapsed_ms: int = 0
    counterexample_validation: object = None


def _validate_aliases(assertions, observation_bridges, cost_bridge):
    """Enforce the freshness condition required by the projection proof."""
    import z3

    observation_bridges = list(observation_bridges)
    bridges = list(observation_bridges)
    if cost_bridge is not None:
        bridges.append(cost_bridge)
    aliases = [alias for alias, _ in bridges]
    alias_ids = [alias.get_id() for alias in aliases]
    if len(alias_ids) != len(set(alias_ids)):
        raise ValueError("each observable and cost requires a distinct alias")
    for alias in aliases:
        if (not z3.is_const(alias)
                or alias.decl().kind() != z3.Z3_OP_UNINTERPRETED
                or alias.sort().kind() == z3.Z3_ARRAY_SORT):
            raise ValueError("projection aliases must be scalar constants")
    if any(alias.sort() != term.sort()
           for alias, term in observation_bridges):
        raise ValueError("projection alias and bridged term sorts differ")
    if cost_bridge is not None:
        cost_alias, cost_term = cost_bridge
        # R77 creates a Real cost coordinate; Z3's equality coerces integer
        # objectives with ToReal. Same-sort Int/Int is also useful in the
        # standalone relational tests.
        cost_sort_pair = (cost_alias.sort().kind(), cost_term.sort().kind())
        allowed_cost_pairs = {
            (z3.Z3_INT_SORT, z3.Z3_INT_SORT),
            (z3.Z3_REAL_SORT, z3.Z3_REAL_SORT),
            (z3.Z3_REAL_SORT, z3.Z3_INT_SORT),
        }
        if cost_sort_pair not in allowed_cost_pairs:
            raise ValueError("cost alias and objective sorts are incompatible")
    original_terms = list(assertions) + [term for _, term in bridges]
    original_ids = {constant.get_id()
                    for constant in free_constants(original_terms)}
    if any(alias_id in original_ids for alias_id in alias_ids):
        raise ValueError("projection aliases must be fresh before bridge equations")


def candidate_projection(assertions, observation_bridges, cost_bridge=None, *,
                         guarded_bool_budget_ms=5000,
                         progress_callback=None):
    """Project a candidate relation to observable aliases and optional cost.

    `observation_bridges` is a sequence of `(fresh_alias, candidate_term)`.
    `cost_bridge`, if supplied, is one `(fresh_cost_alias, objective_term)` pair.
    The cost equation is retained in the body and its alias is visible, but the
    objective term is never used as a substitution pattern. The optimization
    metadata reports exact top-level cardinality conjunct rewrites performed
    before finite quantifier expansion.
    """
    import z3

    assertions = list(assertions)
    observation_bridges = list(observation_bridges)
    _validate_aliases(assertions, observation_bridges, cost_bridge)
    equations = [alias == term for alias, term in observation_bridges]
    visible = [alias for alias, _ in observation_bridges]
    if cost_bridge is not None:
        cost_alias, cost_term = cost_bridge
        equations.append(cost_alias == cost_term)
        visible.append(cost_alias)
    body = z3.And(*(assertions + equations))
    optimization_options = {"guarded_bool_budget_ms": guarded_bool_budget_ms}
    if progress_callback is not None:
        optimization_options["progress_callback"] = progress_callback
    optimization = optimize_observation_projection(
        body, observation_bridges, **optimization_options)
    return CandidateProjection(
        existential_projection(optimization.body, visible), optimization
    )


def reference_projection(assertions, observation_bridges, cost_bridge=None):
    """Build the reference relation through the same exact projection path.

    `candidate_projection` validates alias freshness and retains all source
    assertions plus observation and optional cost bridge equations. Reusing its
    formula prevents side-specific projection behavior while preserving this
    function's formula-only return type.
    """
    return candidate_projection(
        assertions, observation_bridges, cost_bridge).formula


def check_relation_equivalence(reference_assertions, candidate_assertions, *,
                               reference_bridges, candidate_bridges,
                               reference_cost_bridge=None,
                               candidate_cost_bridge=None,
                               total_timeout_ms=120000,
                               preprocessing_budget_ms=None,
                               per_obligation_timeout_ms=1000,
                               simplify=True, progress_callback=None):
    """Project both relations and check equivalence within one wall budget.

    Set total_timeout_ms and per_obligation_timeout_ms to None to remove both
    the overall deadline and individual solver timers. With no overall deadline,
    the default preprocessing_budget_ms=None also leaves preprocessing unbounded.
    Explicit finite preprocessing limits still apply. Zero retains its existing
    exhausted-budget meaning; it is not an alias for an unbounded check.

    The default preprocessing allowance is at most 35 seconds and at most a
    third of the total budget. That supports the 35s+85s case-110 split while
    keeping small-budget calls useful. Both guarded-Bool proof passes share
    this allowance. Their actual elapsed time, along with all other projection
    work, is deducted before the directional checker is called. If projection
    consumes the deadline, the directional checker receives zero and reports
    ``unknown``; it never gets a fresh full budget. Private uninterpreted sort
    carriers are not quantified by term projection. SAT witnesses involving
    such sorts are revalidated against both original relations at the same
    observable assignment, in independent solvers and within this deadline.
    A common feasible tuple plus independent exclusion of all other tuples
    yields an explicitly identified singleton observable relation certificate.
    """
    from .directional_equivalence import check_equivalence
    from .private_sort_witness import (original_relation, private_sort_names,
        revalidate_private_sort_counterexample)

    # Retain the unoptimized input relations for independent model checks.
    # Materialization also keeps iterator inputs usable by both paths.
    reference_assertions = list(reference_assertions)
    candidate_assertions = list(candidate_assertions)
    reference_bridges = list(reference_bridges)
    candidate_bridges = list(candidate_bridges)

    for name, value, minimum in (
            ("total_timeout_ms", total_timeout_ms, 0),
            ("per_obligation_timeout_ms", per_obligation_timeout_ms, 1)):
        if value is None:
            continue
        if isinstance(value, bool) or not isinstance(value, int):
            raise TypeError(f"{name} must be an integer number of milliseconds")
        if value < minimum:
            raise ValueError(f"{name} must be at least {minimum}")
    if preprocessing_budget_ms is None and total_timeout_ms is not None:
        preprocessing_budget_ms = min(35000, total_timeout_ms // 3)
    if preprocessing_budget_ms is not None and (isinstance(preprocessing_budget_ms, bool)
            or not isinstance(preprocessing_budget_ms, int)):
        raise TypeError("preprocessing_budget_ms must be an integer number of milliseconds")
    if preprocessing_budget_ms is not None and preprocessing_budget_ms < 0:
        raise ValueError("preprocessing_budget_ms must be nonnegative")

    started = time.monotonic()
    deadline = None if total_timeout_ms is None else started + total_timeout_ms / 1000.0
    prep_limits = [value for value in (deadline, None if preprocessing_budget_ms is None
                   else started + preprocessing_budget_ms / 1000.0) if value is not None]
    prep_deadline = min(prep_limits) if prep_limits else None

    def remaining_preprocessing_ms():
        return None if prep_deadline is None else max(0, int((prep_deadline - time.monotonic()) * 1000))

    if progress_callback is not None:
        progress_callback({"component": "relation", "phase": "reference_projection.start"})
    reference_started = time.monotonic()
    reference = candidate_projection(
        reference_assertions, reference_bridges, reference_cost_bridge,
        guarded_bool_budget_ms=remaining_preprocessing_ms(),
        progress_callback=progress_callback)
    reference_projection_elapsed_ms = int(
        (time.monotonic() - reference_started) * 1000)
    if progress_callback is not None:
        progress_callback({
            "component": "relation", "phase": "reference_projection.done",
            "elapsed_ms": reference_projection_elapsed_ms})
        progress_callback({"component": "relation", "phase": "candidate_projection.start"})
    candidate_started = time.monotonic()
    candidate = candidate_projection(
        candidate_assertions, candidate_bridges, candidate_cost_bridge,
        guarded_bool_budget_ms=remaining_preprocessing_ms(),
        progress_callback=progress_callback)
    candidate_projection_elapsed_ms = int(
        (time.monotonic() - candidate_started) * 1000)
    if progress_callback is not None:
        progress_callback({
            "component": "relation", "phase": "candidate_projection.done",
            "elapsed_ms": candidate_projection_elapsed_ms})
    reference_body, reference_aliases = original_relation(
        reference_assertions, reference_bridges, reference_cost_bridge)
    candidate_body, candidate_aliases = original_relation(
        candidate_assertions, candidate_bridges, candidate_cost_bridge)
    private_sorts = private_sort_names([reference_body, candidate_body])
    after_projection = time.monotonic()
    preprocessing_elapsed_ms = int((after_projection - started) * 1000)
    directional_budget_ms = (None if deadline is None else
                             max(0, int((deadline - after_projection) * 1000)))
    if progress_callback is not None:
        progress_callback({
            "component": "relation", "phase": "directional_check.start",
            "budget_ms": directional_budget_ms})
    comparison = check_equivalence(
        reference.formula, candidate.formula,
        total_timeout_ms=directional_budget_ms,
        per_obligation_timeout_ms=per_obligation_timeout_ms,
        simplify=simplify)
    counterexample_validation = None
    if private_sorts and comparison.status == "counterexample":
        comparison, counterexample_validation = revalidate_private_sort_counterexample(
            comparison, reference.formula, candidate.formula,
            reference_body=reference_body, candidate_body=candidate_body,
            reference_aliases=reference_aliases, candidate_aliases=candidate_aliases,
            private_sorts=private_sorts, deadline=deadline,
            per_query_timeout_ms=per_obligation_timeout_ms,
            progress_callback=progress_callback)
    if progress_callback is not None:
        progress_callback({
            "component": "relation", "phase": "directional_check.done",
            "elapsed_ms": comparison.elapsed_ms,
            "status": comparison.status})
    return RelationEquivalenceCheck(
        reference, candidate, comparison, total_timeout_ms,
        preprocessing_budget_ms, preprocessing_elapsed_ms,
        directional_budget_ms, int((time.monotonic() - started) * 1000),
        reference_projection_elapsed_ms, candidate_projection_elapsed_ms,
        counterexample_validation)
