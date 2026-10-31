"""Exact equivalence checking by common-conjunct factoring and entailment.

The checker preserves the complete input formulas. It flattens conjunctions,
factors only structurally identical conjuncts, then proves each remaining
conjunct in both directions using incremental solver scopes. A relation is
equivalent only when every entailment obligation is UNSAT. SAT is a concrete
directional counterexample; solver or wall-budget exhaustion remains unknown.
An incomplete quantified check may also be discharged by exact finite-source
exhaustion: every complete source tuple must admit the target sentence, and
the remaining source must be UNSAT. Unsupported/infinite projections stay
unknown. This strategy never introduces a source-domain bound.
"""
from dataclasses import dataclass
import time


@dataclass(frozen=True)
class DirectionResult:
    direction: str
    obligations: int
    proved: int
    counterexample_conjunct: str = None
    counterexample_model: str = None
    unknown_obligations: int = 0
    unknown_reasons: tuple = ()
    not_run_obligations: int = 0
    budget_exhausted: bool = False
    counterexample_values: tuple = ()
    finite_source_checks: tuple = ()


@dataclass(frozen=True)
class EquivalenceResult:
    status: str
    equivalent: object
    common_conjuncts: int
    left_only_conjuncts: int
    right_only_conjuncts: int
    left_implies_right: DirectionResult
    right_implies_left: DirectionResult
    elapsed_ms: int
    preprocessing_simplified: bool
    finite_table_rewrites: int = 0
    canonical_reorders: int = 0
    existential_conjuncts_lifted: int = 0


def _flatten_and(z3, expression):
    terms = []
    stack = [expression]
    while stack:
        current = stack.pop()
        if z3.is_and(current):
            stack.extend(reversed(current.children()))
        else:
            terms.append(current)
    return terms


def _unique_by_id(terms):
    unique = {}
    for term in terms:
        unique.setdefault(term.get_id(), term)
    return unique


def _bounded_simplify(z3, expression, timeout_ms):
    """Run simplify, with no timer when the caller explicitly selects None."""
    if timeout_ms is not None and timeout_ms <= 0:
        return expression, False
    goal = z3.Goal(ctx=expression.ctx)
    goal.add(expression)
    try:
        tactic = z3.Tactic("simplify", ctx=expression.ctx)
        result = (tactic if timeout_ms is None else z3.TryFor(tactic, timeout_ms))(goal)
    except z3.Z3Exception:
        return expression, False
    if len(result) != 1 or result[0].precision() != z3.Z3_GOAL_PRECISE:
        return expression, False
    rewritten = list(result[0])
    if not rewritten:
        return z3.BoolVal(True, ctx=expression.ctx), True
    if len(rewritten) == 1:
        return rewritten[0], True
    return z3.And(*rewritten), True


def _unknown_direction(direction, obligations, proved, reason):
    return DirectionResult(direction, obligations, proved,
                           unknown_obligations=obligations - proved,
                           unknown_reasons=(reason,), budget_exhausted=True)


def _check_direction(z3, ctx, direction, common, source_only, target_only,
                     deadline, per_obligation_timeout_ms):
    solver = z3.Solver(ctx=ctx)
    solver.add(*(common + source_only))
    proved = 0
    unknown = 0
    reasons = []
    finite_checks = []
    for position, target in enumerate(target_only):
        remaining_ms = (None if deadline is None else
                        int((deadline - time.monotonic()) * 1000))
        if remaining_ms is not None and remaining_ms <= 0:
            unknown += len(target_only) - position
            reasons.append("total wall-time budget exhausted")
            return DirectionResult(direction, len(target_only), proved,
                                   unknown_obligations=unknown,
                                   unknown_reasons=tuple(reasons),
                                   budget_exhausted=True,
                                   finite_source_checks=tuple(finite_checks))
        limits = [value for value in (per_obligation_timeout_ms, remaining_ms)
                  if value is not None]
        solver.set(timeout=max(1, min(limits)) if limits else 0)
        obligation_deadline = deadline
        if per_obligation_timeout_ms is not None:
            local_deadline = time.monotonic() + per_obligation_timeout_ms / 1000.0
            obligation_deadline = (local_deadline if deadline is None else
                                   min(deadline, local_deadline))
        solver.push()
        solver.add(z3.Not(target))
        answer = solver.check()
        model = solver.model() if answer == z3.sat else None
        if model is not None:
            from .counterexample_coordinates import scalar_model_values
            values = scalar_model_values(model)
            model = str(model)
        else:
            values = ()
        reason = solver.reason_unknown() if answer == z3.unknown else None
        solver.pop()
        if answer == z3.unknown:
            from dataclasses import asdict
            from .projection import contains_quantifier
            if contains_quantifier(target):
                from .finite_source_entailment import prove_finite_source_entailment
                assertions = list(solver.assertions())
                source = (z3.And(*assertions) if assertions else z3.BoolVal(True, ctx=ctx))
                fallback = prove_finite_source_entailment(
                    source, target, deadline=obligation_deadline)
                finite_checks.append(dict(target_position=position,
                                          original_unknown_reason=reason,
                                          **asdict(fallback)))
                if fallback.status == "proved":
                    answer = z3.unsat
                elif fallback.status == "counterexample":
                    answer = z3.sat
                    model = fallback.counterexample_model
                    values = fallback.counterexample_values
                else:
                    reason = (reason or "solver returned unknown") + "; finite source: " + fallback.reason
        if answer == z3.unsat:
            proved += 1
        elif answer == z3.sat:
            return DirectionResult(direction, len(target_only), proved,
                                   str(target), model, unknown,
                                   tuple(reasons),
                                   not_run_obligations=len(target_only)-position-1,
                                   counterexample_values=values,
                                   finite_source_checks=tuple(finite_checks))
        else:
            unknown += 1
            reasons.append(reason or "solver returned unknown")
    return DirectionResult(direction, len(target_only), proved,
                           unknown_obligations=unknown,
                           unknown_reasons=tuple(reasons),
                           finite_source_checks=tuple(finite_checks))


def check_equivalence(left, right, *, total_timeout_ms=30000,
                      per_obligation_timeout_ms=1000, simplify=True):
    """Check exact equivalence of two Boolean relations.

    Args:
        left, right: Boolean Z3 expressions in the same context. Each formula
            is retained in full; only top-level conjunctions are flattened.
        total_timeout_ms: overall deadline, including bounded simplification
            and both directional checks. Zero produces an unknown result;
            None removes this deadline.
        per_obligation_timeout_ms: maximum solver time for one entailment;
            None removes this limit. Set both limits to None for an unbounded run.
        simplify: apply Z3's ordinary simplify tactic to each complete formula
            before exact conjunct factoring. A timed-out simplify step falls
            back to its original formula; it never changes the proof obligation.

    Returns an :class:`EquivalenceResult`. ``equivalent`` is ``True`` only
    when every directional obligation was UNSAT, ``False`` on a SAT witness,
    and ``None`` if any obligation or the total budget remains unknown.
    Quantifiers and all non-And structure remain inside their original terms.
    """
    import z3

    if not z3.is_bool(left) or not z3.is_bool(right):
        raise TypeError("equivalence inputs must be Boolean Z3 expressions")
    if left.ctx != right.ctx:
        raise ValueError("equivalence inputs must use the same Z3 context")
    for name, value, minimum in (
            ("total_timeout_ms", total_timeout_ms, 0),
            ("per_obligation_timeout_ms", per_obligation_timeout_ms, 1)):
        if value is None:
            continue
        if isinstance(value, bool) or not isinstance(value, int):
            raise TypeError(f"{name} must be an integer number of milliseconds")
        if value < minimum:
            raise ValueError(f"{name} must be at least {minimum}")

    started = time.monotonic()
    deadline = None if total_timeout_ms is None else started + total_timeout_ms / 1000.0
    def remaining_ms():
        return None if deadline is None else max(0, int((deadline - time.monotonic()) * 1000))
    preprocessing_simplified = False
    finite_table_rewrites = canonical_reorders = 0
    existential_conjuncts_lifted = 0
    if simplify and total_timeout_ms != 0:
        from .finite_scalar_tables import normalize_finite_scalar_tables

        normalized_left = normalize_finite_scalar_tables(left, deadline=deadline)
        normalized_right = normalize_finite_scalar_tables(right, deadline=deadline)
        left, right = normalized_left.formula, normalized_right.formula
        finite_table_rewrites = normalized_left.table_rewrites + normalized_right.table_rewrites
        canonical_reorders = normalized_left.canonical_reorders + normalized_right.canonical_reorders
        remaining = remaining_ms()
        left, left_ok = _bounded_simplify(z3, left, remaining)
        remaining = remaining_ms()
        right, right_ok = _bounded_simplify(z3, right, remaining)
        preprocessing_simplified = left_ok and right_ok
        # A hidden witness must not prevent separate obligations for bounds or
        # other conjuncts containing only observable values. Keep the complete
        # quantified residual; this rule neither guesses witnesses nor domains.
        from .existential_conjuncts import factor_existential_conjuncts
        left_factored = factor_existential_conjuncts(left, deadline=deadline)
        right_factored = factor_existential_conjuncts(right, deadline=deadline)
        left, right = left_factored.formula, right_factored.formula
        existential_conjuncts_lifted = (left_factored.lifted_conjuncts
                                      + right_factored.lifted_conjuncts)

    left_terms = _unique_by_id(_flatten_and(z3, left))
    right_terms = _unique_by_id(_flatten_and(z3, right))
    common_ids = left_terms.keys() & right_terms.keys()
    common = [left_terms[term_id] for term_id in common_ids]
    left_only = [term for term_id, term in left_terms.items()
                 if term_id not in common_ids]
    right_only = [term for term_id, term in right_terms.items()
                  if term_id not in common_ids]

    if total_timeout_ms == 0 or (deadline is not None and time.monotonic() >= deadline):
        left_result = _unknown_direction("left_implies_right",
                                          len(right_only), 0,
                                          "total wall-time budget exhausted")
        right_result = _unknown_direction("right_implies_left",
                                           len(left_only), 0,
                                           "total wall-time budget exhausted")
    else:
        left_result = _check_direction(z3, left.ctx, "left_implies_right", common,
                                       left_only, right_only, deadline,
                                       per_obligation_timeout_ms)
        if left_result.counterexample_conjunct is not None:
            right_result = DirectionResult("right_implies_left",
                                           len(left_only), 0,
                                           not_run_obligations=len(left_only))
        else:
            right_result = _check_direction(z3, left.ctx, "right_implies_left", common,
                                            right_only, left_only, deadline,
                                            per_obligation_timeout_ms)

    counterexample = (left_result.counterexample_conjunct is not None
                      or right_result.counterexample_conjunct is not None)
    unknown = (left_result.unknown_obligations > 0
               or right_result.unknown_obligations > 0
               or left_result.budget_exhausted
               or right_result.budget_exhausted)
    if counterexample:
        status, equivalent = "counterexample", False
    elif unknown:
        status, equivalent = "unknown", None
    else:
        status, equivalent = "equivalent", True
    return EquivalenceResult(
        status, equivalent, len(common), len(left_only), len(right_only),
        left_result, right_result,
        int((time.monotonic() - started) * 1000), preprocessing_simplified,
        finite_table_rewrites, canonical_reorders, existential_conjuncts_lifted)
