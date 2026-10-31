"""Validate observable counterexamples independently of private sort carriers.

Closing private terms does not quantify the carrier of an uninterpreted sort.
A negated projected formula can consequently be true merely because the solver
chose too small a carrier. A relation counterexample needs a portable observable
assignment admitted by one original relation and excluded by the other, each
with its own carrier and interpretation choices.
"""
from dataclasses import dataclass, replace
import time


@dataclass(frozen=True)
class PrivateSortWitnessValidation:
    status: str
    private_sorts: tuple
    direction: str
    observable_values: tuple = ()
    witness_status: str = None
    antecedent_status: str = None
    consequent_status: str = None
    reason: str = None
    elapsed_ms: int = 0
    budget_exhausted: bool = False
    original_counterexample_model: str = None
    antecedent_other_status: str = None
    consequent_other_status: str = None


@dataclass(frozen=True)
class SingletonObservableInclusion:
    """Inclusion follows from two independent observable relation facts.

    The source has no tuple outside v (UNSAT); the target admits v (SAT).
    These are not same-carrier directional entailment obligations.
    """
    direction: str
    obligations: int = 2
    proved: int = 2
    counterexample_conjunct: str = None
    counterexample_model: str = None
    unknown_obligations: int = 0
    unknown_reasons: tuple = ()
    not_run_obligations: int = 0
    budget_exhausted: bool = False
    proof_kind: str = "independent-singleton-observable-inclusion"


@dataclass(frozen=True)
class SingletonRelationEquivalence:
    """An equivalence certificate distinct from same-carrier entailment.

    Conjunct statistics and the original same-carrier comparison are retained
    as provenance. Each reported inclusion uses the independent SAT/UNSAT
    facts in the accompanying witness validation, not the failed raw proof.
    """
    status: str
    equivalent: bool
    common_conjuncts: int
    left_only_conjuncts: int
    right_only_conjuncts: int
    left_implies_right: SingletonObservableInclusion
    right_implies_left: SingletonObservableInclusion
    elapsed_ms: int
    preprocessing_simplified: bool
    raw_same_carrier_comparison: object
    proof_kind: str = "independent-singleton-observable-equivalence"
    finite_table_rewrites: int = 0
    canonical_reorders: int = 0


def private_sort_names(expressions):
    """Include binder-only sorts and sorts nested in containers/datatypes."""
    import z3

    pending = list(expressions)
    visited_terms = set()
    visited_sorts = set()
    private = set()

    def inspect_sort(sort):
        if sort.get_id() in visited_sorts:
            return
        visited_sorts.add(sort.get_id())
        kind = sort.kind()
        if kind == z3.Z3_UNINTERPRETED_SORT:
            private.add(sort.sexpr())
        elif kind == z3.Z3_ARRAY_SORT:
            # Arrays may have more than one index sort.
            arity = z3.Z3_get_array_arity(sort.ctx_ref(), sort.ast)
            for index in range(arity):
                inspect_sort(sort.domain_n(index))
            inspect_sort(sort.range())
        elif kind == z3.Z3_DATATYPE_SORT:
            for index in range(sort.num_constructors()):
                constructor = sort.constructor(index)
                for argument in range(constructor.arity()):
                    inspect_sort(constructor.domain(argument))
        elif kind in (z3.Z3_SEQ_SORT, z3.Z3_RE_SORT):
            inspect_sort(sort.basis())
        elif kind not in (z3.Z3_BOOL_SORT, z3.Z3_INT_SORT, z3.Z3_REAL_SORT,
                          z3.Z3_BV_SORT, z3.Z3_FINITE_DOMAIN_SORT, z3.Z3_CHAR_SORT,
                          z3.Z3_FLOATING_POINT_SORT, z3.Z3_ROUNDING_MODE_SORT):
            # An unrecognized composite sort is never silently assumed to
            # have a fixed built-in carrier.
            private.add("opaque-sort:" + sort.sexpr())

    while pending:
        expression = pending.pop()
        if expression.get_id() in visited_terms:
            continue
        visited_terms.add(expression.get_id())
        inspect_sort(expression.sort())
        if z3.is_quantifier(expression):
            for index in range(expression.num_vars()):
                inspect_sort(expression.var_sort(index))
            pending.append(expression.body())
        elif z3.is_app(expression):
            declaration = expression.decl()
            for index in range(declaration.arity()):
                inspect_sort(declaration.domain(index))
            pending.extend(expression.children())
    return tuple(sorted(private))


def original_relation(assertions, bridges, cost_bridge):
    """Keep the exact original assertions and every visible bridge."""
    import z3

    pairs = list(bridges)
    if cost_bridge is not None:
        pairs.append(cost_bridge)
    terms = list(assertions) + [alias == term for alias, term in pairs]
    return z3.And(*terms), [alias for alias, _ in pairs]


def revalidate_private_sort_counterexample(comparison, reference_projection,
                                          candidate_projection, *,
                                          reference_body, candidate_body,
                                          reference_aliases, candidate_aliases,
                                          private_sorts, deadline,
                                          per_query_timeout_ms,
                                          progress_callback=None):
    """Return a sound comparison plus an auditable witness-check receipt.

    Universal same-carrier UNSAT entailments remain sufficient for observable
    inclusion. Only SAT counterexamples need independent carrier validation.
    Each new solver uses the remaining original total deadline, or no deadline
    when it is None. A None per-query limit also removes that limit. If a tuple
    is admitted by both relations, independent exclusion proofs can certify
    that both observable relations are the same exact singleton.
    """
    import z3

    started = time.monotonic()
    left = comparison.left_implies_right
    right = comparison.right_implies_left
    forward = left.counterexample_conjunct is not None
    direction = left if forward else right
    source_projection = reference_projection if forward else candidate_projection
    target_projection = candidate_projection if forward else reference_projection
    source_body = reference_body if forward else candidate_body
    target_body = candidate_body if forward else reference_body
    receipt = dict(status="unknown", private_sorts=tuple(private_sorts),
                   direction=direction.direction,
                   original_counterexample_model=direction.counterexample_model)

    def remaining_ms():
        return None if deadline is None else max(0, int((deadline - time.monotonic()) * 1000))

    def finish(reason, certified=False, singleton=False):
        elapsed = int((time.monotonic() - started) * 1000)
        remaining = remaining_ms()
        exhausted = remaining is not None and remaining <= 0
        receipt.update(reason=reason, elapsed_ms=elapsed,
                       budget_exhausted=exhausted)
        if singleton:
            revised = SingletonRelationEquivalence(
                "equivalent", True, comparison.common_conjuncts,
                comparison.left_only_conjuncts, comparison.right_only_conjuncts,
                SingletonObservableInclusion("left_implies_right"),
                SingletonObservableInclusion("right_implies_left"),
                comparison.elapsed_ms + elapsed, comparison.preprocessing_simplified,
                comparison, finite_table_rewrites=getattr(comparison, "finite_table_rewrites", 0),
                canonical_reorders=getattr(comparison, "canonical_reorders", 0))
        elif certified:
            revised_direction = replace(direction,
                counterexample_conjunct=str(target_projection),
                counterexample_model=str(receipt["observable_values"]),
                counterexample_values=receipt["observable_values"])
            revised = replace(comparison,
                **{direction.direction: revised_direction},
                elapsed_ms=comparison.elapsed_ms + elapsed)
        else:
            revised_direction = replace(direction,
                counterexample_conjunct=None, counterexample_model=None,
                counterexample_values=(),
                unknown_obligations=direction.unknown_obligations + 1,
                unknown_reasons=direction.unknown_reasons + (reason,),
                budget_exhausted=direction.budget_exhausted or exhausted)
            revised = replace(comparison, status="unknown", equivalent=None,
                **{direction.direction: revised_direction},
                elapsed_ms=comparison.elapsed_ms + elapsed)
        return revised, PrivateSortWitnessValidation(**receipt)

    def query(name, formula):
        remaining = remaining_ms()
        if remaining is not None and remaining <= 0:
            return "unknown", None, "total wall-time budget exhausted"
        limits = [value for value in (per_query_timeout_ms, remaining) if value is not None]
        timeout = min(limits) if limits else None
        if progress_callback is not None:
            progress_callback({"component": "relation", "phase": name + ".start",
                               "budget_ms": timeout})
        solver = z3.Solver(ctx=formula.ctx)
        solver.set(timeout=timeout if timeout is not None else 0)
        solver.add(formula)
        status = solver.check()
        model = solver.model() if status == z3.sat else None
        reason = solver.reason_unknown() if status == z3.unknown else None
        if progress_callback is not None:
            progress_callback({"component": "relation", "phase": name + ".done",
                               "status": str(status), "reason": reason})
        return str(status), model, reason

    by_id = {alias.get_id(): alias for alias in reference_aliases}
    if set(by_id) != {alias.get_id() for alias in candidate_aliases}:
        return finish("private-sort-alignment-required: observable aliases differ")
    aliases = list(by_id.values())
    portable_kinds = {z3.Z3_BOOL_SORT, z3.Z3_INT_SORT,
                      z3.Z3_REAL_SORT, z3.Z3_BV_SORT}
    if any(alias.sort().kind() not in portable_kinds for alias in aliases):
        return finish("private-sort-alignment-required: domain-valued or unsupported observables")

    status, model, reason = query("counterexample_witness",
        z3.And(source_projection, z3.Not(target_projection)))
    receipt["witness_status"] = status
    if status != "sat":
        return finish("private-sort-alignment-required: witness replay " + status
                      + (": " + reason if reason else ""))
    assignments = []
    values = []
    for alias in aliases:
        value = model.eval(alias, model_completion=True)
        if not (z3.is_true(value) or z3.is_false(value)
                or z3.is_int_value(value) or z3.is_rational_value(value)
                or z3.is_bv_value(value)):
            return finish("private-sort-alignment-required: observable has no portable closed value")
        assignments.append(alias == value)
        values.append((alias.sexpr(), alias.sort().sexpr(), value.sexpr()))
    receipt["observable_values"] = tuple(values)

    status, _, reason = query("counterexample_antecedent",
        z3.And(source_body, *assignments))
    receipt["antecedent_status"] = status
    if status != "sat":
        return finish("private-sort-alignment-required: independent antecedent " + status
                      + (": " + reason if reason else ""))
    status, _, reason = query("counterexample_consequent",
        z3.And(target_body, *assignments))
    receipt["consequent_status"] = status
    if status == "unsat":
        receipt["status"] = "certified-counterexample"
        return finish("independent original relations certify observable counterexample",
                      certified=True)
    if status == "sat":
        receipt["status"] = "carrier-dependent-witness"
        # Each relation is SAT at this same portable tuple, with independent
        # choices of private carriers. Prove that neither relation admits any
        # other output/cost tuple. For no observables, And() is true: the only
        # tuple is (), and the two existing SAT witnesses establish equality.
        outside = z3.Not(z3.And(*assignments)) if assignments else z3.BoolVal(False, ctx=source_body.ctx)
        status, _, reason = query("singleton_antecedent_outside",
            z3.And(source_body, outside))
        receipt["antecedent_other_status"] = status
        if status != "unsat":
            return finish("private-sort-alignment-required: independent antecedent has no singleton certificate ("
                          + status + (": " + reason if reason else "") + ")")
        status, _, reason = query("singleton_consequent_outside",
            z3.And(target_body, outside))
        receipt["consequent_other_status"] = status
        if status != "unsat":
            return finish("private-sort-alignment-required: independent consequent has no singleton certificate ("
                          + status + (": " + reason if reason else "") + ")")
        receipt["status"] = "certified-singleton-equivalence"
        return finish("both independent original relations admit exactly the same observable/cost tuple",
                      singleton=True)
    return finish("private-sort-alignment-required: independent consequent unknown"
                  + (": " + reason if reason else ""))
