"""Necessary local consequences of original nonnegative indicator sums.

If each original summand is nonnegative, deleting summands from a sum <= k
preserves implication. This is only a proof context: it never replaces an
original formula or establishes either equivalence direction by itself.
"""
import z3
from .qf_conjuncts import _signatures


def nonnegative_sum_plans(conjuncts):
    """Recognize integer sums whose nonnegativity needs no assumptions."""
    plans = {}
    roots = []
    for identity, clause in conjuncts.items():
        if not z3.is_le(clause) or not z3.is_int_value(clause.arg(1)):
            continue
        total, bound = clause.children()
        if not z3.is_add(total) or total.sort().kind() != z3.Z3_INT_SORT:
            continue
        terms = tuple(total.children())
        def nonnegative(term):
            if z3.is_int_value(term):
                return term.as_long() >= 0
            return (z3.is_app_of(term, z3.Z3_OP_ITE)
                    and z3.is_int_value(term.arg(1)) and term.arg(1).as_long() >= 0
                    and z3.is_int_value(term.arg(2)) and term.arg(2).as_long() >= 0)
        if all(nonnegative(term) for term in terms):
            plans[identity] = (terms, bound)
            roots.extend(terms)
    signatures = _signatures(roots)
    if signatures is None:
        return {}, {}
    return plans, signatures


def project_nonnegative_sums(plans, signatures, context_ids, declarations):
    """Retain only summands entirely inside the requested declaration set."""
    consequences = {}
    records = []
    for identity in sorted(context_ids):
        plan = plans.get(identity)
        if plan is None:
            continue
        terms, bound = plan
        kept = [i for i, term in enumerate(terms)
                if signatures[term.get_id()] <= declarations]
        if len(kept) == len(terms):
            continue
        total = z3.Sum(*[terms[i] for i in kept]) if kept else z3.IntVal(0, ctx=bound.ctx)
        consequence = z3.simplify(total <= bound)
        if z3.is_true(consequence):
            continue
        consequences[consequence.get_id()] = consequence
        records.append(dict(original_conjunct=identity, original_terms=len(terms),
                            retained_terms=kept, integer_upper_bound=bound.as_long()))
    return tuple(consequences.values()), records
