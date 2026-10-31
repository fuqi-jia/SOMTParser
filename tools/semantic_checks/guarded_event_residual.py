"""A sufficient residual certificate for guarded integer event conjunctions.

Only bounds asserted in the original shared context justify false guards.
Every guarded source event must match the complete target conjunction under
the existing exact Boolean structure checker. All other source conjuncts
remain in the residual. UNSAT of that residual implies UNSAT of the original
context-and-XOR; a SAT residual is only inconclusive.
"""
from dataclasses import dataclass

import z3

from .boolean_structure import structural_equivalence


@dataclass(frozen=True)
class GuardedEventResidual:
    formula: object
    audit: dict


def _conjuncts(root):
    result, pending = [], [root]
    while pending:
        node = pending.pop()
        if z3.is_and(node):
            pending.extend(reversed(node.children()))
        else:
            result.append(node)
    return result


def _integer(node):
    if z3.is_int_value(node):
        return node.as_long()
    if (z3.is_app_of(node, z3.Z3_OP_UMINUS)
            and z3.is_int_value(node.arg(0))):
        return -node.arg(0).as_long()
    return None


def _coordinate(node):
    return (z3.is_const(node) and node.sort().kind() == z3.Z3_INT_SORT
            and node.decl().kind() == z3.Z3_OP_UNINTERPRETED)


def _shared_lower_bounds(context):
    bounds = {}
    for index, original in enumerate(context):
        negated = z3.is_not(original)
        node = original.arg(0) if negated else original
        if not z3.is_app(node) or node.num_args() != 2:
            continue
        kind = node.decl().kind()
        if kind not in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
            continue
        if negated:
            kind = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_LT: z3.Z3_OP_GE,
                    z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_GT: z3.Z3_OP_LE}[kind]
        coordinate, limit = node.arg(0), _integer(node.arg(1))
        if not _coordinate(coordinate) or limit is None:
            coordinate, limit = node.arg(1), _integer(node.arg(0))
            if not _coordinate(coordinate) or limit is None:
                continue
            kind = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
                    z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}[kind]
        if kind not in (z3.Z3_OP_GE, z3.Z3_OP_GT):
            continue
        limit += int(kind == z3.Z3_OP_GT)
        identity = coordinate.get_id()
        if identity not in bounds or limit > bounds[identity][0]:
            bounds[identity] = (limit, index)
    return bounds


def _sum_lower_bound(root, bounds):
    """Exact integers, addition and asserted Int coordinate lower bounds only."""
    pending, value, references = [root], 0, []
    while pending:
        node = pending.pop()
        numeral = _integer(node)
        if numeral is not None:
            value += numeral
        elif _coordinate(node) and node.get_id() in bounds:
            lower, index = bounds[node.get_id()]
            value += lower
            references.append(index)
        elif z3.is_add(node) and node.sort().kind() == z3.Z3_INT_SORT:
            pending.extend(node.children())
        else:
            return None
    return value, references


def prepare_guarded_event_residual(query, *, retain_target_events=False):
    """Return a sufficient residual, or None when this narrow rule does not fit.

    The input is the actual complete shared-context AND XOR query. The XOR
    must be its final conjunct. No facts from either XOR branch are promoted
    to the shared context. By default the residual uses the shared context
    alone, a stronger sufficient condition. The optional target-event premise
    is sound after the complete event conjunction correspondence succeeds.
    """
    if not z3.is_and(query) or query.num_args() < 2:
        return None
    difference = query.arg(query.num_args() - 1)
    if not z3.is_app_of(difference, z3.Z3_OP_XOR) or difference.num_args() != 2:
        return None
    context = []
    for node in query.children()[:-1]:
        context.extend(_conjuncts(node))
    bounds = _shared_lower_bounds(context)
    left, right = difference.children()
    clauses = _conjuncts(left)
    events, residuals, guards = [], [], []
    for index, clause in enumerate(clauses):
        selected = None
        if z3.is_or(clause) and clause.num_args() == 2:
            for guard_index, guard in enumerate(clause.children()):
                if not z3.is_le(guard):
                    continue
                limit = _integer(guard.arg(1))
                lower = _sum_lower_bound(guard.arg(0), bounds)
                if limit is None or lower is None or lower[0] <= limit:
                    continue
                selected = clause.arg(1 - guard_index)
                guards.append(dict(source_index=index, guard_index=guard_index,
                                   guard=guard.sexpr(), lower_bound=lower[0],
                                   upper_test=limit,
                                   retained_context_indices=lower[1]))
                break
        if selected is None:
            residuals.append((index, clause))
        else:
            events.append(selected)
    if not guards:
        return None
    event_conjunction = z3.And(*events)
    correspondence = structural_equivalence(event_conjunction, right)
    if not correspondence['equivalent']:
        return None
    remaining = z3.And(*[node for _, node in residuals]) if residuals else z3.BoolVal(True, ctx=query.ctx)
    premises = context + ([right] if retain_target_events else [])
    formula = z3.And(*premises, z3.Not(remaining))
    audit = dict(kind='shared-bound-guarded-event-residual',
                 source_conjuncts=len(clauses), target_conjuncts=len(_conjuncts(right)),
                 shared_context_conjuncts=len(context), removed_guards=guards,
                 residual_source_indices=[index for index, _ in residuals],
                 target_event_premise=retain_target_events,
                 complete_event_correspondence=correspondence,
                 acceptance_requires='UNSAT of this exact complete residual',
                 sat_residual_means='inconclusive')
    assert sorted([g['source_index'] for g in guards] + audit['residual_source_indices']) == list(range(len(clauses)))
    return GuardedEventResidual(formula, audit)
