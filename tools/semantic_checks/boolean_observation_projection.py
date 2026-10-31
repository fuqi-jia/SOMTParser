"""Eliminate hidden Bool leaves through explicit Int 0/1 observations.

For a Boolean leaf b and observable integer o, the bridge o=If(b,1,0)
is a bijection between b and o in {0,1}. This module applies that exact
change of variables to the COMPLETE relation, including cost equations.
It is a projection rule, not an equivalence between formulas with b free.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class BooleanObservationProjection:
    body: object
    bridges: tuple
    eliminated_roots: tuple
    retained_roots: tuple
    observed_boolean_cells: int
    weighted_ites: int


def eliminate_boolean_observations(body, observation_bridges):
    """Return an exact existential projection after reversible leaf encoding.

    The caller must use its ordinary fresh scalar observation aliases and
    existentially hide the original Boolean constants/arrays. We additionally
    require each bridge to occur as an unconditional top-level equality.
    Only Bool constants and complete concrete Int-indexed array cells qualify.
    A whole root commits only when it disappears from the transformed body;
    symbolic reads, array equality/prefix uses and UF leaves remain unchanged.
    All original assertions and duplicate bridges survive substitution.
    Quantifier contexts are refused, avoiding binder capture entirely.
    """
    import z3
    from .defined_array_cells import _concrete_scalar_select
    from .projection import contains_quantifier, free_constants

    bridges = tuple(observation_bridges)
    if not z3.is_bool(body):
        raise TypeError('Boolean observation projection requires a Bool body')
    unchanged = BooleanObservationProjection(body, bridges, (), (), 0, 0)
    # Most large source relations have only directly observed Int cells. Do
    # not traverse their complete DAG just to discover this rule is inapplicable.
    potential = []
    for alias, term in bridges:
        if alias.ctx != body.ctx or term.ctx != body.ctx:
            raise ValueError('observation and body contexts differ')
        if not (z3.is_const(alias) and z3.is_int(alias)
                and alias.decl().kind() == z3.Z3_OP_UNINTERPRETED
                and z3.is_app(term) and term.decl().kind() == z3.Z3_OP_ITE):
            continue
        condition, yes, no = term.children()
        if (z3.is_bool(condition) and z3.is_int_value(yes) and yes.as_long() == 1
                and z3.is_int_value(no) and no.as_long() == 0):
            potential.append((alias, term))
    if not potential:
        return unchanged
    if contains_quantifier(body):
        return unchanged

    # Inspect only unconditional conjunction children. A bridge under OR/NOT
    # does not justify restricting its integer alias to 0/1.
    equalities, stack, seen = set(), [body], set()
    while stack:
        node = stack.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_and(node):
            stack.extend(node.children())
        elif z3.is_eq(node):
            a, b = node.children()
            equalities.add((a.get_id(), b.get_id()))
            equalities.add((b.get_id(), a.get_id()))

    groups = {}
    for alias, term in potential:
        if not (z3.is_const(alias) and z3.is_int(alias)
                and alias.decl().kind() == z3.Z3_OP_UNINTERPRETED
                and z3.is_app(term) and term.decl().kind() == z3.Z3_OP_ITE
                and (alias.get_id(), term.get_id()) in equalities):
            continue
        condition, yes, no = term.children()
        if not (z3.is_int_value(yes) and yes.as_long() == 1
                and z3.is_int_value(no) and no.as_long() == 0):
            continue
        if (z3.is_const(condition) and z3.is_bool(condition)
                and condition.decl().kind() == z3.Z3_OP_UNINTERPRETED):
            root = condition
        else:
            cell = _concrete_scalar_select(z3, condition)
            if cell is None or not z3.is_bool(condition):
                continue
            root = cell[0]
        group = groups.setdefault(root.get_id(), {'root': root, 'cells': {}})
        # The first alias represents duplicate observations. Every remaining
        # bridge is retained, so equality to that representative is enforced.
        group['cells'].setdefault(condition.get_id(), (condition, alias))
    if not groups:
        return unchanged

    def rewrite(active):
        leaves = {key: pair for group in active.values()
                  for key, pair in group['cells'].items()}
        memo, weighted, pending = {}, 0, [(body, False)]
        # Rewrite bridges in the SAME substitution environment for subsequent
        # projection phases, without introducing additional assertions there.
        pending.extend((term, False) for _, term in bridges)
        while pending:
            node, ready = pending.pop()
            key = node.get_id()
            if key in memo:
                continue
            if key in leaves:
                memo[key] = (node, leaves[key][1] == 1)
                continue
            if not z3.is_app(node):
                memo[key] = (node, node)
                continue
            children = node.children()
            if node.decl().kind() == z3.Z3_OP_ITE:
                condition, yes, no = children
                selected = leaves.get(condition.get_id())
                if (selected is not None
                        and (z3.is_int_value(yes) or z3.is_rational_value(yes))
                        and (z3.is_int_value(no) or z3.is_rational_value(no))):
                    # The exact affine interpolation is valid because the
                    # observable's 0/1 domain is explicitly retained below.
                    real = yes.sort().kind() == z3.Z3_REAL_SORT
                    yes_value = yes.as_fraction() if real else yes.as_long()
                    low = no.as_fraction() if real else no.as_long()
                    delta = yes_value - low
                    alias = selected[1]
                    number = z3.RealVal if real else z3.IntVal
                    replacement = number(str(low), ctx=body.ctx)
                    if delta:
                        coordinate = z3.ToReal(alias) if real else alias
                        contribution = coordinate if delta == 1 else number(str(delta), ctx=body.ctx) * coordinate
                        replacement = contribution if low == 0 else replacement + contribution
                    memo[key] = (node, replacement)
                    weighted += 1
                    continue
            if not ready and children:
                pending.append((node, True))
                pending.extend((child, False) for child in children)
                continue
            rebuilt = [memo[child.get_id()][1] for child in children]
            replacement = node
            if any(not a.eq(b) for a, b in zip(children, rebuilt)):
                args = (z3.Ast * len(rebuilt))(*[child.as_ast() for child in rebuilt])
                replacement = z3.z3._to_expr_ref(z3.Z3_update_term(
                    node.ctx_ref(), node.as_ast(), len(rebuilt), args), node.ctx)
            # Holding both original and replacement prevents stale AST IDs.
            memo[key] = (node, replacement)
        aliases = {alias.get_id(): alias for _, alias in leaves.values()}
        domain = [bound for alias in aliases.values() for bound in (alias >= 0, alias <= 1)]
        result = z3.And(memo[body.get_id()][1], *domain)
        rewritten_bridges = tuple((alias, memo[term.get_id()][1]) for alias, term in bridges)
        return result, rewritten_bridges, len(leaves), weighted

    candidate, rewritten_bridges, count, weighted = rewrite(groups)
    remaining = {constant.get_id() for constant in free_constants([candidate])}
    rejected = {key: group for key, group in groups.items() if key in remaining}
    accepted = {key: group for key, group in groups.items() if key not in remaining}
    if rejected:
        if not accepted:
            return BooleanObservationProjection(body, bridges, (),
                tuple(str(group['root'].decl().name()) for group in rejected.values()), 0, 0)
        # Roll back the WHOLE escaping root, not only its unobserved reads.
        candidate, rewritten_bridges, count, weighted = rewrite(accepted)
    return BooleanObservationProjection(candidate, rewritten_bridges,
        tuple(str(group['root'].decl().name()) for group in accepted.values()),
        tuple(str(group['root'].decl().name()) for group in rejected.values()), count, weighted)
