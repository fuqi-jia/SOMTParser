"""Sufficient UNSAT proof from a subset of complete target conjuncts.

Only equivalence-preserving conjunction decomposition is used; there are no
new assumptions. SAT of the subset is inconclusive.
The caller must parse and bind the complete original command stream first.
"""
import hashlib

import z3


def derive_conjuncts(assertions):
    """Split positive AND and NOT(OR) only; retain an origin for every leaf.

    The conjunction of ALL returned terms equals the complete original relation.
    No disjunct, negated conjunct or implication branch is promoted to a fact.
    """
    entries = []
    for index, assertion in enumerate(assertions):
        pending = [(assertion, [])]
        while pending:
            term, path = pending.pop()
            if z3.is_and(term):
                pending.extend((term.arg(i), path + [['and', i]])
                               for i in reversed(range(term.num_args())))
            elif z3.is_not(term) and z3.is_or(term.arg(0)):
                disjunction = term.arg(0)
                pending.extend((z3.Not(disjunction.arg(i)), path + [['not-or', i]])
                               for i in reversed(range(disjunction.num_args())))
            else:
                entries.append((index, path, term))
    return entries


def replay_conjunct(assertions, origin, path):
    """Validate an extraction address without trusting a supplied formula."""
    if type(origin) is not int or not 0 <= origin < len(assertions):
        raise ValueError('invalid original assertion index')
    term = assertions[origin]
    for rule, index in path:
        if type(index) is not int or index < 0:
            raise ValueError('invalid conjunct address')
        if rule == 'and' and z3.is_and(term) and index < term.num_args():
            term = term.arg(index)
        elif (rule == 'not-or' and z3.is_not(term) and z3.is_or(term.arg(0))
              and index < term.arg(0).num_args()):
            term = z3.Not(term.arg(0).arg(index))
        else:
            raise ValueError('path does not follow an unconditional conjunction rule')
    return term


def select_coordinates(assertions, names):
    """A heuristic only: return entire assertions using these named constants."""
    assertions = list(assertions)
    allowed = set(names)
    # A context owns its AST IDs. Keep all input roots alive for the whole
    # traversal and distinguish IDs from different contexts explicitly.
    memo = {}
    selected = []
    for index, assertion in enumerate(assertions):
        context = assertion.ctx
        pending = [(assertion, None)]
        while pending:
            node, children = pending.pop()
            key = (context, node.get_id())
            if key in memo:
                continue
            if children is None:
                if z3.is_quantifier(node) or not z3.is_app(node):
                    memo[key] = False
                elif node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                    memo[key] = node.num_args() == 0 and str(node.decl().name()) in allowed
                else:
                    children = node.children()
                    pending.append((node, children))
                    pending.extend((child, None) for child in children
                                   if (context, child.get_id()) not in memo)
            else:
                memo[key] = all(memo[(context, child.get_id())] for child in children)
        if memo[(context, assertion.get_id())]:
            selected.append(index)
    return selected


def prove(assertions, indices):
    """Return the exact subset and its solver; only UNSAT proves the full set."""
    assertions, indices = list(assertions), list(indices)
    if any(not z3.is_bool(term) for term in assertions):
        raise ValueError('complete assertions must be Boolean')
    if (not indices or any(type(i) is not int or i < 0 or i >= len(assertions) for i in indices)
            or len(set(indices)) != len(indices)):
        raise ValueError('subset needs unique valid assertion indices')
    selected = [assertions[i] for i in indices]
    solver = z3.Solver(ctx=selected[0].ctx)
    solver.add(*selected)
    answer = solver.check()
    receipt = dict(
        status=str(answer), full_target_unsat=answer == z3.unsat,
        full_assertion_count=len(assertions), selected_assertion_count=len(selected),
        indices=indices, no_assertion_rewritten=True, no_new_assumptions=True,
        monotonicity_rule='an UNSAT subset implies UNSAT of every superset',
        selected_sexpr_sha256=[hashlib.sha256(term.sexpr().encode()).hexdigest()
                               for term in selected],
    )
    if answer == z3.unknown:
        receipt['reason_unknown'] = solver.reason_unknown()
    return receipt, solver
