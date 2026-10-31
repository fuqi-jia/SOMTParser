"""Exact elimination of one Int universal over finitely many step predicates.

Every use of the bound integer must occur in an order/equality comparison with
a binder-free Int threshold. For each assignment of the free symbols, these
atoms change only at finitely many integer events. Their values before every
event, and at every event, cover the entire integer line. No domain bound or
candidate assignment is needed. Unsupported binders are retained unchanged.
"""
from dataclasses import dataclass
import z3


@dataclass
class StepExpansion:
    formula: z3.BoolRef
    expanded_quantifiers: int = 0
    retained_quantifiers: int = 0
    event_instances: int = 0


def _one_quantifier(node):
    if (not node.is_forall() or node.num_vars() != 1
            or node.var_sort(0).kind() != z3.Z3_INT_SORT):
        return None
    body = node.body()
    # One iterative DAG classification, scoped to this live body's context.
    free, pending = {}, [(body, False)]
    while pending:
        term, ready = pending.pop()
        key = term.get_id()
        if key in free:
            continue
        if z3.is_quantifier(term):
            return None
        if z3.is_var(term):
            if z3.get_var_index(term) != 0 or not z3.is_int(term):
                return None
            free[key] = False
        elif z3.is_app(term):
            children = term.children()
            if ready:
                free[key] = all(free[child.get_id()] for child in children)
            else:
                pending.append((term, True))
                pending.extend((child, False) for child in children
                               if child.get_id() not in free)
        else:
            return None

    events, atoms, todo, seen = {}, [], [body], set()
    reverse = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_GE: z3.Z3_OP_LE,
               z3.Z3_OP_LT: z3.Z3_OP_GT, z3.Z3_OP_GT: z3.Z3_OP_LT,
               z3.Z3_OP_EQ: z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT: z3.Z3_OP_DISTINCT}
    while todo:
        term = todo.pop()
        key = term.get_id()
        if key in seen or free[key]:
            continue
        seen.add(key)
        if z3.is_var(term):
            return None  # Naked time, arithmetic in time, array index, etc.
        kind = term.decl().kind()
        if kind in reverse and term.num_args() == 2:
            a, b = term.children()
            if z3.is_var(b):
                a, b, kind = b, a, reverse[kind]
            if z3.is_var(a) and free[b.get_id()] and z3.is_int(b):
                offsets = ((0, 1) if kind in (z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT)
                           else (1,) if kind in (z3.Z3_OP_LE, z3.Z3_OP_GT)
                           else (0,))
                for offset in offsets:
                    event = b if offset == 0 else b + 1
                    events[event.get_id()] = event
                before = kind in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_DISTINCT)
                atoms.append((term, z3.BoolVal(before, ctx=body.ctx)))
                continue
        todo.extend(term.children())
    if not atoms:
        return body, 0
    # For any valuation, some integer precedes all finitely many thresholds.
    # Substitution gives its exact truth vector, including all free conditions.
    baseline = z3.substitute(body, *atoms)
    instances = [z3.substitute_vars(body, event) for event in events.values()]
    return z3.And(baseline, *instances), len(instances)


def expand_integer_step_universals(expression):
    """Expand supported conjunction-local ForAlls, preserving all other terms.

    The result is equivalent for every assignment of all free coordinates,
    including objective coordinates. No solver is called. Exists, real time,
    nested binders and non-step uses of the bound variable remain unchanged.
    """
    if not z3.is_bool(expression):
        raise ValueError('step expansion requires a Boolean formula')
    out, todo = [], [expression]
    result = StepExpansion(expression)
    while todo:
        node = todo.pop()
        if z3.is_and(node):
            todo.extend(reversed(node.children()))
        elif z3.is_quantifier(node):
            expanded = _one_quantifier(node)
            if expanded is None:
                result.retained_quantifiers += 1
                out.append(node)
            else:
                formula, count = expanded
                result.expanded_quantifiers += 1
                result.event_instances += count
                out.append(formula)
        else:
            out.append(node)
    if result.expanded_quantifiers:
        result.formula = z3.And(*out) if out else z3.BoolVal(True, ctx=expression.ctx)
    return result
