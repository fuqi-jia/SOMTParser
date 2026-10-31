"""Remove bounds proved by integer expressions and retained definitions.

Finite ranges are inferred from literals, both ITE branches, arithmetic and
unconditional top-level equalities. No asserted inequality is used as an
assumption, so a bound can never justify its own removal. Definitions and all
unproved constraints stay in the complete formula. No solver query is made.
"""
from dataclasses import dataclass
import z3


@dataclass(frozen=True)
class ExpressionIntervalNormalization:
    formula: object
    removed_bounds: int
    inferred_coordinates: int
    retained_definitions: int
    visited_nodes: int


def _conjuncts(root):
    pending, clauses, seen = [root], [], set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_and(node):
            pending.extend(reversed(node.children()))
        else:
            clauses.append(node)
    return clauses


def _literal(node):
    if z3.is_int_value(node):
        return node.as_long()
    if z3.is_app_of(node, z3.Z3_OP_UMINUS) and z3.is_int_value(node.arg(0)):
        return -node.arg(0).as_long()
    return None


def _linear_terms(root):
    """Flatten integer linear combinations, leaving nonlinear terms opaque."""
    plans, order, pending = {}, [], [(root, False)]
    while pending:
        node, ready = pending.pop()
        key = node.get_id()
        if key in plans:
            continue
        value = _literal(node)
        kind = node.decl().kind() if z3.is_app(node) else None
        edges, constant = None, 0
        if value is not None:
            edges, constant = [], value
        elif kind == z3.Z3_OP_ADD:
            edges = [(child, 1) for child in node.children()]
        elif kind == z3.Z3_OP_SUB:
            edges = [(child, 1 if i == 0 else -1) for i, child in enumerate(node.children())]
        elif kind == z3.Z3_OP_UMINUS:
            edges = [(node.arg(0), -1)]
        elif kind == z3.Z3_OP_MUL:
            opaque, factor = [], 1
            for child in node.children():
                value = _literal(child)
                if value is None:
                    opaque.append(child)
                else:
                    factor *= value
            if len(opaque) == 1:
                edges = [(opaque[0], factor)]
            elif not opaque:
                edges, constant = [], factor
        if edges and not ready:
            pending.append((node, True))
            pending.extend((child, False) for child, _ in edges)
            continue
        plans[key] = (node, edges, constant)
        order.append(key)
    # Parent weights are combined before visiting a shared child. Expanding
    # paths independently would be exponential for repeated sums such as t+t.
    weights, terms, offset = {root.get_id(): 1}, [], 0
    for key in reversed(order):
        node, edges, constant = plans[key]
        scale = weights.get(key, 0)
        if not scale:
            continue
        if edges is None:
            terms.append((node, scale))
        else:
            offset += scale * constant
            for child, coefficient in edges:
                identity = child.get_id()
                weights[identity] = weights.get(identity, 0) + scale * coefficient
    return terms, offset


def remove_entailed_expression_bounds(formula, audit_callback=None):
    """Return an equivalent conjunction with independently proved bounds removed.

    Inference over coordinate definitions is monotone: only the first finite
    range is retained, and each depends on previously inferred ranges. Cyclic
    or unsupported definitions simply remain unresolved. ITE conditions are
    arbitrary; taking the union of both branch ranges is always sound.
    """
    if not z3.is_bool(formula):
        raise ValueError('expression bound normalization requires a Boolean formula')
    clauses = _conjuncts(formula)
    definitions = []
    for index, clause in enumerate(clauses):
        if not z3.is_eq(clause) or not all(z3.is_int(a) for a in clause.children()):
            continue
        equation = _linear_terms(clause.arg(0) - clause.arg(1))
        if equation is None:
            continue
        terms, offset = equation
        for coordinate, coefficient in terms:
            if (abs(coefficient) != 1 or not z3.is_const(coordinate)
                    or coordinate.decl().kind() != z3.Z3_OP_UNINTERPRETED):
                continue
            rest = [scale * node for node, scale in terms if not node.eq(coordinate)]
            rhs = -coefficient * z3.Sum(z3.IntVal(offset, ctx=formula.ctx), *rest)
            definitions.append((coordinate, rhs, index))

    known, memo, seen, used_definitions = {}, {}, set(), []
    arithmetic = {z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL}

    def interval(root):
        pending = [(root, False)]
        while pending:
            node, ready = pending.pop()
            key = node.get_id()
            if key in memo:
                continue
            seen.add(key)
            value = _literal(node)
            if value is not None:
                memo[key] = (value, value)
                continue
            if key in known:
                memo[key] = known[key]
                continue
            if not z3.is_int(node) or not z3.is_app(node):
                memo[key] = None
                continue
            kind = node.decl().kind()
            if kind == z3.Z3_OP_MOD and _literal(node.arg(1)) is not None:
                divisor = _literal(node.arg(1))
                memo[key] = (0, divisor - 1) if divisor > 0 else None
                continue
            children = (list(node.children())[1:] if kind == z3.Z3_OP_ITE
                        else list(node.children()))
            if kind not in arithmetic | {z3.Z3_OP_ITE, z3.Z3_OP_IDIV}:
                memo[key] = None
                continue
            if not ready:
                pending.append((node, True))
                pending.extend((child, False) for child in children)
                continue
            ranges = [memo[child.get_id()] for child in children]
            if any(pair is None for pair in ranges):
                memo[key] = None
                continue
            if kind == z3.Z3_OP_ITE:
                answer = (min(p[0] for p in ranges), max(p[1] for p in ranges))
            elif kind == z3.Z3_OP_ADD:
                answer = (sum(p[0] for p in ranges), sum(p[1] for p in ranges))
            elif kind == z3.Z3_OP_SUB:
                answer = (ranges[0][0] - sum(p[1] for p in ranges[1:]),
                          ranges[0][1] - sum(p[0] for p in ranges[1:]))
            elif kind == z3.Z3_OP_UMINUS:
                answer = (-ranges[0][1], -ranges[0][0])
            elif kind == z3.Z3_OP_MUL:
                answer = (1, 1)
                for low, high in ranges:
                    endpoints = [a * b for a in answer for b in (low, high)]
                    answer = (min(endpoints), max(endpoints))
            else:
                low, high = ranges[1]
                answer = ((ranges[0][0] // low, ranges[0][1] // low)
                          if low == high and low > 0 else None)
            memo[key] = answer
        return memo[root.get_id()]

    unresolved = list(definitions)
    while unresolved:
        changed, next_pass = False, []
        for coordinate, rhs, index in unresolved:
            if coordinate.get_id() in known:
                continue
            result = interval(rhs)
            if result is None:
                next_pass.append((coordinate, rhs, index))
            else:
                known[coordinate.get_id()] = result
                used_definitions.append(index)
                changed = True
        if not changed:
            break
        # Only failed queries may change as more retained definitions resolve.
        memo = {key: value for key, value in memo.items() if value is not None}
        unresolved = next_pass

    memo = {key: value for key, value in memo.items() if value is not None}
    kept, removed = [], 0
    inverse = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_LT: z3.Z3_OP_GE,
               z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_GT: z3.Z3_OP_LE}
    for index, clause in enumerate(clauses):
        atom = clause.arg(0) if z3.is_not(clause) else clause
        kind = atom.decl().kind() if z3.is_app(atom) else None
        if (kind not in inverse or atom.num_args() != 2
                or not all(z3.is_int(a) for a in atom.children())):
            kept.append(clause)
            continue
        if z3.is_not(clause):
            kind = inverse[kind]
        left, right = interval(atom.arg(0)), interval(atom.arg(1))
        proven = False
        if left is not None and right is not None:
            proven = {z3.Z3_OP_LE: left[1] <= right[0],
                      z3.Z3_OP_LT: left[1] < right[0],
                      z3.Z3_OP_GE: left[0] >= right[1],
                      z3.Z3_OP_GT: left[0] > right[1]}[kind]
        if not proven:
            kept.append(clause)
            continue
        removed += 1
        if audit_callback is not None:
            audit_callback(dict(bound_index=index, left_interval=left, right_interval=right,
                                asserted_inequalities_used=0, all_definitions_retained=True,
                                retained_definition_indices=sorted(set(used_definitions))))
    result = z3.And(*kept) if kept else z3.BoolVal(True, ctx=formula.ctx)
    return ExpressionIntervalNormalization(result, removed, len(known),
                                           len({index for _, _, index in definitions}), len(seen))
