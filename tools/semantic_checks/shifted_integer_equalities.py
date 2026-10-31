"""Canonicalize shifted equalities without projecting any coordinate.

Only affine integer equalities with two free coordinates and coefficients
+1 and -1 qualify. Every replacement is an algebraic identity, including
inside negations, disjunctions, and binders; no contextual domain is assumed.
The AST identity order is shared by both relations in the comparison context.
"""
from dataclasses import dataclass

import z3


@dataclass(frozen=True)
class ShiftedIntegerEqualityNormalization:
    formula: object
    eligible_equalities: int = 0


def _affine(root, cache):
    """Return (constant, {AST identity: (coordinate, coefficient)}), or None."""
    pending = [(root, False)]
    while pending:
        node, expanded = pending.pop()
        identity = node.get_id()
        if identity in cache:
            continue
        if not z3.is_app(node) or node.sort().kind() != z3.Z3_INT_SORT:
            cache[identity] = None
            continue
        if z3.is_int_value(node):
            cache[identity] = (node.as_long(), {})
            continue
        if z3.is_const(node) and node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            cache[identity] = (0, {identity: (node, 1)})
            continue
        kind = node.decl().kind()
        if kind not in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL):
            cache[identity] = None
            continue
        children = node.children()
        if not expanded:
            pending.append((node, True))
            pending.extend((child, False) for child in children)
            continue
        pieces = [cache[child.get_id()] for child in children]
        if any(piece is None for piece in pieces):
            cache[identity] = None
            continue
        weights = [1] * len(pieces)
        if kind == z3.Z3_OP_MUL:
            nonconstant = [i for i, (_, terms) in enumerate(pieces) if terms]
            if len(nonconstant) > 1:
                cache[identity] = None
                continue
            factor = 1
            for constant, terms in pieces:
                if not terms:
                    factor *= constant
            if not nonconstant:
                cache[identity] = (factor, {})
                continue
            pieces = [pieces[nonconstant[0]]]
            weights = [factor]
        elif kind == z3.Z3_OP_SUB:
            weights = [1] + [-1] * (len(pieces) - 1)
        elif kind == z3.Z3_OP_UMINUS:
            weights = [-1]
        constant, terms = 0, {}
        for weight, (offset, child_terms) in zip(weights, pieces):
            constant += weight * offset
            for key, (coordinate, coefficient) in child_terms.items():
                terms[key] = (coordinate, terms.get(key, (None, 0))[1] + weight * coefficient)
        cache[identity] = (constant, {key: value for key, value in terms.items() if value[1]})
    return cache[root.get_id()]


def normalize_shifted_integer_equalities(formula):
    pending, seen, replacements, cache = [formula], set(), [], {}
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_quantifier(node):
            pending.append(node.body())
            continue
        if not z3.is_app(node):
            continue
        pending.extend(node.children())
        if not z3.is_eq(node) or any(arg.sort().kind() != z3.Z3_INT_SORT for arg in node.children()):
            continue
        left, right = (_affine(arg, cache) for arg in node.children())
        if left is None or right is None:
            continue
        terms = dict(left[1])
        for key, (coordinate, coefficient) in right[1].items():
            terms[key] = (coordinate, terms.get(key, (None, 0))[1] - coefficient)
        terms = {key: value for key, value in terms.items() if value[1]}
        if len(terms) != 2:
            continue
        first, second = [terms[key] for key in sorted(terms)]
        if sorted([first[1], second[1]]) != [-1, 1]:
            continue
        # Multiplication by first's sign orients both syntactic forms equally.
        offset = (right[0] - left[0]) * first[1]
        replacements.append((node, first[0] - second[0] == z3.IntVal(offset, ctx=formula.ctx)))
    rewritten = z3.substitute(formula, *replacements) if replacements else formula
    return ShiftedIntegerEqualityNormalization(rewritten, len(replacements))
