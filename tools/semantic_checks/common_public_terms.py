"""A sufficient equivalence proof by abstracting shared public arithmetic terms.

Replacing the same ground term in both relations with the same fresh constant
can introduce additional assignments. UNSAT of the resulting XOR therefore
proves the original equivalence. SAT or UNKNOWN is not an original result and
must fall back to the complete original formulas.
"""
from dataclasses import dataclass

import z3


@dataclass(frozen=True)
class CommonPublicTermAbstraction:
    left: object
    right: object
    substitutions: tuple


def abstract_common_public_products(left, right, public_variables):
    """Abstract identical nonlinear products containing only public coordinates.

    Bound variables, private constants and uninterpreted function applications
    disqualify a term. All relation structure and all conjuncts are retained.
    Each returned substitution can be reversed to recover the input exactly.
    """
    if not z3.is_bool(left) or not z3.is_bool(right) or left.ctx != right.ctx:
        raise ValueError('relations must be Boolean in the same context')
    public = tuple(public_variables)
    if any(not z3.is_const(v) or v.decl().kind() != z3.Z3_OP_UNINTERPRETED
           or v.ctx != left.ctx for v in public):
        raise ValueError('public coordinates must be constants in the relation context')
    allowed = {v.get_id() for v in public}
    if len(allowed) != len(public):
        raise ValueError('duplicate public coordinate')

    def public_only(term):
        pending, seen = [term], set()
        while pending:
            node = pending.pop()
            if node.get_id() in seen:
                continue
            seen.add(node.get_id())
            if not z3.is_app(node):
                return False
            if node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                if not z3.is_const(node) or node.get_id() not in allowed:
                    return False
            pending.extend(node.children())
        return True

    def products(root):
        found, seen, pending = {}, set(), [root]
        while pending:
            node = pending.pop()
            if node.get_id() in seen:
                continue
            seen.add(node.get_id())
            if z3.is_quantifier(node):
                pending.append(node.body())
            elif z3.is_app(node):
                if node.decl().kind() == z3.Z3_OP_MUL:
                    values = [z3.simplify(v) for v in node.children()]
                    nonliteral = sum(not (z3.is_int_value(v) or z3.is_rational_value(v))
                                     for v in values)
                    if nonliteral > 1 and public_only(node):
                        found[node.get_id()] = node
                pending.extend(reversed(node.children()))
        return found

    source, target = products(left), products(right)
    # Use maximal shared terms so reverse substitution is syntactically exact
    # even when products are nested. Nested terms are already covered by the
    # outer public expression and need no separate abstraction coordinate.
    common = {key:term for key,term in source.items() if key in target}
    nested = set()
    for term in common.values():
        pending, seen = list(term.children()), set()
        while pending:
            node = pending.pop()
            if node.get_id() in seen:
                continue
            seen.add(node.get_id())
            if node.get_id() in common:
                nested.add(node.get_id())
            if z3.is_app(node):
                pending.extend(node.children())
            elif z3.is_quantifier(node):
                pending.append(node.body())
    pairs = tuple((term, z3.FreshConst(term.sort(), 'shared_public_product'))
                  for key,term in common.items() if key not in nested)
    if not pairs:
        return CommonPublicTermAbstraction(left, right, ())
    return CommonPublicTermAbstraction(z3.substitute(left, *pairs),
                                      z3.substitute(right, *pairs), pairs)
