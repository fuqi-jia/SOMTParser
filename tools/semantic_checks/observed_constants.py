"""Eliminate private scalars through unconditional public equality bridges."""
from dataclasses import dataclass

import z3


@dataclass(frozen=True)
class ObservedConstantProjection:
    body: object
    private_variables: tuple
    substitutions: tuple


def project_observed_constants(body, private_variables, public_variables):
    """Preserve the full existential relation while preferring public names.

    Only an equality that is an unconditional conjunct can define a private
    constant as a public constant. All conjuncts stay in the rewritten body,
    including equalities for additional aliases of the same private value.
    This prevents subsequent quantifier elimination from inlining a public
    quantity's implementation into unrelated constraints or objective terms.
    """
    if not z3.is_bool(body):
        raise ValueError('projection body must be Boolean')
    private_variables = tuple(private_variables)
    public_variables = tuple(public_variables)
    for variables in (private_variables, public_variables):
        if any(not z3.is_const(v) or v.decl().kind() != z3.Z3_OP_UNINTERPRETED
               or v.ctx != body.ctx for v in variables):
            raise ValueError('projection coordinates must be constants in the body context')
        if len({v.get_id() for v in variables}) != len(variables):
            raise ValueError('duplicate projection coordinate')
    private = {v.get_id(): v for v in private_variables}
    public = {v.get_id(): v for v in public_variables}
    if private.keys() & public.keys():
        raise ValueError('private and public coordinates overlap')

    replacements = {}
    stack = [body]
    while stack:
        expression = stack.pop()
        if z3.is_and(expression):
            stack.extend(reversed(expression.children()))
        elif z3.is_eq(expression):
            left, right = expression.children()
            if left.get_id() in public and right.get_id() in private:
                left, right = right, left
            if (left.get_id() in private and right.get_id() in public
                    and left.sort().kind() != z3.Z3_ARRAY_SORT):
                replacements.setdefault(left.get_id(), (left, right))
    pairs = tuple(replacements.values())
    rewritten = z3.substitute(body, *pairs) if pairs else body
    remaining = tuple(v for v in private_variables if v.get_id() not in replacements)
    return ObservedConstantProjection(rewritten, remaining, pairs)
