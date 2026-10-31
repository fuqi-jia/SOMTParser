"""Exact extraction of common integer affine terms from ITE branches.

If(c, S+A, S+B) = S+If(c, A, B), with the complete multiplicity and
integer coefficient of every opaque term preserved. No domain, solver model
or equality from another formula is assumed. Quantifier bodies are not
traversed by this pass; the final Z3 simplifier is semantics preserving.
"""
from dataclasses import dataclass
import z3

from .expression_interval_bounds import _linear_terms


@dataclass(frozen=True)
class IteAffineFactoring:
    formula: object
    rewritten_ites: int
    extracted_terms: int
    visited_nodes: int


def factor_ite_common_affine_terms(formula):
    """Factor identical integer terms and coefficients, without a solver query.

    Nonlinear and unsupported terms are opaque atoms. A shared atom is moved
    only when its full coefficient is identical in both branches. Distinct
    atoms, nonmatching coefficients and all branch-specific constants remain.
    Both the traversal and affine collection preserve DAG sharing.
    """
    memo, affine_cache = {}, {}
    rewritten = extracted = 0

    def affine(root):
        identity = root.get_id()
        if identity not in affine_cache:
            terms, offset = _linear_terms(root)
            # Keep the expression alive as long as its ID is a cache key.
            affine_cache[identity] = (root, {n.get_id(): (n, c) for n, c in terms}, offset)
        return affine_cache[identity][1:]

    def expression(terms, offset):
        args = [coefficient * node for node, coefficient in terms]
        if offset or not args:
            args.append(z3.IntVal(offset, ctx=formula.ctx))
        return args[0] if len(args) == 1 else z3.Sum(*args)

    pending = [(formula, False)]
    while pending:
        node, ready = pending.pop()
        key = node.get_id()
        if key in memo:
            continue
        if not z3.is_app(node):
            memo[key] = node
            continue
        children = list(node.children())
        if children and not ready:
            pending.append((node, True))
            pending.extend((child, False) for child in children)
            continue
        args = [memo[child.get_id()] for child in children]
        current = (node if all(a.eq(b) for a, b in zip(children, args))
                   else node.decl()(*args))
        if z3.is_app_of(current, z3.Z3_OP_ITE) and z3.is_int(current):
            left, left_offset = affine(current.arg(1))
            right, right_offset = affine(current.arg(2))
            shared = {identity for identity in left.keys() & right.keys()
                      if left[identity][1] == right[identity][1]}
            constant = left_offset if left_offset == right_offset else 0
            if shared or constant:
                common = expression([left[i] for i in sorted(shared)], constant)
                a = expression([term for i, term in left.items() if i not in shared],
                               left_offset - constant)
                b = expression([term for i, term in right.items() if i not in shared],
                               right_offset - constant)
                current = common + z3.If(current.arg(0), a, b)
                rewritten += 1
                extracted += len(shared) + int(constant != 0)
        memo[key] = current
    return IteAffineFactoring(z3.simplify(memo[formula.get_id()]),
                             rewritten, extracted, len(memo))
