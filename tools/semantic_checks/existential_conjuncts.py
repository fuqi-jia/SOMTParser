"""Expose independent conjuncts of a top-level existential relation exactly.

For inhabited SMT sorts, ``Exists(v, C & B(v)) == C & Exists(v, B(v))``
when C does not contain v free. This is not quantifier elimination: every
dependent conjunct, variable sort and bound remains in the residual relation.
The transformation only visits conjunctions at the root, never connective
contexts such as negation/disjunction or the interior of another quantifier.
"""
from dataclasses import dataclass
import time


@dataclass(frozen=True)
class Factoring:
    formula: object
    lifted_conjuncts: int = 0
    rewritten_quantifiers: int = 0
    deadline_exhausted: bool = False


class _Expired(Exception):
    pass


def factor_existential_conjuncts(formula, *, deadline=None):
    """Factor free conjuncts, alpha-renaming bound variables capture-safely.

    ``deadline`` is the caller's existing monotonic deadline, or None. Any
    interrupted traversal rolls back the whole rewrite. Quantifiers with
    patterns/no-patterns are conservatively retained rather than rebuilding
    their solver annotations. A local DAG cache avoids rescanning common terms.
    """
    import z3

    if not z3.is_bool(formula):
        raise TypeError("expected a Boolean relation")

    def check_time():
        if deadline is not None and time.monotonic() >= deadline:
            raise _Expired()

    def flatten(root):
        stack, result = [root], []
        while stack:
            check_time()
            expr = stack.pop()
            if z3.is_and(expr):
                stack.extend(reversed(expr.children()))
            else:
                result.append(expr)
        return result

    lifted = rewritten = 0
    output = []
    try:
        for term in flatten(formula):
            if (not z3.is_quantifier(term) or not term.is_exists()
                    or term.num_patterns() or term.num_no_patterns()):
                output.append(term)
                continue
            # Opening with FreshConst, followed by the same constants' binding,
            # preserves nested de Bruijn references and same-spelled free names.
            variables = [z3.FreshConst(term.var_sort(i), "factor_exists")
                         for i in range(term.num_vars())]
            hidden_ids = {var.get_id() for var in variables}
            opened = z3.substitute_vars(term.body(), *reversed(variables))
            memo = {}

            def depends(root):
                stack = [(root, False)]
                while stack:
                    check_time()
                    expr, done = stack.pop()
                    key = expr.get_id()
                    if key in memo:
                        continue
                    if key in hidden_ids:
                        memo[key] = True
                        continue
                    children = ([expr.body()] if z3.is_quantifier(expr)
                                else expr.children() if z3.is_app(expr) else [])
                    if done:
                        memo[key] = any(memo[child.get_id()] for child in children)
                    else:
                        stack.append((expr, True))
                        stack.extend((child, False) for child in children
                                     if child.get_id() not in memo)
                return memo[root.get_id()]

            independent, dependent = [], []
            for conjunct in flatten(opened):
                (dependent if depends(conjunct) else independent).append(conjunct)
            if not independent:
                output.append(term)
                continue
            output.extend(independent)
            if dependent:
                body = dependent[0] if len(dependent) == 1 else z3.And(*dependent)
                output.append(z3.Exists(variables, body))
            lifted += len(independent)
            rewritten += 1
        if not rewritten:
            return Factoring(formula)
        result = output[0] if len(output) == 1 else z3.And(*output)
        return Factoring(result, lifted, rewritten)
    except _Expired:
        return Factoring(formula, deadline_exhausted=True)
