"""Sufficient full-formula certificate using a candidate witness bijection.

Conjunct-local existential binders can be moved to a common outer block after
capture-safe freshening. If the two complete opened bodies are equivalent for
all values of the shared witness tuple, their existential closures are equal.
Binder order is only a candidate correspondence; names are never evidence.
A poor candidate can fail even for equivalent formulas and stays inconclusive.
"""
import z3
from .qf_conjuncts import prove_qf_conjunctions


def _opened_conjunction(root):
    witnesses, terms, todo = [], [], [root]
    while todo:
        node = todo.pop()
        if z3.is_and(node):
            todo.extend(reversed(node.children()))
        elif z3.is_quantifier(node) and node.is_exists():
            values = [z3.FreshConst(node.var_sort(i), prefix='exists_bijection')
                      for i in range(node.num_vars())]
            witnesses.extend(values)
            todo.append(z3.substitute_vars(node.body(), *reversed(values)))
        else:
            # Binders inside OR/NOT or a universal block are not moved. The
            # downstream QF checker explicitly rejects these remaining nodes.
            terms.append(node)
    return z3.And(*terms) if terms else z3.BoolVal(True, ctx=root.ctx), witnesses


def prove_existential_bijection(left, right, *, body_checker=None):
    """Prove a sufficient full body correspondence; do not guess public maps.

    Both complete formulas, including any ordered cost observations, must be
    supplied by the caller. No original conjunct, domain or objective is
    removed. Every moved witness is fresh, of its original sort, and remains
    existential in the mathematical conclusion. SMT sorts are inhabited.
    An optional body checker must prove equivalence of the complete opened
    bodies; only an explicit equivalent=True certificate is accepted.
    """
    if left.ctx != right.ctx:
        raise ValueError('existential comparison needs one Z3 context')
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('existential comparison requires Boolean formulas')
    result = dict(equivalent=None, solver_queries=0,
                  method='complete opened conjunction under candidate existential bijection',
                  all_original_conjuncts_retained=True)
    lb, lw = _opened_conjunction(left)
    rb, rw = _opened_conjunction(right)
    result.update(left_witnesses=len(lw), right_witnesses=len(rw))
    if len(lw) != len(rw) or any(not a.sort().eq(b.sort()) for a, b in zip(lw, rw)):
        return dict(result, reason='candidate witness arity or sorts differ')
    if rw:
        rb = z3.substitute(rb, *zip(rw, lw))
    checker = prove_qf_conjunctions if body_checker is None else body_checker
    proof = checker(lb, rb)
    result.update(body_certificate=proof, solver_queries=proof['solver_queries'])
    if proof['equivalent'] is True:
        return dict(result, equivalent=True,
                    reason='complete bodies equivalent for every shared witness value')
    return dict(result, reason='candidate body correspondence inconclusive')
