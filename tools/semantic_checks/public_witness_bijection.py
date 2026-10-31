"""Propose a typed witness bijection, then prove both complete bodies equal.

Shared public declarations in each conjunct select candidate correspondences.
They never establish equivalence by themselves. All positive existential
witnesses are mapped bijectively and the supplied checker sees every original
constraint and ordered cost. Other quantifier contexts remain unsupported.
"""
from collections import defaultdict

import z3

from .existential_bijection import _opened_conjunction
from .qf_conjuncts import _conjuncts, _signatures


def prove_public_witness_bijection(left, right, *, body_checker):
    if left.ctx != right.ctx or not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('witness comparison requires Boolean formulas in one context')
    result = dict(equivalent=None, solver_queries=0,
                  method='candidate typed witness bijection by shared public incidence',
                  all_original_conjuncts_retained=True)
    a, av = _opened_conjunction(left)
    b, bv = _opened_conjunction(right)
    if len(av) != len(bv) or not av:
        return dict(result, reason='no matching nonempty witness tuples')

    def groups(body, witnesses):
        clauses = _conjuncts(body)
        signatures = _signatures(clauses)
        if signatures is None:
            return None
        ids = {w.decl().get_id() for w in witnesses}
        neighbors = {identity: set() for identity in ids}
        for signature in signatures.values():
            for identity in signature & ids:
                neighbors[identity].update(signature - ids)
        buckets = defaultdict(list)
        for witness in witnesses:
            key = (witness.sort().get_id(), tuple(sorted(neighbors[witness.decl().get_id()])))
            buckets[key].append(witness)
        return buckets

    ag, bg = groups(a, av), groups(b, bv)
    if ag is None or bg is None:
        return dict(result, reason='remaining binder prevents QF incidence matching')
    if ag.keys() != bg.keys() or any(len(ag[k]) != len(bg[k]) for k in ag):
        return dict(result, reason='candidate typed public-incidence groups differ')
    pairs = [(r, l) for key in ag for r, l in zip(bg[key], ag[key])]
    # Buckets partition every fresh witness, so this substitution is a typed
    # bijection. Free source observations are never renamed or projected here.
    b = z3.substitute(b, *pairs)
    proof = body_checker(a, b)
    result.update(body_certificate=proof, solver_queries=proof['solver_queries'],
                  witness_count=len(pairs), candidate_groups=len(ag),
                  correspondence=[dict(left=str(l), right=str(r), sort=str(l.sort()))
                                  for r, l in pairs])
    if proof['equivalent'] is True:
        result.update(equivalent=True, reason='complete bodies equivalent for every mapped witness value')
    else:
        result['reason'] = 'candidate matching inconclusive'
    return result
