"""Existential cyclic-order witness for the XCSP successor-cycle relation.

This optional source-side formula is built solely from the XML successors,
start index and optional size. It neither reads nor recognizes target formulas.
The original successor-walk source encoding remains an independent oracle.

Proof of the alternative encoding: successor range plus Distinct is a
permutation of n labels. Its non-fixed labels A are closed under successor
(otherwise a fixed label would have two predecessors). Let m=|A|>1. Distinct
ranks in [0,m) form a bijection A -> [0,m). Requiring each edge to advance the
rank cyclically makes every orbit length a positive multiple of m. An orbit
has at most m labels, hence has exactly m and covers A. Conversely, enumerate
the one active cycle from any anchor to provide ranks 0,...,m-1, and assign
-1 to fixed labels. This proves equivalence to exactly one nontrivial cycle;
self loops, arbitrary start indices and the optional exact size are retained.

Unused ranks and the total lookup default cannot change the public relation:
all fixed ranks are -1, all reads are in the declared label interval, and the
explicit [-1,n-1] bounds are consequences of the guarded rank conditions.
"""
import z3


def cyclic_order_witness(successors, *, start=0, size=None):
    """Return (complete circuit formula, private Int witnesses)."""
    xs=tuple(successors);n=len(xs)
    if n<2 or type(start) is not int or any(not z3.is_int(x) for x in xs):
        raise ValueError('circuit needs at least two Int successors and an integer start')
    if size is not None and not z3.is_int(size):
        raise ValueError('circuit size must be Int')
    labels=tuple(range(start,start+n))
    active=tuple(x!=label for x,label in zip(xs,labels))
    count=z3.Sum(*[z3.If(a,1,0) for a in active])
    ranks=tuple(z3.FreshInt('source_circuit_order') for _ in xs)
    parts=[z3.And(start<=x,x<=start+n-1) for x in xs]
    parts.extend([z3.Distinct(*xs),count>1])
    if size is not None:parts.append(count==size)
    table=z3.K(z3.IntSort(),z3.IntVal(0))
    for label,rank,enabled in zip(labels,ranks,active):
        parts.append(z3.And(-1<=rank,rank<=n-1))
        parts.append(z3.Implies(enabled,z3.And(0<=rank,rank<count)))
        parts.append(z3.Implies(z3.Not(enabled),rank==-1))
        table=z3.Store(table,label,rank)
    parts.append(z3.Distinct(*[z3.If(a,p,-1-i) for i,(a,p) in enumerate(zip(active,ranks))]))
    for value,rank,enabled in zip(xs,ranks,active):
        parts.append(z3.Implies(enabled,z3.Select(table,value)==z3.If(rank+1==count,0,rank+1)))
    return z3.And(*parts),ranks
