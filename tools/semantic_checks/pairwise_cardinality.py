"""Compress complete explicit Boolean mutex cliques without expanding a target.

For arbitrary Boolean atoms p[0] ... p[n-1], the conjunction of every
not(p[i] and p[j]), i < j, is exactly sum(If(p[i], 1, 0)) <= 1.
This identity needs no independence, finite domain, or arithmetic assumptions.
Only complete connected components of the actual input edge set are replaced.
The scan is linear in the input clauses apart from union/find; output adds one
term per atom and never enumerates missing pairs.
"""
from dataclasses import dataclass
import z3


@dataclass(frozen=True)
class PairwiseCompression:
    formula: object
    components: int
    consumed_clauses: int
    original_conjuncts: int
    generated_indicator_terms: int


def compress_pairwise_at_most_one(formula):
    """Return an equivalent complete formula; unmatched clauses remain intact.

    AST identities belong to one input context and all nodes are retained while
    indexed. Duplicate edges do not establish completeness twice. Self-pairs
    stay as original unary restrictions. Components with fewer than three
    atoms are left unchanged, since compressing them provides no size saving.
    """
    if not z3.is_bool(formula):
        raise ValueError('pairwise compression requires a Boolean formula')
    clauses, todo = [], [formula]
    while todo:
        node = todo.pop()
        if z3.is_and(node):
            todo.extend(reversed(node.children()))
        else:
            clauses.append(node)
    atoms, parent, rank, edges = {}, {}, {}, {}

    def find(key):
        while parent[key] != key:
            parent[key] = parent[parent[key]]
            key = parent[key]
        return key

    def join(a, b):
        a, b = find(a), find(b)
        if a == b:
            return
        if rank[a] < rank[b]:
            a, b = b, a
        parent[b] = a
        if rank[a] == rank[b]:
            rank[a] += 1

    for index, node in enumerate(clauses):
        pair = None
        if z3.is_or(node) and node.num_args() == 2:
            a, b = node.children()
            if z3.is_not(a) and z3.is_not(b):
                pair = (a.arg(0), b.arg(0))
        elif z3.is_not(node) and z3.is_and(node.arg(0)):
            body = node.arg(0)
            if body.num_args() == 2:
                pair = tuple(body.children())
        if pair is None or pair[0].eq(pair[1]):
            continue
        for atom in pair:
            key = atom.get_id()
            if key not in atoms:
                atoms[key] = atom
                parent[key], rank[key] = key, 0
        a, b = sorted(atom.get_id() for atom in pair)
        edges.setdefault((a, b), []).append(index)
        join(a, b)
    vertices, grouped_edges = {}, {}
    for key in atoms:
        vertices.setdefault(find(key), []).append(key)
    for edge in edges:
        grouped_edges.setdefault(find(edge[0]), []).append(edge)
    replacements, consumed = [], set()
    terms = 0
    for root, keys in vertices.items():
        n = len(keys)
        component_edges = grouped_edges[root]
        # A loop-free simple graph has at most n*(n-1)/2 distinct edges.
        # Equality proves it is complete; no quadratic missing-edge scan.
        if n < 3 or len(component_edges) != n * (n - 1) // 2:
            continue
        ordered = [atoms[key] for key in sorted(keys)]
        replacements.append(z3.Sum(*[z3.If(atom, 1, 0) for atom in ordered]) <= 1)
        terms += n
        for edge in component_edges:
            consumed.update(edges[edge])
    if not replacements:
        return PairwiseCompression(formula, 0, 0, len(clauses), 0)
    result = z3.And(*[node for index, node in enumerate(clauses)
                     if index not in consumed], *replacements)
    return PairwiseCompression(result, len(replacements), len(consumed),
                               len(clauses), terms)
