"""Exactly match and normalize an existential finite circuit-rank witness.

The accepted body describes a permutation x of consecutive integer labels,
without self loops, together with a total rank array r: 0 <= r[i] < n,
r[first] = 0, and x[i] = first or r[x[i]] = r[i] + 1. The whole body must
match, modulo the qualified Boolean structural identities. Extra assertions
are never discarded. No symbol spelling, problem family or external domain
is used to identify the relation.

Proof of normalization: a finite permutation partitions the nodes into cycles.
A cycle not containing first would strictly increase integer rank around a
closed walk, an impossibility. Thus all nodes belong to the first's cycle.
Conversely, distance from first along any Hamiltonian cycle supplies every
required rank; a total array extends those finitely many values arbitrarily.
The replacement uses distinct positions 1..n, anchored at first, with each
edge advancing modulo n. Their bijection implies that any edge cycle has
length divisible by n; hence it is the same single Hamiltonian cycle. Positions
along that cycle give the converse witness. Both relations therefore have
exactly the same free-variable assignments, including within larger signed
cost relations. Only the private existential witness changes.
"""
from dataclasses import dataclass

import z3

from .boolean_structure import structural_equivalence


@dataclass(frozen=True)
class CircuitRankNormalization:
    formula: object
    normalized_circuits: int = 0
    nodes: tuple = ()


def _conjuncts(body):
    pending = [body]
    while pending:
        node = pending.pop()
        if z3.is_and(node):
            pending.extend(reversed(node.children()))
        else:
            yield node


def _read(node, array):
    return (z3.is_select(node) and node.arg(0).eq(array)
            and node.num_args() == 2)


def _ground_index(node, array):
    if _read(node, array) and z3.is_int_value(node.arg(1)):
        return node.arg(1).as_long()
    return None


def _closed_rank_free(term, rank):
    pending, seen = [term], set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if node.eq(rank) or z3.is_var(node) or z3.is_quantifier(node):
            return False
        pending.extend(node.children())
    return True


def _increment_index(node, rank):
    if not z3.is_add(node) or node.num_args() != 2:
        return None
    for one, read in (node.children(), tuple(reversed(node.children()))):
        if z3.is_int_value(one) and one.as_long() == 1:
            index = _ground_index(read, rank)
            if index is not None:
                return index
    return None


def _edge(clause, rank, first):
    if not z3.is_or(clause) or clause.num_args() != 2:
        return None
    for returning, stepping in (clause.children(), tuple(reversed(clause.children()))):
        if not z3.is_eq(returning) or not z3.is_eq(stepping):
            continue
        for root, successor in (returning.children(), tuple(reversed(returning.children()))):
            if not (z3.is_int_value(root) and root.as_long() == first
                    and z3.is_int(successor) and _closed_rank_free(successor, rank)):
                continue
            for destination, increment in (stepping.children(), tuple(reversed(stepping.children()))):
                if not (_read(destination, rank) and destination.arg(1).eq(successor)):
                    continue
                index = _increment_index(increment, rank)
                if index is not None:
                    return index, successor
    return None


def _match_form(body):
    """Use only the exact two-operand DISTINCT/NOT-EQ identity.

    Whole-expression simplify can isolate opposite orientations of an
    arithmetic equality differently. Keep arithmetic ASTs intact for the
    qualified symmetric equality/addition matcher instead of solving them.
    """
    pending, seen, pairs = [body], set(), []
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_quantifier(node):
            continue
        if z3.is_distinct(node) and node.num_args() == 2:
            pairs.append((node, z3.Not(node.arg(0) == node.arg(1))))
        pending.extend(node.children())
    return z3.substitute(body, *pairs) if pairs else body


def _normalize_one(formula):
    if not (z3.is_quantifier(formula) and formula.is_exists()
            and formula.num_vars() == 1 and not formula.num_patterns()
            and not formula.num_no_patterns()):
        return None
    sort = formula.var_sort(0)
    if not (sort.kind() == z3.Z3_ARRAY_SORT
            and sort.domain().kind() == z3.Z3_INT_SORT
            and sort.range().kind() == z3.Z3_INT_SORT):
        return None
    rank = z3.FreshConst(sort, 'matched_rank')
    body = z3.substitute_vars(formula.body(), rank)
    clauses = list(_conjuncts(body))
    anchors = set()
    for clause in clauses:
        if not z3.is_eq(clause):
            continue
        for read, zero in (clause.children(), tuple(reversed(clause.children()))):
            index = _ground_index(read, rank)
            if index is not None and z3.is_int_value(zero) and zero.as_long() == 0:
                anchors.add(index)
    if len(anchors) != 1:
        return None
    first = anchors.pop()
    edges = {}
    for clause in clauses:
        found = _edge(clause, rank, first)
        if found is not None:
            index, successor = found
            if index in edges and not edges[index].eq(successor):
                return None
            edges[index] = successor
    n = len(edges)
    if n < 2 or sorted(edges) != list(range(first, first + n)):
        return None
    xs = [edges[i] for i in range(first, first + n)]
    parts = [z3.Distinct(*xs), rank[first] == 0]
    for i, x in enumerate(xs, first):
        parts.extend((x >= first, x < first + n, x != i,
                      rank[i] >= 0, rank[i] < n,
                      z3.Or(x == first, rank[x] == rank[i] + 1)))
    expected = z3.And(*parts)
    if not structural_equivalence(_match_form(body),
                                  _match_form(expected))['equivalent']:
        return None
    # This is the complete cyclic-position contract used independently by
    # the official FlatZinc source semantics, without any inferred bounds.
    order = [z3.FreshInt('circuit_position', ctx=body.ctx) for _ in xs]
    lookup = z3.K(z3.IntSort(ctx=body.ctx), z3.IntVal(0, ctx=body.ctx))
    for i, value in enumerate(order, first):
        lookup = z3.Store(lookup, i, value)
    parts = [z3.Distinct(*xs), z3.Distinct(*order), order[0] == 1]
    parts.extend(z3.And(value >= 1, value <= n) for value in order)
    parts.extend(z3.And(x >= first, x < first + n, x != first + i,
                       z3.Select(lookup, x) == z3.If(order[i] == n, 1, order[i] + 1))
                 for i, x in enumerate(xs))
    return z3.Exists(order, z3.And(*parts)), n


def normalize_root_circuit_ranks(formula):
    """Normalize fully recognized root-conjunct witnesses; keep all else.

    Unsupported encodings, nonconjunctive contexts, patterns, and outer
    quantifiers retain their exact input AST. Call before opening private
    array binders or simplifying away the full recognizable contract.
    """
    if not z3.is_bool(formula):
        raise TypeError('the complete relation must be Boolean')
    parts, sizes = [], []
    for clause in _conjuncts(formula):
        found = _normalize_one(clause)
        if found is None:
            parts.append(clause)
        else:
            normalized, n = found
            parts.append(normalized)
            sizes.append(n)
    if not sizes:
        return CircuitRankNormalization(formula)
    return CircuitRankNormalization(z3.And(*parts), len(sizes), tuple(sizes))
