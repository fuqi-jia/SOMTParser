"""Compress complete tuple-disequality cliques under original integer bounds.

The opposite relation only suggests an arithmetic packing. Its coefficients,
offsets, every source-side digit bound, and every clique edge are independently
checked. A missing edge or a possible carry leaves the original formula intact.
"""
from dataclasses import dataclass
import z3
from .qf_conjuncts import _conjuncts


@dataclass(frozen=True)
class PackedTupleProjection:
    formula: object
    certificates: tuple
    consumed_clauses: int = 0


def _scalar(node):
    return (z3.is_const(node) and z3.is_int(node)
            and node.decl().kind() == z3.Z3_OP_UNINTERPRETED)


def _affine(node):
    terms, offset, pending = {}, 0, [(node, 1)]
    while pending:
        value, scale = pending.pop()
        if not z3.is_int(value):
            return None
        if z3.is_int_value(value):
            offset += scale * value.as_long()
        elif _scalar(value):
            key = value.get_id()
            old = terms.get(key, (value, 0))
            terms[key] = (value, old[1] + scale)
        else:
            kind = value.decl().kind()
            children = value.children()
            if kind == z3.Z3_OP_ADD:
                pending.extend((child, scale) for child in children)
            elif kind == z3.Z3_OP_SUB:
                pending.extend((child, scale if index == 0 else -scale)
                               for index, child in enumerate(children))
            elif kind == z3.Z3_OP_UMINUS:
                pending.append((children[0], -scale))
            elif kind == z3.Z3_OP_MUL:
                nonnumeric = []
                for child in children:
                    if z3.is_int_value(child):
                        scale *= child.as_long()
                    else:
                        nonnumeric.append(child)
                if len(nonnumeric) != 1:
                    return None
                pending.append((nonnumeric[0], scale))
            else:
                return None
    return [(value, coefficient) for value, coefficient in terms.values()
            if coefficient], offset


def _bounds(clauses):
    result = {}
    reverse = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_GE: z3.Z3_OP_LE,
               z3.Z3_OP_LT: z3.Z3_OP_GT, z3.Z3_OP_GT: z3.Z3_OP_LT,
               z3.Z3_OP_EQ: z3.Z3_OP_EQ}
    for clause in clauses:
        if not z3.is_app(clause) or clause.num_args() != 2:
            continue
        kind = clause.decl().kind()
        if kind not in reverse:
            continue
        a, b = clause.children()
        if z3.is_int_value(a) and _scalar(b):
            a, b, kind = b, a, reverse[kind]
        if not _scalar(a) or not z3.is_int_value(b):
            continue
        low, high = result.setdefault(a.get_id(), [None, None])
        value = b.as_long()
        if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ):
            bound = value + (kind == z3.Z3_OP_GT)
            low = bound if low is None else max(low, bound)
        if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_EQ):
            bound = value - (kind == z3.Z3_OP_LT)
            high = bound if high is None else min(high, bound)
        result[a.get_id()] = [low, high]
    return result


def _packing(candidate, bounds):
    if not z3.is_distinct(candidate) or candidate.num_args() < 2:
        return None
    rows, expected, offset, identities = [], None, None, set()
    for expression in candidate.children():
        affine = _affine(expression)
        if affine is None:
            return None
        terms, constant = affine
        terms.sort(key=lambda item: item[1])
        coefficients = tuple(coefficient for _, coefficient in terms)
        if (len(terms) < 2 or any(c <= 0 for c in coefficients)
                or len(set(coefficients)) != len(coefficients)):
            return None
        if expected is None:
            expected, offset = coefficients, constant
        elif coefficients != expected or constant != offset:
            return None
        row = tuple(value for value, _ in terms)
        for value in row:
            key = value.get_id()
            if key in identities or key not in bounds:
                return None
            low, high = bounds[key]
            if low is None or high is None or low > high:
                return None
            identities.add(key)
        rows.append(row)
    lower = [min(bounds[row[column].get_id()][0] for row in rows)
             for column in range(len(expected))]
    upper = [max(bounds[row[column].get_id()][1] for row in rows)
             for column in range(len(expected))]
    # In two distinct integer tuples, take the highest differing position.
    # Its contribution is at least that positive coefficient. All lower
    # contributions together have absolute value at most ``span``. Strict
    # dominance makes cancellation impossible, proving injectivity.
    span = 0
    for coefficient, low, high in zip(expected, lower, upper):
        if coefficient <= span:
            return None
        span += coefficient * (high - low)
    return rows, dict(rows=len(rows), columns=len(expected), weights=expected,
                      lower_bounds=lower, upper_bounds=upper,
                      common_offset=offset, strict_integer_dominance=True)


def _pairs(clause):
    pairs, pending = [], [(clause, False)]
    while pending:
        node, negated = pending.pop()
        if z3.is_not(node):
            pending.append((node.arg(0), not negated))
        elif ((not negated and z3.is_or(node))
              or (negated and z3.is_and(node))):
            pending.extend((child, negated) for child in node.children())
        elif z3.is_true(node) or z3.is_false(node):
            if z3.is_true(node) != negated:
                return None
        elif ((negated and z3.is_eq(node))
              or (not negated and z3.is_distinct(node) and node.num_args() == 2)):
            a, b = node.children()
            if not _scalar(a) or not _scalar(b):
                return None
            pairs.append((a.get_id(), b.get_id()))
        else:
            return None
    return pairs or None


def compress_packed_tuple_cliques(formula, opposite):
    """Return an equivalent formula, guarded by its own retained domain facts."""
    if formula.ctx != opposite.ctx:
        raise ValueError('packed tuple comparison needs one Z3 context')
    candidates = [clause for clause in _conjuncts(opposite)
                  if z3.is_distinct(clause) and clause.num_args() >= 2]
    if not candidates:
        return PackedTupleProjection(formula, ())
    clauses = _conjuncts(formula)
    bounds = _bounds(clauses)
    consumed, replacements, certificates = set(), [], []
    pair_cache = {}
    for candidate in candidates:
        packed = _packing(candidate, bounds)
        if packed is None:
            continue
        rows, certificate = packed
        location = {value.get_id(): (row, column)
                    for row, values in enumerate(rows)
                    for column, value in enumerate(values)}
        edges, matched = set(), set()
        for clause in clauses:
            key = clause.get_id()
            if key in consumed:
                continue
            if key not in pair_cache:
                pair_cache[key] = _pairs(clause)
            pairs = pair_cache[key]
            if pairs is None:
                continue
            edge, columns = None, set()
            for a, b in pairs:
                if a not in location or b not in location:
                    break
                ra, ca = location[a]
                rb, cb = location[b]
                pair = (min(ra, rb), max(ra, rb))
                if ra == rb or ca != cb or (edge is not None and edge != pair):
                    break
                edge = pair
                columns.add(ca)
            else:
                if len(columns) == certificate['columns']:
                    edges.add(edge)
                    matched.add(key)
        required = len(rows) * (len(rows) - 1) // 2
        if len(edges) == required:
            consumed.update(matched)
            replacements.append(candidate)
            certificates.append(dict(certificate, clique_edges=len(edges),
                                     consumed_clauses=len(matched)))
    if not certificates:
        return PackedTupleProjection(formula, ())
    rewritten = z3.And(*[clause for clause in clauses
                         if clause.get_id() not in consumed], *replacements)
    return PackedTupleProjection(rewritten, tuple(certificates), len(consumed))
