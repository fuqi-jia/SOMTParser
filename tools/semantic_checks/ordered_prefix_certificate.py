"""Finite prefix injection certificate for an actual ordered-row UNSAT core.

All premises must occur as unconditional conjuncts of the supplied formulas.
Rows are strictly increasing integers bounded below by ``low``. Every row pair
has a shared valid index where both selected values lie in [low, high] and
differ. A row's values in that interval form a finite increasing prefix.
Prefixes with the same members below ``high`` agree at every shared position;
hence each row requires a distinct finite code. More rows than codes is UNSAT.
This verifies a sufficient core, never claims equivalence of entire inputs.
"""
from itertools import combinations

import z3

from .finite_domain_bounds import _conjuncts, _coordinate_number
from .retained_square_domains import _bound, _int_coordinate


def finite_prefix_injection(length, low, high):
    if any(not isinstance(v, int) or isinstance(v, bool) for v in (length, low, high)):
        raise ValueError("prefix parameters must be integers")
    if length < 1 or high < low or high - low > 10:
        raise ValueError("prefix alphabet is outside this finite certificate")
    prefixes = [p for n in range(min(length, high-low+1)+1)
                for p in combinations(range(low, high+1), n)]
    codes = [tuple(v for v in p if v < high) for p in prefixes]
    pairs_checked = 0
    for i, a in enumerate(prefixes):
        for j, b in enumerate(prefixes):
            if codes[i] == codes[j]:
                if any(x != y for x, y in zip(a, b)):
                    raise AssertionError("prefix injection law failed")
                pairs_checked += 1
    return dict(length=length, low=low, high=high, prefixes=len(prefixes),
                finite_codes=len(set(codes)), equal_code_pairs_checked=pairs_checked,
                prefix_table=[dict(prefix=list(p), code=list(c)) for p, c in zip(prefixes, codes)])


def _strict_order(term):
    negated = z3.is_not(term)
    atom = term.arg(0) if negated else term
    if not z3.is_app(atom) or atom.num_args() != 2:
        return None
    kind = atom.decl().kind()
    if negated:
        kind = {z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_LE: z3.Z3_OP_GT}.get(kind)
    a, b = atom.children()
    if not _int_coordinate(a) or not _int_coordinate(b):
        return None
    if kind == z3.Z3_OP_LT:
        return a.get_id(), b.get_id()
    if kind == z3.Z3_OP_GT:
        return b.get_id(), a.get_id()
    return None


def _element(term):
    if not z3.is_or(term):
        return None
    branches, pending = [], [term]
    while pending:
        node = pending.pop()
        if z3.is_or(node):
            pending.extend(node.children())
        else:
            branches.append(node)
    records, shared = [], None
    for branch in branches:
        atoms = _conjuncts(branch)
        if len(atoms) != 2 or not all(z3.is_eq(a) and a.num_args() == 2 for a in atoms):
            return None
        index, value_pair = None, None
        for atom in atoms:
            a, b = atom.children()
            if _int_coordinate(a) and _int_coordinate(b) and not z3.eq(a, b):
                if value_pair is not None:
                    return None
                value_pair = frozenset((a.get_id(), b.get_id()))
            else:
                pair = _coordinate_number(a, b) or _coordinate_number(b, a)
                if pair is None or not _int_coordinate(pair[0]) or pair[1].denominator != 1 or index is not None:
                    return None
                index = (pair[0].get_id(), int(pair[1]))
        if index is None or value_pair is None:
            return None
        shared = value_pair if shared is None else shared & value_pair
        records.append((index, value_pair))
    if shared is None or len(shared) != 1:
        return None
    value = next(iter(shared))
    index_ids = {index[0] for index, _ in records}
    if len(index_ids) != 1:
        return None
    cells = {}
    for (_, position), pair in records:
        cell = next(iter(pair - {value}))
        if position in cells and cells[position] != cell:
            return None
        cells[position] = cell
    if set(cells) != set(range(len(cells))):
        return None
    return next(iter(index_ids)), value, tuple(cells[i] for i in range(len(cells)))


def ordered_prefix_unsat(assertions, rows, pair_variables, low=0, high=5):
    """Verify every core premise before applying the finite pigeonhole law.

    ``pair_variables[(i,j)]`` is (shared_index, selected_left, selected_right).
    The returned indices address the complete simplified top-level conjuncts.
    Unrecognized encodings or absent premises return inconclusive.
    """
    if not rows or not rows[0]:
        raise ValueError("nonempty rows required")
    length = len(rows[0])
    if any(len(row) != length for row in rows):
        raise ValueError("row lengths differ")
    coordinates = [x for row in rows for x in row]
    coordinates += [x for values in pair_variables.values() for x in values]
    if any(not _int_coordinate(x) for x in coordinates):
        raise ValueError("all core coordinates must be free Int constants")
    context = coordinates[0].ctx
    if any(x.ctx != context for x in coordinates) or any(a.ctx != context for a in assertions):
        raise ValueError("one context required")
    if len({x.get_id() for x in coordinates}) != len(coordinates):
        raise ValueError("distinct core coordinates required")
    lemma = finite_prefix_injection(length, low, high)
    needed_pairs = set(combinations(range(len(rows)), 2))
    if set(pair_variables) != needed_pairs:
        return dict(passed=False, status="inconclusive", reason="incomplete row pair map")
    clauses = _conjuncts(z3.simplify(z3.And(*assertions)))
    bounds, orders, elements, unequal = {}, {}, {}, {}
    for index, term in enumerate(clauses):
        bound = _bound(term)
        if bound is not None:
            coordinate, direction, value = bound
            table = bounds.setdefault(coordinate.get_id(), {})
            previous = table.get(direction)
            if previous is None or (value > previous[0] if direction == "lower" else value < previous[0]):
                table[direction] = (value, index)
        order = _strict_order(term)
        if order is not None:
            orders[order] = index
        element = _element(term)
        if element is not None:
            elements[element] = index
        atom = term.arg(0) if z3.is_not(term) and z3.is_eq(term.arg(0)) else None
        if atom is None and z3.is_app(term) and term.decl().kind() == z3.Z3_OP_DISTINCT and term.num_args() == 2:
            atom = term
        if atom is not None and atom.num_args() == 2 and all(_int_coordinate(x) for x in atom.children()):
            unequal[frozenset(x.get_id() for x in atom.children())] = index
    used = set()
    missing = []
    def require_bound(coordinate, direction, limit):
        item = bounds.get(coordinate.get_id(), {}).get(direction)
        good = item is not None and (item[0] >= limit if direction == "lower" else item[0] <= limit)
        if good:
            used.add(item[1])
        else:
            missing.append("bound:" + str(coordinate) + ":" + direction)
    for row in rows:
        for coordinate in row:
            require_bound(coordinate, "lower", low)
        for a, b in zip(row, row[1:]):
            item = orders.get((a.get_id(), b.get_id()))
            if item is None:
                missing.append("strict-order:" + str(a) + ":" + str(b))
            else:
                used.add(item)
    for (i, j), (position, left, right) in pair_variables.items():
        require_bound(position, "lower", 0)
        require_bound(position, "upper", length-1)
        for value in (left, right):
            require_bound(value, "lower", low)
            require_bound(value, "upper", high)
        for value, row in ((left, rows[i]), (right, rows[j])):
            item = elements.get((position.get_id(), value.get_id(), tuple(x.get_id() for x in row)))
            if item is None:
                missing.append("element:" + str(position) + ":" + str(value))
            else:
                used.add(item)
        item = unequal.get(frozenset((left.get_id(), right.get_id())))
        if item is None:
            missing.append("unequal:" + str(left) + ":" + str(right))
        else:
            used.add(item)
    passed = not missing and len(rows) > lemma["finite_codes"]
    return dict(passed=passed, status="unsat" if passed else "inconclusive",
                rows=len(rows), checked_pairs=len(needed_pairs), lemma=lemma,
                missing=missing, simplified_conjuncts=len(clauses),
                premise_indices=sorted(used), whole_input_unsat=passed,
                proof_kind="actual unconditional ordered-prefix core and finite pigeonhole")
