"""Exact removal of bounds implied by retained, unconditional finite domains.

Only top-level conjunctions are inspected. A domain is an explicit disjunction
of numeral equalities or finite closed integer intervals for one coordinate.
Every removed bound holds at all interval endpoints, hence on the retained
domain. Domain holes are never filled in the formula. No variable,
definition, objective coordinate, or conditional constraint is projected away.
Structural mismatch of the resulting complete formulas is inconclusive.
"""
from fractions import Fraction

import z3

from .boolean_structure import structural_equivalence


def _conjuncts(formula):
    pending = [formula]
    result = []
    while pending:
        current = pending.pop()
        if z3.is_and(current):
            pending.extend(reversed(current.children()))
        else:
            result.append(current)
    return result


def _number(term):
    if z3.is_int_value(term):
        return Fraction(term.as_long())
    if z3.is_rational_value(term):
        return Fraction(term.numerator_as_long(), term.denominator_as_long())
    return None


def _coordinate(term):
    return (z3.is_const(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and term.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT))


def _coordinate_number(first, second):
    value = _number(second)
    if _coordinate(first) and value is not None:
        return first, value
    return None


def _interval(term):
    """Recognize an actual conjunction defining one finite integer interval."""
    if not z3.is_and(term):
        return None
    coordinate, low, high = None, None, None
    for atom in _conjuncts(term):
        negated = z3.is_not(atom)
        if negated:
            atom = atom.arg(0)
        if not z3.is_app(atom) or atom.num_args() != 2:
            return None
        kind = atom.decl().kind()
        if kind not in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
            return None
        if negated:
            kind = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_LT: z3.Z3_OP_GE,
                    z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_GT: z3.Z3_OP_LE}[kind]
        pair = _coordinate_number(atom.arg(0), atom.arg(1))
        if pair is None:
            pair = _coordinate_number(atom.arg(1), atom.arg(0))
            if pair is not None:
                kind = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
                        z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}[kind]
        if pair is None or pair[0].sort().kind() != z3.Z3_INT_SORT or pair[1].denominator != 1:
            return None
        symbol, value = pair
        if coordinate is not None and not z3.eq(coordinate, symbol):
            return None
        coordinate = symbol
        if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT):
            value -= int(kind == z3.Z3_OP_LT)
            high = value if high is None else min(high, value)
        else:
            value += int(kind == z3.Z3_OP_GT)
            low = value if low is None else max(low, value)
    if coordinate is None or low is None or high is None:
        return None
    return coordinate, low, high


def _domain(term):
    # Singleton equalities are domains too, but are never removed by this pass.
    pending = [term]
    symbol = None
    values = set()
    while pending:
        atom = pending.pop()
        if z3.is_or(atom):
            pending.extend(atom.children())
            continue
        interval = _interval(atom)
        if interval is not None:
            coordinate, low, high = interval
            if symbol is not None and not z3.eq(symbol, coordinate):
                return None
            symbol = coordinate
            if low <= high:
                values.update((low, high))
            continue
        if not z3.is_eq(atom) or atom.num_args() != 2:
            return None
        pair = (_coordinate_number(atom.arg(0), atom.arg(1))
                or _coordinate_number(atom.arg(1), atom.arg(0)))
        if pair is None:
            return None
        coordinate, value = pair
        if symbol is not None and not z3.eq(symbol, coordinate):
            return None
        symbol = coordinate
        values.add(value)
    if symbol is None or not values:
        return None
    # Linear order bounds are implied on a union exactly when they hold at
    # its extreme endpoints. The original complete union remains asserted.
    return symbol, tuple(sorted({min(values), max(values)}))


def remove_entailed_finite_domain_bounds(formula, audit_callback=None):
    """Return a formula equivalent to the complete input and exact audit counts.

    Z3's semantics-preserving simplifier runs first. Audit indices address the
    resulting flattened top-level conjunction. Domain clauses stay present;
    only arithmetic <, <=, >, >= clauses justified by them can be removed.
    """
    if not z3.is_bool(formula):
        raise ValueError("finite-domain bound removal requires a Boolean formula")
    simplified = z3.simplify(formula)
    conjuncts = _conjuncts(simplified)
    domains = {}
    for index, term in enumerate(conjuncts):
        if not (z3.is_or(term) or z3.is_eq(term)):
            continue
        found = _domain(term)
        if found is not None:
            coordinate, values = found
            key = coordinate.get_id()
            previous = domains.get(key)
            if previous is None or len(values) < len(previous[1]):
                domains[key] = (index, values)
    kept, removed = [], 0
    comparison_kinds = (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT)
    for index, term in enumerate(conjuncts):
        # simplify represents strict comparisons as negated non-strict ones.
        # This is only a top-level atomic bound, never a conditional domain.
        negated = z3.is_not(term)
        atom = term.arg(0) if negated else term
        if (not z3.is_app(atom) or atom.decl().kind() not in comparison_kinds
                or atom.num_args() != 2):
            kept.append(term)
            continue
        kind = atom.decl().kind()
        if negated:
            kind = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_LT: z3.Z3_OP_GE,
                    z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_GT: z3.Z3_OP_LE}[kind]
        pair = _coordinate_number(atom.arg(0), atom.arg(1))
        if pair is None:
            pair = _coordinate_number(atom.arg(1), atom.arg(0))
            if pair is not None:
                kind = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
                        z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}[kind]
        domain = None if pair is None else domains.get(pair[0].get_id())
        if domain is None:
            kept.append(term)
            continue
        domain_index, values = domain
        limit = pair[1]
        def accepts(value):
            if kind == z3.Z3_OP_LE:
                return value <= limit
            if kind == z3.Z3_OP_LT:
                return value < limit
            if kind == z3.Z3_OP_GE:
                return value >= limit
            return value > limit
        if not all(accepts(value) for value in values):
            kept.append(term)
            continue
        removed += 1
        if audit_callback is not None:
            audit_callback(dict(bound_index=index, retained_domain_index=domain_index,
                                exact_value_count=len(values)))
    result = z3.And(*kept) if kept else z3.BoolVal(True, ctx=formula.ctx)
    return result, dict(input_conjuncts=len(conjuncts), retained_conjuncts=len(kept),
                        finite_domains=len(domains), removed_entailed_bounds=removed,
                        all_domain_clauses_retained=True, public_coordinates_preserved=True)


def finite_domain_structural_equivalence(left, right, progress_callback=None,
                                         audit_callback=None):
    """Sufficient complete-relation proof; no satisfiability search is used."""
    if left.ctx != right.ctx:
        raise ValueError("complete relation comparison requires one Z3 context")
    normalized, reports = [], []
    for side, formula in enumerate((left, right)):
        if progress_callback is not None:
            progress_callback(dict(phase="finite-domain-bound-normalization-started", side=side))
        callback = None if audit_callback is None else lambda record, side=side: audit_callback(dict(side=side, **record))
        result, report = remove_entailed_finite_domain_bounds(formula, callback)
        normalized.append(result)
        reports.append(report)
        if progress_callback is not None:
            progress_callback(dict(phase="finite-domain-bound-normalization-completed", side=side, **report))
    proof = structural_equivalence(*normalized)
    return dict(equivalent=proof["equivalent"], method="retained finite domains and complete structural correspondence",
                normalization=reports, structural_proof=proof, solver_queries=0,
                all_public_definitions_retained=True, ordered_cost_coordinates_preserved=True)
