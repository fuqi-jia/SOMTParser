"""Exact normalization of unconditional, bounded, single-coordinate predicates.

Only whole top-level conjuncts are grouped. The conjunction itself must imply
finite integer bounds. Every integer inside that hull is checked by constant
substitution and simplification; the complete allowed set replaces the group.
Constraints involving other coordinates, definitions and costs remain present.
The enumeration threshold only skips normalization, never weakens a formula.
"""
import z3

from .boolean_structure import structural_equivalence
from .finite_domain_bounds import _conjuncts, _domain, _coordinate_number


def normalize_unary_finite_domains(formula, max_values=65536, audit_callback=None):
    if not z3.is_bool(formula):
        raise ValueError("unary normalization requires a Boolean formula")
    if not isinstance(max_values, int) or isinstance(max_values, bool) or max_values < 1:
        raise ValueError("max_values must be a positive integer")
    clauses = _conjuncts(z3.simplify(formula))
    memo, symbols = {}, {}
    allowed = {z3.Z3_OP_TRUE, z3.Z3_OP_FALSE, z3.Z3_OP_ANUM,
               z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_NOT, z3.Z3_OP_IMPLIES,
               z3.Z3_OP_XOR, z3.Z3_OP_ITE, z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT,
               z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT,
               z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL,
               z3.Z3_OP_IDIV, z3.Z3_OP_REM, z3.Z3_OP_MOD}

    def coordinate(node):
        # The cache belongs to this call/context. None means unsupported or
        # multiple coordinates; an empty set means a closed built-in term.
        stack = [(node, False)]
        while stack:
            term, ready = stack.pop()
            key = term.get_id()
            if key in memo:
                continue
            if not z3.is_app(term) or term.sort().kind() not in (z3.Z3_INT_SORT, z3.Z3_BOOL_SORT):
                memo[key] = None
                continue
            kind = term.decl().kind()
            if kind == z3.Z3_OP_UNINTERPRETED:
                if z3.is_const(term) and term.sort().kind() == z3.Z3_INT_SORT:
                    memo[key] = frozenset((key,))
                    symbols[key] = term
                else:
                    memo[key] = None
                continue
            if kind not in allowed:
                memo[key] = None
                continue
            if not ready:
                stack.append((term, True))
                stack.extend((child, False) for child in term.children())
                continue
            found = set()
            for child in term.children():
                value = memo[child.get_id()]
                if value is None:
                    found = None
                    break
                found.update(value)
                if len(found) > 1:
                    found = None
                    break
            memo[key] = None if found is None else frozenset(found)
        found = memo[node.get_id()]
        return next(iter(found)) if found is not None and len(found) == 1 else None

    groups = {}
    for index, clause in enumerate(clauses):
        key = coordinate(clause)
        if key is not None:
            groups.setdefault(key, []).append(index)
    comparison = (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT)
    reverse = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
               z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}
    negate = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_LT: z3.Z3_OP_GE,
              z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_GT: z3.Z3_OP_LE}
    replaced, removed, normalized, checked = {}, set(), 0, 0
    for key, indices in groups.items():
        low, high = None, None
        for index in indices:
            term = clauses[index]
            domain = _domain(term) if z3.is_eq(term) or z3.is_or(term) else None
            if domain is not None and domain[0].get_id() == key:
                ends = domain[1]
                if all(value.denominator == 1 for value in ends):
                    lo, hi = int(min(ends)), int(max(ends))
                    low = lo if low is None else max(low, lo)
                    high = hi if high is None else min(high, hi)
            negative = z3.is_not(term)
            atom = term.arg(0) if negative else term
            if not z3.is_app(atom) or atom.num_args() != 2 or atom.decl().kind() not in comparison:
                continue
            kind = negate[atom.decl().kind()] if negative else atom.decl().kind()
            pair = _coordinate_number(atom.arg(0), atom.arg(1))
            if pair is None:
                pair = _coordinate_number(atom.arg(1), atom.arg(0))
                if pair is not None:
                    kind = reverse[kind]
            if pair is None or pair[0].get_id() != key or pair[1].denominator != 1:
                continue
            value = int(pair[1])
            if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT):
                value += kind == z3.Z3_OP_GT
                low = value if low is None else max(low, value)
            else:
                value -= kind == z3.Z3_OP_LT
                high = value if high is None else min(high, value)
        if low is None or high is None or high - low + 1 > max_values:
            continue
        symbol = symbols[key]
        group = z3.And(*(clauses[index] for index in indices))
        accepted, definite = [], True
        for value in range(low, high + 1):
            result = z3.simplify(z3.substitute(group, (symbol, z3.IntVal(value, ctx=formula.ctx))))
            checked += 1
            if z3.is_true(result):
                accepted.append(value)
            elif not z3.is_false(result):
                definite = False
                break
        if not definite:
            continue
        replacement = (z3.Or(*(symbol == z3.IntVal(value, ctx=formula.ctx) for value in accepted))
                       if accepted else z3.BoolVal(False, ctx=formula.ctx))
        replaced[indices[0]] = replacement
        removed.update(indices[1:])
        normalized += 1
        if audit_callback is not None:
            audit_callback(dict(coordinate=str(symbol), clause_indices=indices, low=low, high=high,
                                allowed_values=accepted, values_checked=max(0, high-low+1)))
    output = [replaced.get(index, term) for index, term in enumerate(clauses) if index not in removed]
    result = z3.And(*output) if output else z3.BoolVal(True, ctx=formula.ctx)
    return result, dict(input_conjuncts=len(clauses), output_conjuncts=len(output),
                        normalized_coordinates=normalized, values_checked=checked,
                        public_coordinates_preserved=True, complete_allowed_sets_retained=True)


def unary_finite_domain_equivalence(left, right, max_values=65536,
                                    progress_callback=None, audit_callback=None):
    if left.ctx != right.ctx:
        raise ValueError("complete relation comparison requires one context")
    outputs, reports = [], []
    for side, formula in enumerate((left, right)):
        if progress_callback:
            progress_callback(dict(phase="unary-finite-domain-started", side=side))
        callback = None if audit_callback is None else lambda record, side=side: audit_callback(dict(side=side, **record))
        output, report = normalize_unary_finite_domains(formula, max_values, callback)
        outputs.append(output)
        reports.append(report)
        if progress_callback:
            progress_callback(dict(phase="unary-finite-domain-completed", side=side, **report))
    proof = structural_equivalence(*outputs)
    return dict(equivalent=proof["equivalent"], normalization=reports, structural_proof=proof,
                solver_queries=0, complete_relation_and_ordered_costs_preserved=True)
