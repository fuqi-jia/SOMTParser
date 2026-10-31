"""Remove only domains implied by retained public square definitions and bounds.

No public variable is eliminated. All square equations and their actual input
bound conjuncts stay present. Existential multiplication domains are witnessed
by using the square input for both factors. Explicit output domains are checked
at every integer input permitted by those bounds, without assuming optimality.
"""
from bisect import bisect_right
from math import isqrt

import z3

from .finite_domain_bounds import _conjuncts, _coordinate_number, _interval
from .finite_product_domains import _shape as _product_shape


def _int_coordinate(term):
    return (z3.is_const(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and term.sort().kind() == z3.Z3_INT_SORT)


def _bound(term):
    negated = z3.is_not(term)
    atom = term.arg(0) if negated else term
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
    if pair is None or not _int_coordinate(pair[0]) or pair[1].denominator != 1:
        return None
    coordinate, value = pair[0], int(pair[1])
    if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT):
        return coordinate, "upper", value - int(kind == z3.Z3_OP_LT)
    return coordinate, "lower", value + int(kind == z3.Z3_OP_GT)


def _ranges(term, coordinate):
    # term owns every raw pointer until return. The caches belong to this
    # one call/context; no AST identity survives it or another Z3 context.
    if term.ctx != coordinate.ctx or not _int_coordinate(coordinate):
        return None
    core, context = z3.z3core, term.ctx_ref()
    wanted = coordinate.get_id()
    numerals = {}
    def kind(node):
        if core.Z3_get_ast_kind(context, node) != z3.Z3_APP_AST:
            return None
        app = core.Z3_to_app(context, node)
        return core.Z3_get_decl_kind(context, core.Z3_get_app_decl(context, app))
    def children(node):
        app = core.Z3_to_app(context, node)
        return [core.Z3_get_app_arg(context, app, i)
                for i in range(core.Z3_get_app_num_args(context, app))]
    def number(node):
        identity = core.Z3_get_ast_id(context, node)
        if identity not in numerals:
            if (core.Z3_get_ast_kind(context, node) != z3.Z3_NUMERAL_AST
                    or core.Z3_get_sort_kind(context, core.Z3_get_sort(context, node)) != z3.Z3_INT_SORT):
                numerals[identity] = None
            else:
                text = core.Z3_get_numeral_string(context, node)
                if isinstance(text, bytes):
                    text = text.decode('ascii')
                numerals[identity] = int(text)
        return numerals[identity]
    reverse = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
               z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}
    negate = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_LT: z3.Z3_OP_GE,
              z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_GT: z3.Z3_OP_LE}
    def comparison(node):
        operation = kind(node)
        negative = operation == z3.Z3_OP_NOT
        if negative:
            args = children(node)
            if len(args) != 1:
                return None
            node, operation = args[0], kind(args[0])
        if operation not in reverse and (negative or operation != z3.Z3_OP_EQ):
            return None
        args = children(node)
        if len(args) != 2:
            return None
        if negative:
            operation = negate[operation]
        if core.Z3_get_ast_id(context, args[0]) == wanted:
            value = number(args[1])
        elif core.Z3_get_ast_id(context, args[1]) == wanted:
            value = number(args[0])
            if operation in reverse:
                operation = reverse[operation]
        else:
            return None
        return None if value is None else (operation, value)
    pending, intervals = [term.as_ast()], []
    while pending:
        node = pending.pop()
        operation = kind(node)
        if operation == z3.Z3_OP_OR:
            pending.extend(children(node))
            continue
        if operation == z3.Z3_OP_AND:
            atoms, low, high = children(node), None, None
            while atoms:
                atom = atoms.pop()
                if kind(atom) == z3.Z3_OP_AND:
                    atoms.extend(children(atom))
                    continue
                bound = comparison(atom)
                if bound is None or bound[0] == z3.Z3_OP_EQ:
                    return None
                op, value = bound
                if op in (z3.Z3_OP_LE, z3.Z3_OP_LT):
                    value -= int(op == z3.Z3_OP_LT)
                    high = value if high is None else min(high, value)
                else:
                    value += int(op == z3.Z3_OP_GT)
                    low = value if low is None else max(low, value)
            if low is None or high is None:
                return None
            if low <= high:
                intervals.append((low, high))
        else:
            equality = comparison(node)
            if equality is None or equality[0] != z3.Z3_OP_EQ:
                return None
            intervals.append((equality[1], equality[1]))
    merged = []
    for low, high in sorted(intervals):
        if merged and low <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(high, merged[-1][1]))
        else:
            merged.append((low, high))
    return merged


def _domain_coordinate_hint(term):
    # Only a cheap candidate hint: _ranges must still validate every branch.
    while z3.is_or(term) and term.num_args():
        term = term.arg(0)
    if z3.is_and(term):
        interval = _interval(term)
        return None if interval is None else interval[0]
    if z3.is_eq(term) and term.num_args() == 2:
        pair = (_coordinate_number(term.arg(0), term.arg(1))
                or _coordinate_number(term.arg(1), term.arg(0)))
        if pair is not None:
            return pair[0]
    return None


def _excluded_values(term):
    """Recognize a single integer coordinate unequal to explicit constants."""
    if z3.is_not(term) and z3.is_eq(term.arg(0)):
        args = term.arg(0).children()
    elif z3.is_app(term) and term.decl().kind() == z3.Z3_OP_DISTINCT:
        args = term.children()
    else:
        return None
    variables = [arg for arg in args if _int_coordinate(arg)]
    if len(variables) != 1:
        return None
    coordinate = variables[0]
    constants = [arg for arg in args if not z3.eq(arg, coordinate)]
    if not constants or not all(z3.is_int_value(arg) for arg in constants):
        return None
    values = [arg.as_long() for arg in constants]
    # DISTINCT also compares the constants with one another.
    if len(values) != len(set(values)):
        return None
    return coordinate, values


def _square_avoids(values, low, high):
    for value in values:
        if value < 0:
            continue
        root = isqrt(value)
        if root * root == value and (low <= root <= high or low <= -root <= high):
            return False
    return True


def _literal_square_cover(term, coordinate, low, high):
    """Find actual disjunct witnesses, without assuming disjunct ordering.

    Binary search is only a search heuristic. Acceptance checks an original
    equality or closed integer interval for the same coordinate at every
    attainable square. Unsorted or
    mixed domains may fail to yield witnesses and then use the existing path.
    """
    if term.ctx != coordinate.ctx or low > high or not z3.is_or(term):
        return None
    size = term.num_args()
    first = 0 if low <= 0 <= high else min(abs(low), abs(high))
    last = max(abs(low), abs(high))
    if last - first + 1 > size:
        return None
    cache = {}
    def literal(index):
        if index not in cache:
            node = term.arg(index)
            value = None
            if z3.is_eq(node) and node.num_args() == 2:
                for variable, number in ((node.arg(0), node.arg(1)), (node.arg(1), node.arg(0))):
                    if z3.eq(variable, coordinate) and z3.is_int_value(number):
                        number = number.as_long()
                        value = (number, number)
                        break
            elif z3.is_and(node):
                interval = _interval(node)
                if interval is not None and z3.eq(interval[0], coordinate):
                    lower, upper = int(interval[1]), int(interval[2])
                    if lower <= upper:
                        value = (lower, upper)
            cache[index] = value
        return cache[index]
    edge_a, edge_b = literal(0), literal(size - 1)
    if edge_a is None or edge_b is None:
        return None
    ascending = edge_a[0] <= edge_b[0]
    witnesses = []
    for magnitude in range(first, last + 1):
        square, lo, hi = magnitude * magnitude, 0, size - 1
        found = None
        while lo <= hi:
            middle = (lo + hi) // 2
            value = literal(middle)
            if value is None:
                return None
            if value[0] <= square <= value[1]:
                found = middle
                break
            if (ascending and square > value[1]) or (not ascending and square < value[0]):
                lo = middle + 1
            else:
                hi = middle - 1
        if found is None:
            return None
        witnesses.append(dict(value=str(square), disjunct_index=found,
                              interval=[str(n) for n in literal(found)]))
    return witnesses


def remove_square_entailed_domains(formula, audit_callback=None):
    if not z3.is_bool(formula):
        raise ValueError("complete relation must be Boolean")
    clauses = _conjuncts(z3.simplify(formula))
    definitions, bounds = {}, {}
    for index, clause in enumerate(clauses):
        if z3.is_eq(clause) and clause.num_args() == 2:
            for output, term in ((clause.arg(0), clause.arg(1)), (clause.arg(1), clause.arg(0))):
                if (_int_coordinate(output) and z3.is_mul(term) and term.num_args() == 2
                        and _int_coordinate(term.arg(0)) and z3.eq(term.arg(0), term.arg(1))):
                    definitions.setdefault(output.get_id(), (output, term.arg(0), index))
        bound = _bound(clause)
        if bound is not None:
            coordinate, direction, value = bound
            record = bounds.setdefault(coordinate.get_id(), {})
            previous = record.get(direction)
            if previous is None or (value > previous[0] if direction == "lower" else value < previous[0]):
                record[direction] = (value, index)
    usable = {}
    protected = set()
    for key, (output, input_coordinate, index) in definitions.items():
        interval = bounds.get(input_coordinate.get_id(), {})
        if "lower" not in interval or "upper" not in interval:
            continue
        (low, low_index), (high, high_index) = interval["lower"], interval["upper"]
        if low > high:
            continue
        usable[key] = (output, input_coordinate, index, low, high, low_index, high_index)
        protected.update((index, low_index, high_index))
    kept, counts = [], dict(product_domains=0, explicit_domains=0, output_bounds=0,
                           excluded_value_domains=0, literal_square_covers=0, checked_square_values=0)
    for index, clause in enumerate(clauses):
        if index in protected:
            kept.append(clause)
            continue
        product = _product_shape(clause) if z3.is_quantifier(clause) else None
        bound = _bound(clause)
        exclusion = _excluded_values(clause)
        hint = (product[0] if product is not None else bound[0] if bound is not None
                else exclusion[0] if exclusion is not None else _domain_coordinate_hint(clause))
        definition = None if hint is None else usable.get(hint.get_id())
        if definition is None:
            kept.append(clause)
            continue
        output, input_coordinate, definition_index, low, high, low_index, high_index = definition
        method, accepted, checked, cover = None, False, 0, None
        if product is not None:
            accepted = all(a <= low and high <= b for a, b in product[1])
            method = "product_domains"
        elif bound is not None:
            _, direction, limit = bound
            squares = (low*low, high*high, 0 if low <= 0 <= high else min(low*low, high*high))
            accepted = max(squares) <= limit if direction == "upper" else min(squares) >= limit
            method = "output_bounds"
        elif exclusion is not None:
            accepted = _square_avoids(exclusion[1], low, high)
            method = "excluded_value_domains"
        else:
            cover = _literal_square_cover(clause, output, low, high)
            intervals = None if cover is not None else _ranges(clause, output)
            if cover is not None:
                accepted, checked, method = True, len(cover), "explicit_domains"
                counts['literal_square_covers'] += 1
            if intervals is not None:
                starts = [a for a, _ in intervals]
                accepted = True
                for value in range(low, high + 1):
                    square = value*value
                    position = bisect_right(starts, square) - 1
                    checked += 1
                    if position < 0 or square > intervals[position][1]:
                        accepted = False
                        break
                method = "explicit_domains"
        if not accepted:
            kept.append(clause)
            continue
        counts[method] += 1
        counts["checked_square_values"] += checked
        if audit_callback is not None:
            audit_callback(dict(removed_index=index, retained_definition_index=definition_index,
                                retained_input_bound_indices=[low_index, high_index],
                                input_interval=[low, high], method=method, checked_square_values=checked,
                                literal_square_disjuncts=cover))
    result = z3.And(*kept) if kept else z3.BoolVal(True, ctx=formula.ctx)
    return result, dict(**counts, input_conjuncts=len(clauses), retained_conjuncts=len(kept),
                        protected_premises=len(protected), square_definitions_retained=True,
                        input_bounds_retained=True, solver_queries=0)
