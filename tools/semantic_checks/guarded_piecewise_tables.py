"""Exact finite-domain table normalization with the original guards retained.

Only positive top-level clauses of the form ``Or(index == integer, ...)``
supply a domain. Holes and every original domain clause remain in the output.
Values outside that domain may change, so callers must use the complete
returned formula, never extract a rewritten subexpression as an identity.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class GuardedPiecewiseNormalization:
    formula: object
    domain_count: int
    retained_domain_indices: tuple
    table_rewrites: int
    combined_tables: int
    visited_nodes: int


def normalize_guarded_piecewise_tables(formula, audit_callback=None):
    """Normalize single-index Int/Bool tables, making no solver queries.

    Domain premises are exact, unconditional finite disjunctions. Intersecting
    several such premises is safe because all of them are kept unchanged.
    Quantifier bodies are opaque; unsupported operations retain rewritten
    children. The full-domain integer-piecewise API is independent of this one.
    """
    import z3

    conjuncts, pending, seen = [], [formula], set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_and(node):
            pending.extend(reversed(node.children()))
        else:
            conjuncts.append(node)

    domains, retained = {}, []
    for position, clause in enumerate(conjuncts):
        atoms = clause.children() if z3.is_or(clause) else [clause]
        index, points = None, set()
        for atom in atoms:
            if not z3.is_eq(atom):
                break
            left, right = atom.children()
            if z3.is_int_value(left):
                left, right = right, left
            if (left.sort().kind() != z3.Z3_INT_SORT or
                    z3.is_int_value(left) or not z3.is_int_value(right)):
                break
            if index is not None and not index.eq(left):
                break
            index = left
            points.add(right.as_long())
        else:
            if index is None:
                continue
            key = index.get_id()
            if key in domains:
                domains[key][1].intersection_update(points)
                domains[key][2].append(position)
            else:
                domains[key] = [index, points, [position]]
            retained.append(position)
    # Contradictory domains are preserved rather than used to justify arbitrary
    # rewrites. Retaining all input clauses also retains their contradiction.
    domains = {key: (row[0], tuple(sorted(row[1])), tuple(row[2]))
               for key, row in domains.items() if row[1]}
    if not domains:
        return GuardedPiecewiseNormalization(formula, 0, tuple(retained), 0, 0, 0)
    if audit_callback is not None:
        for index, values, positions in domains.values():
            audit_callback(dict(index=index.sexpr(), values=list(values),
                                retained_domain_indices=list(positions)))

    memo, emitted, literals = {}, {}, {}
    rewrites = combined = 0

    def literal(value, boolean):
        key = (boolean, value)
        if key not in literals:
            literals[key] = (z3.BoolVal(value, ctx=formula.ctx) if boolean
                             else z3.IntVal(value, ctx=formula.ctx))
        return literals[key]

    def emit(record):
        index, values, boolean = record
        if index is None or all(value == values[0] for value in values):
            return literal(values[0], boolean)
        cache_key = (index.get_id(), values, boolean)
        if cache_key in emitted:
            return emitted[cache_key][1]
        # The default is attained at the smallest legal index. Both infinite
        # tails and domain holes receive that same attained value; no invented
        # zero can widen a subsequent exact interval proof.
        default, events = values[0], {}
        for point, value in zip(domains[index.get_id()][1], values):
            if value != default:
                events[point] = value
                events[point + 1] = default
        cuts, regions = [], [default]
        for point, value in sorted(events.items()):
            if value != regions[-1]:
                cuts.append(point)
                regions.append(value)

        def build(lo, hi):
            if lo == hi:
                return literal(regions[lo], boolean)
            middle = (lo + hi) // 2
            return z3.If(index < literal(cuts[middle], False),
                         build(lo, middle), build(middle + 1, hi))

        result = build(0, len(cuts))
        emitted[cache_key] = (index, result)
        return result

    def materialize(entry):
        nonlocal rewrites
        if entry[1] is None:
            entry[1] = emit(entry[2])
            rewrites += not entry[0].eq(entry[1])
        return entry[1]

    operations = {
        z3.Z3_OP_ITE: lambda a: a[1] if a[0] else a[2],
        z3.Z3_OP_EQ: lambda a: a[0] == a[1],
        z3.Z3_OP_DISTINCT: lambda a: len(set(a)) == len(a),
        z3.Z3_OP_NOT: lambda a: not a[0],
        z3.Z3_OP_AND: all,
        z3.Z3_OP_OR: any,
        z3.Z3_OP_IMPLIES: lambda a: not a[0] or a[1],
        z3.Z3_OP_XOR: lambda a: a[0] != a[1],
        z3.Z3_OP_LE: lambda a: a[0] <= a[1],
        z3.Z3_OP_GE: lambda a: a[0] >= a[1],
        z3.Z3_OP_LT: lambda a: a[0] < a[1],
        z3.Z3_OP_GT: lambda a: a[0] > a[1],
        z3.Z3_OP_ADD: sum,
        z3.Z3_OP_SUB: lambda a: a[0] - sum(a[1:]),
        z3.Z3_OP_UMINUS: lambda a: -a[0],
    }

    def multiply(args):
        result = 1
        for value in args:
            result *= value
        return result

    operations[z3.Z3_OP_MUL] = multiply

    def combine(node, entries):
        nonlocal combined
        operation = operations.get(node.decl().kind())
        records = [entry[2] for entry in entries]
        if operation is None or any(record is None for record in records):
            return None
        roots = {record[0].get_id(): record[0] for record in records
                 if record[0] is not None}
        if len(roots) > 1:
            return None
        index = next(iter(roots.values()), None)
        size = len(domains[index.get_id()][1]) if index is not None else 1
        values = tuple(operation([record[1][i if record[0] is not None else 0]
                                  for record in records]) for i in range(size))
        combined += 1
        return index, values, z3.is_bool(node)

    retained_set = set(retained)
    pending = [(node, False) for i, node in enumerate(conjuncts)
               if i not in retained_set]
    while pending:
        node, ready = pending.pop()
        key = node.get_id()
        if key in memo:
            continue
        if key in domains:
            # Keep a bare index intact; its finite values are used only when
            # evaluating a supported parent table.
            memo[key] = [node, node, (node, domains[key][1], False)]
            continue
        if not z3.is_app(node):
            memo[key] = [node, node, None]
            continue
        children = node.children()
        if children and not ready:
            pending.append((node, True))
            pending.extend((child, False) for child in children)
            continue
        if z3.is_int_value(node):
            record = (None, (node.as_long(),), False)
        elif z3.is_true(node) or z3.is_false(node):
            record = (None, (z3.is_true(node),), True)
        else:
            entries = [memo[child.get_id()] for child in children]
            record = combine(node, entries)
            if record is None:
                rewritten = [materialize(entry) for entry in entries]
                result = (node if all(a.eq(b) for a, b in zip(children, rewritten))
                          else node.decl()(*rewritten))
                memo[key] = [node, result, None]
                continue
        memo[key] = [node, None, record]
    result = z3.And(*[node if i in retained_set else materialize(memo[node.get_id()])
                       for i, node in enumerate(conjuncts)])
    return GuardedPiecewiseNormalization(result, len(domains), tuple(retained),
                                         rewrites, combined, len(memo))
