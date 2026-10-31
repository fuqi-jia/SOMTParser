"""Exact constant-valued functions of one integer term over the whole Int domain.

Unlike finite point tables, these tables retain separate negative and positive
infinite tails. No surrounding domain assertion is assumed or removed. Bound
expressions, unsupported operations and functions of multiple indices remain
intact; eligible children can still be normalized independently.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class PiecewiseTableNormalization:
    formula: object
    table_rewrites: int
    combined_tables: int
    emitted_regions: int
    visited_nodes: int


@dataclass(frozen=True)
class _Table:
    index: object
    cuts: tuple
    values: tuple
    boolean: bool


def normalize_integer_piecewise_tables(formula):
    """Canonicalize literal-valued Int-indexed ITEs without any solver query.

    A cut k starts a new region at k. Values cover (-infinity, first cut),
    every half-open interval between cuts, and [last cut, +infinity). Adjacent
    equal values are merged and the result is emitted as a balanced ITE tree.
    The traversal preserves DAG sharing and does not enter quantifier bodies.
    """
    import bisect
    import z3

    memo, emitted, literals = {}, {}, {}
    table_rewrites = combined_tables = emitted_regions = 0

    def literal(value, boolean):
        key = (boolean, value)
        if key not in literals:
            literals[key] = (z3.BoolVal(value, ctx=formula.ctx) if boolean
                             else z3.IntVal(value, ctx=formula.ctx))
        return literals[key]

    def table(index, cuts, values, boolean):
        kept_cuts, kept_values = [], [values[0]]
        for cut, value in zip(cuts, values[1:]):
            if value != kept_values[-1]:
                kept_cuts.append(cut)
                kept_values.append(value)
        return _Table(index if kept_cuts else None, tuple(kept_cuts),
                      tuple(kept_values), boolean)

    def emit(record):
        nonlocal emitted_regions
        if record.index is None:
            return literal(record.values[0], record.boolean)
        identity = (record.index.get_id(), record.cuts, record.values, record.boolean)
        if identity in emitted:
            return emitted[identity][1]

        def build(lo, hi):
            if lo == hi:
                return literal(record.values[lo], record.boolean)
            middle = (lo + hi) // 2
            return z3.If(record.index < literal(record.cuts[middle], False),
                         build(lo, middle), build(middle + 1, hi))

        result = build(0, len(record.cuts))
        # Keep the index alive whenever its AST id is used as a cache key.
        emitted[identity] = (record.index, result)
        emitted_regions += len(record.values)
        return result

    def materialize(entry):
        nonlocal table_rewrites
        if entry[1] is None:
            entry[1] = emit(entry[2])
            table_rewrites += not entry[1].eq(entry[0])
        return entry[1]

    def apply(kind, args):
        if kind == z3.Z3_OP_ITE:
            return args[1] if args[0] else args[2]
        if kind == z3.Z3_OP_EQ:
            return args[0] == args[1]
        if kind == z3.Z3_OP_DISTINCT:
            return len(set(args)) == len(args)
        if kind == z3.Z3_OP_NOT:
            return not args[0]
        if kind == z3.Z3_OP_AND:
            return all(args)
        if kind == z3.Z3_OP_OR:
            return any(args)
        if kind == z3.Z3_OP_IMPLIES:
            return not args[0] or args[1]
        if kind == z3.Z3_OP_XOR:
            return args[0] != args[1]
        if kind == z3.Z3_OP_LE:
            return args[0] <= args[1]
        if kind == z3.Z3_OP_GE:
            return args[0] >= args[1]
        if kind == z3.Z3_OP_LT:
            return args[0] < args[1]
        if kind == z3.Z3_OP_GT:
            return args[0] > args[1]
        if kind == z3.Z3_OP_ADD:
            return sum(args)
        if kind == z3.Z3_OP_UMINUS:
            return -args[0]
        if kind == z3.Z3_OP_SUB:
            return args[0] - sum(args[1:])
        if kind == z3.Z3_OP_MUL:
            value = 1
            for arg in args:
                value *= arg
            return value
        raise AssertionError('unsupported table operation')

    supported = {z3.Z3_OP_ITE, z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT, z3.Z3_OP_NOT,
                 z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_IMPLIES, z3.Z3_OP_XOR,
                 z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT,
                 z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL}

    def combine(kind, records, boolean):
        nonlocal combined_tables
        if kind not in supported or any(record is None for record in records):
            return None
        roots = {record.index.get_id(): record.index for record in records
                 if record.index is not None}
        if len(roots) > 1:
            return None
        cuts = sorted({cut for record in records for cut in record.cuts})
        values = [apply(kind, [record.values[0] for record in records])]
        for cut in cuts:
            values.append(apply(kind, [record.values[bisect.bisect_right(record.cuts, cut)]
                                       for record in records]))
        combined_tables += 1
        return table(next(iter(roots.values()), None), cuts, values, boolean)

    reverse = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_GE: z3.Z3_OP_LE,
               z3.Z3_OP_LT: z3.Z3_OP_GT, z3.Z3_OP_GT: z3.Z3_OP_LT,
               z3.Z3_OP_EQ: z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT: z3.Z3_OP_DISTINCT}

    def comparison(node):
        if node.num_args() != 2 or node.decl().kind() not in reverse:
            return None
        kind = node.decl().kind()
        left, right = node.children()
        if z3.is_int_value(left):
            left, right = right, left
            kind = reverse[kind]
        if left.sort().kind() != z3.Z3_INT_SORT or not z3.is_int_value(right):
            return None
        n = right.as_long()
        if kind == z3.Z3_OP_LE:
            return table(left, [n + 1], [True, False], True)
        if kind == z3.Z3_OP_LT:
            return table(left, [n], [True, False], True)
        if kind == z3.Z3_OP_GE:
            return table(left, [n], [False, True], True)
        if kind == z3.Z3_OP_GT:
            return table(left, [n + 1], [False, True], True)
        values = [False, True, False] if kind == z3.Z3_OP_EQ else [True, False, True]
        return table(left, [n, n + 1], values, True)

    pending = [(formula, False)]
    while pending:
        original, ready = pending.pop()
        key = original.get_id()
        if key in memo:
            continue
        if not z3.is_app(original):
            memo[key] = [original, original, None]
            continue
        children = list(original.children())
        if children and not ready:
            pending.append((original, True))
            pending.extend((child, False) for child in children)
            continue
        kind = original.decl().kind()
        if z3.is_true(original) or z3.is_false(original):
            record = table(None, [], [z3.is_true(original)], True)
        elif z3.is_int_value(original):
            record = table(None, [], [original.as_long()], False)
        else:
            entries = [memo[child.get_id()] for child in children]
            record = combine(kind, [entry[2] for entry in entries], z3.is_bool(original))
            if record is None:
                rewritten = [materialize(entry) for entry in entries]
                node = (original if all(old.eq(new) for old, new in zip(children, rewritten))
                        else original.decl()(*rewritten))
                record = comparison(node)
                if record is None:
                    memo[key] = [original, node, None]
                    continue
        memo[key] = [original, None, record]
    return PiecewiseTableNormalization(materialize(memo[formula.get_id()]),
                                       table_rewrites, combined_tables,
                                       emitted_regions, len(memo))
