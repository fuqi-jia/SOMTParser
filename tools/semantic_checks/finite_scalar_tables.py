"""Exact finite Int-indexed scalar tables for structural relation matching.

A table records one arbitrary Int term, a scalar default for every other Int,
and finitely many exceptional integer keys. Composition never assumes an
input domain: guards and out-of-range values remain part of the exact table.
The size limit chooses an encoding; unsupported or larger terms stay intact.
"""
from dataclasses import dataclass
import time


@dataclass(frozen=True)
class ScalarTableNormalization:
    formula: object
    table_rewrites: int
    canonical_reorders: int
    completed: bool


@dataclass
class _Table:
    index: object
    default: object
    entries: dict
    boolean: bool


def normalize_finite_scalar_tables(formula, *, max_table_entries=256, deadline=None):
    """Normalize finite literal tables and commutative Int/Real sums exactly.

    Only Int/Bool literal-valued tables are recognized. Reassociation retains
    shared expressions if flattening would exceed 1024 operands. Array equality, symbolic
    stores, multi-domain arrays, quantifier bodies and uninterpreted operations
    are never treated as tables. A canceled traversal returns the original AST.
    All rewriting time is charged to the caller's existing absolute deadline.
    """
    import z3

    if type(max_table_entries) is not int or max_table_entries < 0:
        raise ValueError('max_table_entries must be a nonnegative integer')
    memo, arrays = {}, {}
    literals, comparisons, emitted = {}, {}, {}
    table_rewrites = reorders = 0

    def constant(raw, boolean):
        key = (boolean, raw)
        if key not in literals:
            literals[key] = (z3.BoolVal(raw, ctx=formula.ctx) if boolean
                             else z3.IntVal(raw, ctx=formula.ctx))
        return literals[key]

    def table(index, default, entries, boolean):
        entries = {key: item for key, item in entries.items() if item != default}
        return _Table(index if entries else None, default, entries, boolean)

    def membership(index, keys):
        terms = []
        index_id = index.get_id()
        for key in sorted(keys):
            identity = (index_id, key)
            if identity not in comparisons:
                # Retain the index as well as the expression: AST ids are only
                # safe cache keys while their original nodes remain alive.
                comparisons[identity] = (index, index == constant(key, False))
            terms.append(comparisons[identity][1])
        return terms[0] if len(terms) == 1 else z3.Or(*terms)

    def emit(record):
        if not record.entries:
            return constant(record.default, record.boolean)
        identity = (record.index.get_id(), record.boolean, record.default,
                    tuple(sorted(record.entries.items())))
        cached = emitted.get(identity)
        if cached is not None:
            return cached[1]
        if record.boolean:
            condition = membership(record.index, record.entries)
            result = z3.Not(condition) if record.default else condition
        else:
            groups = {}
            for key, item in record.entries.items():
                groups.setdefault(item, []).append(key)
            result = constant(record.default, False)
            for output in sorted(groups, reverse=True):
                result = z3.If(membership(record.index, groups[output]),
                               constant(output, False), result)
        emitted[identity] = (record.index, result)
        return result

    def combine(kind, records):
        if any(record is None for record in records):
            return None
        roots = {record.index.get_id(): record.index for record in records if record.index is not None}
        if len(roots) > 1:
            return None
        keys = set().union(*(record.entries for record in records))
        if len(keys) > max_table_entries:
            return None

        def apply(raw):
            if kind == z3.Z3_OP_ITE:
                return raw[1] if raw[0] else raw[2]
            if kind == z3.Z3_OP_EQ:
                result = raw[0] == raw[1]
            elif kind == z3.Z3_OP_DISTINCT:
                result = raw[0] != raw[1]
            elif kind == z3.Z3_OP_NOT:
                result = not raw[0]
            elif kind == z3.Z3_OP_AND:
                result = all(raw)
            elif kind == z3.Z3_OP_OR:
                result = any(raw)
            else:
                return None
            return result

        default = apply([record.default for record in records])
        if default is None:
            return None
        return table(next(iter(roots.values()), None), default,
                     {key: apply([record.entries.get(key, record.default) for record in records])
                      for key in keys}, records[1].boolean if kind == z3.Z3_OP_ITE else True)

    def interval(node):
        # A conjunction containing ONLY direct bounds on one Int term is a
        # finite truth table when both endpoints are known and small enough.
        root = None
        lower = upper = None
        pending = list(node.children())
        while pending:
            atom = pending.pop()
            if z3.is_and(atom):
                pending.extend(atom.children())
                continue
            if not z3.is_app(atom) or atom.num_args() != 2:
                return None
            kind = atom.decl().kind()
            if kind not in (z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT, z3.Z3_OP_EQ):
                return None
            left, right = atom.children()
            if z3.is_int_value(left) and not z3.is_int_value(right):
                left, right = right, left
                kind = {z3.Z3_OP_LE:z3.Z3_OP_GE, z3.Z3_OP_GE:z3.Z3_OP_LE,
                        z3.Z3_OP_LT:z3.Z3_OP_GT, z3.Z3_OP_GT:z3.Z3_OP_LT,
                        z3.Z3_OP_EQ:z3.Z3_OP_EQ}[kind]
            if left.sort().kind() != z3.Z3_INT_SORT or not z3.is_int_value(right):
                return None
            if root is not None and not root.eq(left):
                return None
            root = left
            bound = right.as_long()
            if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ):
                candidate = bound + (kind == z3.Z3_OP_GT)
                lower = candidate if lower is None else max(lower, candidate)
            if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_EQ):
                candidate = bound - (kind == z3.Z3_OP_LT)
                upper = candidate if upper is None else min(upper, candidate)
        if root is None or lower is None or upper is None or upper-lower+1 > max_table_entries:
            return None
        return table(root, False, {key: True for key in range(lower, upper+1)}, True)

    def materialize(entry):
        nonlocal table_rewrites
        original, result, record = entry
        if result is None:
            result = emit(record)
            entry[1] = result
            table_rewrites += not result.eq(original)
        return result

    # Preserve child frames between entry and exit. Tables stay as small exact
    # Python values until a non-table parent (or the root) needs SMT syntax.
    # In particular a union of k points does not emit k point tables and then
    # immediately rebuild those same k comparisons to emit its union.
    pending = [(formula, None)]
    visited = 0
    while pending:
        original, frame = pending.pop()
        key = original.get_id()
        if key in memo:
            continue
        visited += 1
        if visited % 32 == 1 and deadline is not None and time.monotonic() >= deadline:
            return ScalarTableNormalization(formula, 0, 0, False)
        # Keep all binders and their annotations physically intact.
        if frame is None:
            if not z3.is_app(original):
                memo[key] = [original, original, None]
                continue
            old_children = original.children()
            frame = (old_children, [child.get_id() for child in old_children], original.decl().kind())
            if old_children:
                pending.append((original, frame))
                pending.extend((child, None) for child in old_children)
                continue
        old_children, child_ids, kind = frame
        child_entries = [memo[child_id] for child_id in child_ids]
        records = [entry[2] for entry in child_entries]
        record = None
        if kind in (z3.Z3_OP_TRUE, z3.Z3_OP_FALSE):
            record = _Table(None, kind == z3.Z3_OP_TRUE, {}, True)
        elif kind == z3.Z3_OP_ANUM and z3.is_int_value(original):
            record = _Table(None, original.as_long(), {}, False)
        elif (kind in (z3.Z3_OP_NOT, z3.Z3_OP_ITE, z3.Z3_OP_AND, z3.Z3_OP_OR)
              or kind in (z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT) and len(records) == 2):
            record = combine(kind, records)
        if record is not None:
            memo[key] = [original, None, record]
            continue
        # A scalar table below an unsupported operation must still be emitted;
        # it is not dropped, approximated or restricted to an inferred domain.
        children = [materialize(entry) for entry in child_entries]
        node = original
        if any(not before.eq(after) for before, after in zip(old_children, children)):
            args = (z3.Ast * len(children))(*[child.as_ast() for child in children])
            node = z3.z3._to_expr_ref(z3.Z3_update_term(
                original.ctx_ref(), original.as_ast(), len(children), args), original.ctx)
        # Cache ground store chains once, honoring the outermost write.
        if kind == z3.Z3_OP_CONST_ARRAY and len(records) == 1 and records[0] is not None and records[0].index is None:
            if node.sort().domain().kind() == z3.Z3_INT_SORT:
                arrays[key] = (records[0].default, {}, records[0].boolean)
        elif kind == z3.Z3_OP_STORE and len(records) == 3 and records[1] is not None and records[2] is not None and records[1].index is None and records[2].index is None:
            base = arrays.get(child_ids[0])
            if base is not None:
                default, entries, boolean = base
                entries = dict(entries)
                entries[records[1].default] = records[2].default
                entries = {index:item for index,item in entries.items() if item != default}
                if len(entries) <= max_table_entries:
                    arrays[key] = (default, entries, boolean)
        elif kind == z3.Z3_OP_SELECT and len(children) == 2:
            base = arrays.get(child_ids[0])
            if base is not None:
                default, entries, boolean = base
                if records[1] is not None and records[1].index is None:
                    record = _Table(None, entries.get(records[1].default, default), {}, boolean)
                else:
                    record = table(children[1], default, entries, boolean)
        if record is None and kind == z3.Z3_OP_EQ and len(children) == 2:
            left, right = children
            if z3.is_int_value(left):
                left, right = right, left
            if left.sort().kind() == z3.Z3_INT_SORT and z3.is_int_value(right) and max_table_entries:
                record = table(left, False, {right.as_long(): True}, True)
        if record is None and kind == z3.Z3_OP_AND:
            record = interval(node)
            if record is not None:
                # A bounded guard is useful as a table when an enclosing ITE
                # or Boolean table actually composes it. Standing on its own,
                # retain its compact bounds: expanding an ordinary domain into
                # an Or of every value adds work and prevents matching the same
                # bounds written as separate assertions.
                memo[key] = [original, node, record]
                continue
        if record is not None:
            memo[key] = [original, None, record]
            continue
        else:
            result = node
            if (kind in (z3.Z3_OP_AND, z3.Z3_OP_OR)
                    or kind == z3.Z3_OP_ADD and node.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT)):
                flat = []
                work = list(children)
                while work and len(flat) <= 1024:
                    child = work.pop()
                    if z3.is_app(child) and child.decl().kind() == kind:
                        work.extend(child.children())
                    else:
                        flat.append(child)
                if work or len(flat) > 1024:
                    # A shared recurrence t[n+1] = t[n] + t[n] must not be
                    # expanded into exponentially many leaf occurrences.
                    flat = []
                else:
                    flat.sort(key=lambda child:child.get_id())
                    if kind != z3.Z3_OP_ADD:
                        flat = list({child.get_id():child for child in flat}.values())
                if flat:
                    result = (z3.Sum(*flat) if kind == z3.Z3_OP_ADD else
                              z3.And(*flat) if kind == z3.Z3_OP_AND else z3.Or(*flat))
            elif kind == z3.Z3_OP_EQ and len(children) == 2:
                result = children[0] == children[1] if children[0].get_id() <= children[1].get_id() else children[1] == children[0]
            reorders += not result.eq(node)
        memo[key] = [original, result, None]
    result = materialize(memo[formula.get_id()])
    return ScalarTableNormalization(result, table_rewrites, reorders, True)
