"""Share a finite extension for bounded reads of an observed array.

Bounds come from mandatory conjuncts of the complete SMT formula, never from
array shapes or provider metadata. Only scalar constants and concrete array
cells can supply index bounds: these terms and their guard atoms cannot be
changed by this rewrite. Thus the original guards remain in both formulas,
and reading the finite extension is equivalent in both directions. One
extension is shared by all eligible reads of a root, avoiding a separate
cell-by-cell expansion at each access.
"""
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class BoundedReadExpansion:
    formula: object
    expanded_reads: int = 0
    expanded_cells: int = 0
    materialized_cells: int = 0


def expand_bounded_observed_reads(formula, observable_bridges):
    """Replace eligible scalar reads with reads of a shared finite extension.

    Every possible coordinate must already occur in an observation bridge.
    Missing bounds, missing coordinates, quantified contexts and unsupported
    index expressions do not license expansion. Observing an array-valued
    prefix supplies no scalar cells.
    This function adds no constraints and does not restrict an array's domain.
    """
    import z3

    def chain(term):
        if term.sort().kind() == z3.Z3_ARRAY_SORT or not z3.is_select(term):
            return None
        indices = []
        root = term
        while z3.is_select(root):
            if root.num_args() != 2 or not z3.is_int(root.arg(1)):
                return None
            indices.append(root.arg(1))
            root = root.arg(0)
        if not z3.is_const(root) or root.decl().kind() != z3.Z3_OP_UNINTERPRETED:
            return None
        return root, tuple(reversed(indices))

    def stable(term):
        if not z3.is_int(term):
            return False
        if z3.is_const(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            return True
        parts = chain(term)
        return parts is not None and all(z3.is_int_value(i) for i in parts[1])

    cells = {}
    for _, term in observable_bridges:
        parts = chain(term)
        if parts is not None and all(z3.is_int_value(i) for i in parts[1]):
            root, indices = parts
            cells.setdefault(root.get_id(), {})[tuple(i.as_long() for i in indices)] = term
    if not cells:
        return BoundedReadExpansion(formula)

    # Keep references alive while AST ids are used as keys.
    bounds = {}
    stack = [formula]
    while stack:
        atom = stack.pop()
        if z3.is_and(atom):
            stack.extend(atom.children())
            continue
        if not z3.is_app(atom) or atom.num_args() != 2:
            continue
        kind = atom.decl().kind()
        if kind not in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ):
            continue
        left, right = atom.children()
        if z3.is_int_value(left) and stable(right):
            left, right = right, left
            kind = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
                    z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT,
                    z3.Z3_OP_EQ: z3.Z3_OP_EQ}[kind]
        if not stable(left) or not z3.is_int_value(right):
            continue
        record = bounds.setdefault(left.get_id(), [left, None, None])
        number = right.as_long()
        if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ):
            lower = number + (kind == z3.Z3_OP_GT)
            record[1] = lower if record[1] is None else max(record[1], lower)
        if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_EQ):
            upper = number - (kind == z3.Z3_OP_LT)
            record[2] = upper if record[2] is None else min(record[2], upper)
    if not bounds:
        return BoundedReadExpansion(formula)

    substitutions = []
    seen = set()
    stack = [formula]
    expanded_cells = 0
    coverage = {}
    extensions = {}
    materialized_cells = 0

    def extension(observed, rank):
        # A total array can extend its finite observed tuple arbitrarily.
        # Reuse an existing scalar as default rather than introducing a fresh
        # hidden symbol. Only proved-covered reads use this extension.
        defaults = [None] * (rank + 1)
        defaults[rank] = next(iter(observed.values()))
        for depth in range(rank - 1, -1, -1):
            defaults[depth] = z3.K(z3.IntSort(ctx=formula.ctx), defaults[depth + 1])
        trie = {}
        for coordinates, cell in observed.items():
            node = trie
            for coordinate in coordinates[:-1]:
                node = node.setdefault(coordinate, {})
            node[coordinates[-1]] = cell
        # Iterative postorder also handles high-rank arrays without Python
        # recursion. Shared prefixes produce a single row/table node.
        pending = [(trie, 0, False)]
        tables = {}
        while pending:
            node, depth, ready = pending.pop()
            if not ready and depth + 1 < rank:
                pending.append((node, depth, True))
                pending.extend((child, depth + 1, False) for child in node.values())
                continue
            result = defaults[depth]
            for coordinate, child in sorted(node.items()):
                value = child if depth + 1 == rank else tables[id(child)]
                result = z3.Store(result, coordinate, value)
            tables[id(node)] = result
        return tables[id(trie)]

    while stack:
        term = stack.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if z3.is_quantifier(term):
            # Do not apply an outer bound below a binder, even accidentally.
            return BoundedReadExpansion(formula)
        if not z3.is_app(term):
            continue
        stack.extend(term.children())
        parts = chain(term)
        if parts is None:
            continue
        root, indices = parts
        observed = cells.get(root.get_id())
        if observed is None or all(z3.is_int_value(i) for i in indices):
            continue
        ranges = []
        count = 1
        for index in indices:
            if z3.is_int_value(index):
                lower = upper = index.as_long()
            else:
                record = bounds.get(index.get_id())
                if record is None:
                    break
                _, lower, upper = record
                if lower is None or upper is None or lower > upper:
                    break
            count *= upper - lower + 1
            # A complete rectangle cannot have more cells than its supplied
            # observation map. This is a coverage condition, not a quota.
            if count > len(observed):
                break
            ranges.append(range(lower, upper + 1))
        if len(ranges) != len(indices):
            continue
        coverage_key = (root.get_id(), tuple((r.start, r.stop) for r in ranges))
        if coverage_key not in coverage:
            coverage[coverage_key] = all(tuple(coordinate) in observed
                                         for coordinate in product(*ranges))
        if not coverage[coverage_key]:
            continue
        if root.get_id() not in extensions:
            extensions[root.get_id()] = extension(observed, len(indices))
            materialized_cells += len(observed)
        replacement = extensions[root.get_id()]
        for index in indices:
            replacement = z3.Select(replacement, index)
        substitutions.append((term, replacement))
        expanded_cells += count
    rewritten = z3.substitute(formula, *substitutions) if substitutions else formula
    return BoundedReadExpansion(rewritten, len(substitutions), expanded_cells,
                                materialized_cells)
