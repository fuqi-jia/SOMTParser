"""Exact scalarization for hidden arrays read at finitely many ground cells.

For an existentially hidden array used only through a finite set of ground
scalar reads, its interpretation can be replaced by one existential scalar
witness per distinct read. This is an exact projection rule: every array
interpretation induces those values, and every assignment to the finite cells
extends to a total array. Any unsupported use rejects the whole root group.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class FiniteArrayReadResult:
    body: object
    eliminated_roots: tuple
    retained_roots: tuple
    cell_counts: tuple
    substitutions: tuple


def _full_ground_scalar_read(z3, expression):
    """Return `(root, expression)` only for a ground scalar Select chain."""
    if expression.sort().kind() == z3.Z3_ARRAY_SORT or not z3.is_select(expression):
        return None
    current = expression
    saw_select = False
    while z3.is_select(current):
        array_expression, *indices = current.children()
        if (not indices
                or any(index.sort().kind() != z3.Z3_INT_SORT
                       or not z3.is_int_value(index) for index in indices)):
            return None
        saw_select = True
        current = array_expression
    if (not saw_select or not z3.is_const(current)
            or current.decl().kind() != z3.Z3_OP_UNINTERPRETED
            or current.sort().kind() != z3.Z3_ARRAY_SORT):
        return None
    return current, expression


def _collect_ground_scalar_reads(z3, body, eligible_root_ids):
    """Collect ground scalar Select chains in one DAG traversal."""
    cells_by_root = {root_id: {} for root_id in eligible_root_ids}
    stack = [body]
    visited = set()
    while stack:
        node = stack.pop()
        if node.get_id() in visited:
            continue
        visited.add(node.get_id())
        if z3.is_quantifier(node):
            stack.append(node.body())
            continue
        if z3.is_select(node):
            ground_read = _full_ground_scalar_read(z3, node)
            if ground_read is not None:
                root, cell = ground_read
                if root.get_id() in cells_by_root:
                    cells_by_root[root.get_id()].setdefault(cell.get_id(), cell)
        if z3.is_app(node):
            stack.extend(node.children())
    return cells_by_root


def scalarize_finite_array_reads(body, eligible_roots, visible_roots=()):
    """Replace safe hidden roots with fresh scalar witnesses conservatively.

    The caller supplies hidden roots as `eligible_roots`; roots explicitly
    listed in `visible_roots` are protected even if also listed as eligible.
    A root commits only if all uses are complete scalar Select chains at
    concrete Int numerals and simultaneous substitution removes it from the
    full relation. Fixed indices outside any nominal shape are still retained
    as distinct cells; dynamic/out-of-range expressions are never discarded.
    """
    import z3

    from .projection import contains_quantifier, free_constants

    if not z3.is_bool(body):
        raise ValueError("finite array-read scalarization requires a Boolean body")
    roots = {}
    visible = {}
    for root in list(eligible_roots) + list(visible_roots):
        if (not z3.is_const(root)
                or root.decl().kind() != z3.Z3_OP_UNINTERPRETED
                or root.sort().kind() != z3.Z3_ARRAY_SORT):
            raise ValueError("eligible roots must be uninterpreted array constants")
    for root in visible_roots:
        visible[root.get_id()] = root
    for root in eligible_roots:
        roots[root.get_id()] = root

    current = body
    eliminated = []
    retained = []
    counts = {}
    committed_substitutions = []
    present_root_ids = {constant.get_id() for constant in free_constants([body])
                        if constant.sort().kind() == z3.Z3_ARRAY_SORT}
    visible_retained = [str(root.decl().name()) for root_id, root in visible.items()
                        if root_id in present_root_ids]
    roots = {root_id: root for root_id, root in roots.items()
             if root_id in present_root_ids and root_id not in visible}
    if roots and contains_quantifier(body):
        return FiniteArrayReadResult(
            body, (), tuple(visible_retained +
                            [str(root.decl().name()) for root in roots.values()]),
            (), ())
    retained.extend(visible_retained)
    cells_by_root = _collect_ground_scalar_reads(z3, body, set(roots))
    for root_id, root in roots.items():
        cells = cells_by_root[root_id]
        if not cells:
            retained.append(str(root.decl().name()))
            continue
        substitutions = []
        for index, cell in enumerate(cells.values()):
            if cell.sort().kind() == z3.Z3_ARRAY_SORT:
                # Defensive: _full_ground_scalar_read already rules this out.
                substitutions = []
                break
            witness = z3.FreshConst(
                cell.sort(), f"finite_array_cell_{root.decl().name()}_{index}")
            substitutions.append((cell, witness))
        if not substitutions:
            retained.append(str(root.decl().name()))
            continue
        candidate = z3.substitute(current, *substitutions)
        remaining_ids = {constant.get_id() for constant in free_constants([candidate])
                         if constant.sort().kind() == z3.Z3_ARRAY_SORT}
        if root_id in remaining_ids:
            retained.append(str(root.decl().name()))
            continue
        current = candidate
        eliminated.append(str(root.decl().name()))
        counts[str(root.decl().name())] = len(substitutions)
        committed_substitutions.extend(substitutions)

    return FiniteArrayReadResult(
        current, tuple(eliminated), tuple(retained), tuple(sorted(counts.items())),
        tuple(committed_substitutions))
