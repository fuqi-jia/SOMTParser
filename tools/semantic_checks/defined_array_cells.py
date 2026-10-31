"""Exact projection of arrays with concrete cell definitions.

Call only after finite quantifier expansion. A root is eligible only when its
caller has classified it as hidden auxiliary state, never as an observable or
cost coordinate. The helper accepts only unconditional top-level conjunct
equalities defining full scalar Select chains at concrete Int indices.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class ArrayCellElimination:
    body: object
    eliminated_roots: tuple
    retained_roots: tuple
    definition_counts: tuple


def _top_level_conjuncts(z3, expression):
    stack, result, seen = [expression], [], set()
    while stack:
        node = stack.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_and(node):
            stack.extend(reversed(node.children()))
        else:
            result.append(node)
    return result


def _concrete_scalar_select(z3, expression):
    """Return `(array_root, scalar_select, concrete_index_tuple)` if exact."""
    if expression.sort().kind() == z3.Z3_ARRAY_SORT:
        return None
    current = expression
    reversed_indices = []
    while z3.is_select(current):
        children = current.children()
        if len(children) != 2:
            return None
        array_expression, index_expression = children
        if not z3.is_int_value(index_expression):
            return None
        reversed_indices.append((str(index_expression.sort()),
                                 index_expression.as_long()))
        current = array_expression
    if (not reversed_indices or not z3.is_const(current)
            or current.decl().kind() != z3.Z3_OP_UNINTERPRETED
            or current.sort().kind() != z3.Z3_ARRAY_SORT):
        return None
    return current, expression, tuple(reversed(reversed_indices))


def _contains_root(z3, expression, root_id):
    from tools.semantic_checks.projection import free_constants
    return any(constant.get_id() == root_id
               for constant in free_constants([expression]))


def eliminate_defined_array_cells(body, eligible_roots):
    """Replace proven concrete array cells, rolling back incomplete groups.

    For each caller-authorized hidden root, find top-level equalities of the
    form `Select(root, numerals...) == rhs` (or the reverse). The RHS must not
    contain that root. The first RHS for a concrete cell is used as its
    representative; every equality remains in the body, so duplicate
    definitions continue to impose their equality constraints after
    substitution. A root group commits only when simultaneous substitution
    removes the root from the entire current body.

    Re-scanning the current body after every successful group lets an
    acyclic dependency become eligible after its prerequisite root is
    eliminated. Any group that cannot remove its full root is rolled back.
    Unsupported symbolic reads, array prefixes, whole-array uses, or
    self-dependent RHSs therefore remain untouched.
    """
    import z3

    from .projection import contains_quantifier
    if contains_quantifier(body):
        raise ValueError('array cell elimination requires a quantifier-free body')

    roots = {}
    for root in eligible_roots:
        if (not z3.is_const(root)
                or root.decl().kind() != z3.Z3_OP_UNINTERPRETED
                or root.sort().kind() != z3.Z3_ARRAY_SORT):
            raise ValueError("eligible roots must be array constants")
        roots[root.get_id()] = root

    current = body
    remaining = dict(roots)
    eliminated = []
    definition_counts = {}

    while remaining:
        progress = False
        for root_id, root in list(remaining.items()):
            if not _contains_root(z3, current, root_id):
                eliminated.append(str(root.decl().name()))
                definition_counts[str(root.decl().name())] = 0
                del remaining[root_id]
                progress = True
                continue

            cells = {}
            unsafe_definition = False
            for conjunct in _top_level_conjuncts(z3, current):
                if (not z3.is_app(conjunct)
                        or conjunct.decl().kind() != z3.Z3_OP_EQ
                        or conjunct.num_args() != 2):
                    continue
                left, right = conjunct.children()
                left_select = _concrete_scalar_select(z3, left)
                right_select = _concrete_scalar_select(z3, right)
                oriented = None
                if left_select is not None and left_select[0].get_id() == root_id:
                    oriented = (left_select, right)
                elif (right_select is not None
                      and right_select[0].get_id() == root_id):
                    oriented = (right_select, left)
                if oriented is None:
                    continue
                select_info, replacement = oriented
                if _contains_root(z3, replacement, root_id):
                    unsafe_definition = True
                    continue
                _cell_root, cell_expression, index_tuple = select_info
                cells.setdefault(index_tuple, (cell_expression, replacement))

            if unsafe_definition or not cells:
                continue

            substitutions = [pair for pair in cells.values()]
            candidate = z3.substitute(current, *substitutions)
            if _contains_root(z3, candidate, root_id):
                continue

            # Commit only after the root-disappearance check. Definitions are
            # intentionally not removed; they become tautologies or preserve
            # consistency constraints for duplicate cell definitions.
            current = candidate
            eliminated.append(str(root.decl().name()))
            definition_counts[str(root.decl().name())] = len(cells)
            del remaining[root_id]
            progress = True
        if not progress:
            break

    retained = tuple(str(root.decl().name()) for root in remaining.values())
    return ArrayCellElimination(
        current, tuple(eliminated), retained,
        tuple(sorted(definition_counts.items())))
