"""Exact compression of finite binary tables into disjoint clique families.

Only the source table's integer tuples build this optional representation.
The complete reconstructed edge set is checked before a plan is accepted.
An unsupported shape returns None and keeps the general table encoding.
"""
from itertools import combinations
import z3


def plan_clique_table(width, rows):
    if width != 2:
        return None
    pairs = set()
    for row in rows:
        if len(row) != 2:
            return None
        points = []
        for label in row:
            if label is None or len(label) != 1:
                return None
            lo, hi = label[0]
            if type(lo) is not int or type(hi) is not int or lo != hi:
                return None
            points.append(lo)
        pairs.add(tuple(points))
    if not pairs or any(a == b or (b, a) not in pairs for a, b in pairs):
        return None
    neighbors = {}
    for a, b in pairs:
        neighbors.setdefault(a, set()).add(b)
    edges = {(a, b) for a, b in pairs if a < b}
    uncovered = set(edges)
    cliques = []
    # Visit each original edge once. Repeated min(uncovered) would rescan
    # the entire edge set for every small disconnected component.
    for a, b in sorted(edges):
        if (a, b) not in uncovered:
            continue
        clique = {a, b} | (neighbors[a] & neighbors[b])
        if any(not (clique - {v}) <= neighbors[v] for v in clique):
            return None
        group = tuple(sorted(clique))
        cliques.append(group)
        uncovered.difference_update(combinations(group, 2))

    # A value may occur in two families, but never in two groups of one
    # family. Bipartite coloring establishes that property without assuming
    # the input came from a grid, rook graph, or any particular benchmark.
    memberships = {}
    for index, group in enumerate(cliques):
        for value in group:
            memberships.setdefault(value, []).append(index)
    if any(len(indices) > 2 for indices in memberships.values()):
        return None
    adjacent = [set() for _ in cliques]
    for indices in memberships.values():
        if len(indices) == 2:
            a, b = indices
            adjacent[a].add(b)
            adjacent[b].add(a)
    colors = {}
    for root in range(len(cliques)):
        if root in colors:
            continue
        colors[root] = 0
        pending = [root]
        while pending:
            a = pending.pop()
            for b in sorted(adjacent[a]):
                if b in colors:
                    if colors[b] == colors[a]:
                        return None
                else:
                    colors[b] = 1 - colors[a]
                    pending.append(b)
    families = tuple(tuple(cliques[i] for i in range(len(cliques)) if colors[i] == color)
                     for color in (0, 1))
    families = tuple(family for family in families if family)
    # This exact check is the acceptance criterion, not a hash or a sample.
    reconstructed = {(a, b) for family in families for group in family
                     for a in group for b in group if a != b}
    if reconstructed != pairs:
        return None
    # Avoid replacing small/sparse tables with a more expensive expression.
    if sum(len(group) for family in families for group in family) >= len(pairs):
        return None
    return families


def _member(value, points):
    ranges = []
    for point in points:
        if ranges and point == ranges[-1][1] + 1:
            ranges[-1] = (ranges[-1][0], point)
        else:
            ranges.append((point, point))
    return z3.Or(*[value == lo if lo == hi else z3.And(value >= lo, value <= hi)
                   for lo, hi in ranges])


class CliqueTable:
    """Bind an accepted plan without introducing functions or witnesses."""
    def __init__(self, families):
        self.families = families
        self.codes = [{} for _ in families]
        self.templates = [{} for _ in families]

    def relation(self, xs):
        if len(xs) != 2 or not all(z3.is_int(x) for x in xs):
            raise ValueError('binary integer table scope required')
        equal_codes = []
        for family, cache, templates in zip(self.families, self.codes, self.templates):
            codes = []
            for value in xs:
                key = (value.ctx_ref().value, value.get_id())
                if key not in cache:
                    context = value.ctx_ref().value
                    if context not in templates:
                        column = z3.FreshInt('source_table_class_column', ctx=value.ctx)
                        template = z3.IntVal(0, ctx=value.ctx)
                        for index, group in reversed(list(enumerate(family, 1))):
                            template = z3.If(_member(column, group), index, template)
                        templates[context] = (column, template)
                    column, template = templates[context]
                    # Binding the shared classifier in Z3 avoids repeating
                    # Python AST construction for every source variable.
                    code = z3.substitute(template, (column, value))
                    # Retain the original AST: cached identifiers cannot later
                    # be reused for a different expression by the Z3 context.
                    cache[key] = (value, code)
                original, code = cache[key]
                if not original.eq(value):
                    raise ValueError('table scope identity changed')
                codes.append(code)
            # Code 0 is outside this family, not a new equivalence class.
            equal_codes.append(z3.And(codes[0] != 0, codes[0] == codes[1]))
        return z3.And(xs[0] != xs[1], z3.Or(*equal_codes))
