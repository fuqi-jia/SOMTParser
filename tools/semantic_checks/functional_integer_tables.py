"""Exact literal table relation using a functional dependent first column.

For each key tuple k, the input rows must give exactly one value v. The
relation is then key-membership(k) AND first-column = value(k). A finite
membership guard rejects every absent key, independently of the total value
array's default. Nonfunctional tables return None for the general encoding.
No source-variable domain, target formula or target-private name is used.
"""
from collections import Counter
from math import prod
import z3


def _membership(term, values):
    runs = []
    for value in sorted(values):
        if runs and value == runs[-1][1] + 1:
            runs[-1] = (runs[-1][0], value)
        else:
            runs.append((value, value))
    return z3.Or(*[term == lo if lo == hi else z3.And(term >= lo, term <= hi)
                   for lo, hi in runs])


def functional_integer_table_relation(scope, flat_values):
    """Return the complete relation, or None when first-column dependence fails."""
    width = len(scope)
    if not width or len(flat_values) % width:
        raise ValueError('integer table width')
    if any(type(value) is not int for value in flat_values):
        raise ValueError('integer table literal sort')
    if any(not z3.is_int(term) for term in scope):
        raise ValueError('integer table scope sort')
    if not flat_values:
        return z3.BoolVal(False)
    if width > 64:
        return None
    values_by_key = {}
    coordinates = [set() for _ in scope[1:]]
    for offset in range(0, len(flat_values), width):
        key = tuple(flat_values[offset + 1:offset + width])
        value = flat_values[offset]
        if key in values_by_key and values_by_key[key] != value:
            return None
        values_by_key[key] = value
        for domain, coordinate in zip(coordinates, key):
            domain.add(coordinate)
    if width == 1:
        return scope[0] == values_by_key[()]

    # Equality of cardinalities proves that these unique keys cover the whole
    # Cartesian product of their projections. Holes inside a coordinate set
    # remain explicit membership holes; no interval completion is assumed.
    rectangular = len(values_by_key) == prod(map(len, coordinates))
    tree = {}
    for key, value in values_by_key.items():
        node = tree
        for coordinate in key[:-1]:
            node = node.setdefault(coordinate, {})
        node[key[-1]] = value
    literals = {}

    def literal(value):
        if value not in literals:
            literals[value] = z3.IntVal(value)
        return literals[value]

    def build(node, level):
        children = []
        for coordinate, item in sorted(node.items()):
            if level == width - 2:
                value, support = literal(item), z3.BoolVal(True)
            else:
                value, support = build(item, level + 1)
            children.append((coordinate, value, support))
        # The default affects only representation: a separate exact key guard
        # determines where a value may participate in the table relation.
        frequency = Counter(value.get_id() for _, value, _ in children)
        selected = max(frequency, key=frequency.get)
        default = next(value for _, value, _ in children if value.get_id() == selected)
        value_array = z3.K(z3.IntSort(), default)
        for coordinate, value, _ in children:
            if not value.eq(default):
                value_array = z3.Store(value_array, coordinate, value)
        if rectangular:
            return value_array, None
        missing = z3.BoolVal(False)
        for _ in range(width - 2 - level):
            missing = z3.K(z3.IntSort(), missing)
        support_array = z3.K(z3.IntSort(), missing)
        for coordinate, _, support in children:
            support_array = z3.Store(support_array, coordinate, support)
        return value_array, support_array

    value, support = build(tree, 0)
    for term in scope[1:]:
        value = z3.Select(value, term)
        if support is not None:
            support = z3.Select(support, term)
    if rectangular:
        support = z3.And(*[_membership(term, domain)
                           for term, domain in zip(scope[1:], coordinates)])
    return z3.And(support, scope[0] == value)
