"""Exact finite images of two bounded integer multiplication witnesses.

Only complete conjunctions of interval bounds and one product equation are
rewritten. The output is a public Int constant, so replacement is capture-safe
under surrounding binders. No source-domain estimate or sampled value is used.
"""
from dataclasses import dataclass
import z3


@dataclass(frozen=True)
class ProductDomainProjection:
    formula: object
    quantifiers: int = 0
    enumerated_pairs: int = 0
    distinct_values: int = 0


def _parts(root):
    todo = [root]
    while todo:
        node = todo.pop()
        if z3.is_and(node):
            todo.extend(node.children())
        else:
            yield node


def _index(node):
    if z3.is_var(node):
        index = z3.get_var_index(node)
        if index < 2:
            return index
    return None


def _number(node):
    value = z3.simplify(node)
    return value.as_long() if z3.is_int_value(value) else None


def _shape(node):
    if not (z3.is_quantifier(node) and node.is_exists() and node.num_vars() == 2
            and all(node.var_sort(i).kind() == z3.Z3_INT_SORT for i in range(2))):
        return None
    bounds = [[None, None], [None, None]]
    output = None
    for clause in _parts(node.body()):
        if not z3.is_app(clause) or clause.num_args() != 2:
            return None
        left, right = clause.children()
        kind = clause.decl().kind()
        if kind == z3.Z3_OP_EQ:
            candidates = []
            for value, term in ((left, right), (right, left)):
                if (z3.is_const(value) and value.decl().kind() == z3.Z3_OP_UNINTERPRETED
                        and value.sort().kind() == z3.Z3_INT_SORT
                        and z3.is_mul(term) and term.num_args() == 2
                        and {_index(arg) for arg in term.children()} == {0, 1}):
                    candidates.append(value)
            if len(candidates) != 1 or output is not None:
                return None
            output = candidates[0]
            continue
        if kind not in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
            return None
        if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT):
            left, right = right, left
        strict = kind in (z3.Z3_OP_LT, z3.Z3_OP_GT)
        li, ri = _index(left), _index(right)
        ln, rn = _number(left), _number(right)
        if li is not None and rn is not None:
            high = rn - int(strict)
            bounds[li][1] = high if bounds[li][1] is None else min(bounds[li][1], high)
        elif ln is not None and ri is not None:
            low = ln + int(strict)
            bounds[ri][0] = low if bounds[ri][0] is None else max(bounds[ri][0], low)
        else:
            return None
    if output is None or any(value is None for pair in bounds for value in pair):
        return None
    return output, tuple(tuple(pair) for pair in bounds)


def project_finite_product_domains(formula):
    """Enumerate every product and retain exactly its possibly nonconvex image.

    Unrecognized quantifiers remain unchanged. Original interval conjuncts are
    the sole domain authority. Consecutive products are merged into intervals
    only after the complete finite image has been constructed.
    """
    pending, seen, replacements, images = [formula], set(), [], {}
    pair_count = value_count = 0
    while pending:
        node = pending.pop()
        identity = node.get_id()
        if identity in seen:
            continue
        seen.add(identity)
        shape = _shape(node)
        if shape is not None:
            output, bounds = shape
            if bounds not in images:
                (a, b), (c, d) = bounds
                products = sorted({x * y for x in range(a, b + 1)
                                   for y in range(c, d + 1)})
                intervals = []
                for value in products:
                    if intervals and value == intervals[-1][1] + 1:
                        intervals[-1] = (intervals[-1][0], value)
                    else:
                        intervals.append((value, value))
                images[bounds] = (intervals, max(0, b - a + 1) * max(0, d - c + 1),
                                  len(products))
            intervals, pairs, count = images[bounds]
            alternatives = [output == low if low == high else z3.And(output >= low, output <= high)
                            for low, high in intervals]
            relation = z3.Or(*alternatives) if alternatives else z3.BoolVal(False, ctx=formula.ctx)
            replacements.append((node, relation))
            pair_count += pairs
            value_count += count
        else:
            pending.extend([node.body()] if z3.is_quantifier(node) else node.children())
    result = z3.substitute(formula, *replacements) if replacements else formula
    return ProductDomainProjection(result, len(replacements), pair_count, value_count)
