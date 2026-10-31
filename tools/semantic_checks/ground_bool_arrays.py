"""Exact normalization of ground Int-to-Bool arrays, including cofinite sets.

A value is its Boolean default plus every exceptional integer coordinate.
Unknown arrays, symbolic stores and unknown map functions remain untouched.
This is a local rewriting utility; it supplies no model or optimality claim.
"""
import z3


def simplify_ground_bool_arrays(expression):
    """Normalize supported ground arrays and exact extensional comparisons."""
    rewritten, values = {}, {}
    stack = [(expression, False)]

    def boolean_array(term):
        sort = term.sort()
        return (sort.kind() == z3.Z3_ARRAY_SORT
                and sort.domain().kind() == z3.Z3_INT_SORT
                and sort.range().kind() == z3.Z3_BOOL_SORT)

    def literal_boolean(term):
        if z3.is_true(term):
            return True
        if z3.is_false(term):
            return False
        return None

    def canonical(value, sort):
        default, entries = value
        result = z3.K(sort.domain(), z3.BoolVal(default, ctx=sort.ctx))
        for index, present in sorted(entries.items()):
            result = z3.Store(result, z3.IntVal(index, ctx=sort.ctx),
                              z3.BoolVal(present, ctx=sort.ctx))
        return result

    def ground_value(root):
        pending = [(root, False)]
        descriptions = {}
        while pending:
            node, ready = pending.pop()
            key = node.get_id()
            if key in values:
                continue
            if not ready:
                if not boolean_array(node) or not z3.is_app(node):
                    values[key] = None
                    continue
                if z3.is_const_array(node):
                    base = literal_boolean(node.arg(0))
                    values[key] = None if base is None else (base, {})
                    continue
                if z3.is_store(node):
                    # Peel an entire Store chain once. Outer stores are the
                    # last writes and override every inner write at that key.
                    base, writes, valid = node, {}, True
                    while z3.is_store(base):
                        index, present = base.arg(1), literal_boolean(base.arg(2))
                        if not z3.is_int_value(index) or present is None:
                            valid = False
                            break
                        writes.setdefault(index.as_long(), present)
                        base = base.arg(0)
                    if not valid:
                        values[key] = None
                        continue
                    descriptions[key] = ('store', [base], writes)
                elif node.decl().kind() == z3.Z3_OP_ARRAY_MAP:
                    function = z3.get_map_func(node)
                    if (function.kind() == z3.Z3_OP_UNINTERPRETED
                            or function.range().kind() != z3.Z3_BOOL_SORT
                            or any(function.domain(i).kind() != z3.Z3_BOOL_SORT
                                   for i in range(function.arity()))):
                        values[key] = None
                        continue
                    descriptions[key] = ('map', node.children(), function)
                elif z3.is_app_of(node, z3.Z3_OP_ITE):
                    condition = literal_boolean(node.arg(0))
                    if condition is None:
                        values[key] = None
                        continue
                    descriptions[key] = ('ite', [node.arg(1 if condition else 2)], None)
                else:
                    values[key] = None
                    continue
                pending.append((node, True))
                pending.extend((child, False) for child in descriptions[key][1]
                               if child.get_id() not in values)
                continue
            kind, dependencies, extra = descriptions.pop(key)
            inputs = [values[child.get_id()] for child in dependencies]
            if any(v is None for v in inputs):
                values[key] = None
                continue
            if kind == 'ite':
                values[key] = inputs[0]
            elif kind == 'store':
                default, entries = inputs[0]
                entries = dict(entries)
                for index, present in extra.items():
                    if present == default:
                        entries.pop(index, None)
                    else:
                        entries[index] = present
                values[key] = (default, entries)
            else:
                def apply(arguments):
                    return literal_boolean(z3.simplify(extra(*[
                        z3.BoolVal(argument, ctx=node.ctx) for argument in arguments])))
                default = apply([v[0] for v in inputs])
                support = set().union(*(set(v[1]) for v in inputs))
                entries = {index: apply([v[1].get(index, v[0]) for v in inputs])
                           for index in support}
                values[key] = (None if default is None or any(v is None for v in entries.values())
                               else (default, {i: v for i, v in entries.items() if v != default}))
        return values[root.get_id()]

    while stack:
        term, ready = stack.pop()
        identity = term.get_id()
        if identity in rewritten:
            continue
        if z3.is_quantifier(term) or not z3.is_app(term):
            rewritten[identity] = term
            continue
        if boolean_array(term):
            value = ground_value(term)
            rewritten[identity] = term if value is None else canonical(value, term.sort())
            continue
        if not ready:
            stack.append((term, True))
            stack.extend((child, False) for child in reversed(term.children())
                         if child.get_id() not in rewritten)
            continue
        original_children = term.children()
        children = [rewritten[child.get_id()] for child in original_children]
        child_values = [values.get(child.get_id()) for child in original_children]
        updated = term.decl()(*children) if children else term
        if z3.is_eq(term) and len(children) == 2 and all(v is not None for v in child_values):
            updated = z3.BoolVal(child_values[0] == child_values[1], ctx=term.ctx)
        elif z3.is_app_of(term, z3.Z3_OP_DISTINCT) and child_values and all(v is not None for v in child_values):
            keys = [(v[0], tuple(sorted(v[1].items()))) for v in child_values]
            updated = z3.BoolVal(len(keys) == len(set(keys)), ctx=term.ctx)
        elif z3.is_select(term) and child_values[0] is not None and z3.is_int_value(children[1]):
            default, entries = child_values[0]
            updated = z3.BoolVal(entries.get(children[1].as_long(), default), ctx=term.ctx)
        # Normal scalar simplification is useful after exact array selects,
        # but avoid repeatedly traversing growing array Store chains.
        rewritten[identity] = updated if boolean_array(term) else z3.simplify(updated)
    return rewritten[expression.get_id()]
