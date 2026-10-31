"""Group additive constant-valued integer tables by their exact index.

Different index groups and unsupported terms remain independent summands. Each
group is normalized by the full-Int-domain table API, retaining both infinite
tails. No domain assumptions, solver queries or expansion of products are used.
"""
from dataclasses import dataclass

from .expression_interval_bounds import _linear_terms, _literal
from .integer_piecewise_tables import normalize_integer_piecewise_tables


@dataclass(frozen=True)
class IntegerTableSumNormalization:
    formula: object
    grouped_sums: int
    combined_groups: int
    cancelled_groups: int
    visited_nodes: int


def normalize_integer_table_sums(formula):
    """Combine same-index summands without conflating different table inputs.

    Linear decomposition counts every occurrence of shared DAG terms before
    combining coefficients. Nonlinear products remain opaque unless the whole
    product is itself a constant-valued table of a single exact integer index.
    Quantifier bodies are opaque. Rewriting is an identity over the full domain.
    """
    import z3

    unsupported = object()
    signatures, memo = {}, {}
    grouped_sums = combined_groups = cancelled_groups = 0
    operations = {z3.Z3_OP_ITE, z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT, z3.Z3_OP_NOT,
                  z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_IMPLIES, z3.Z3_OP_XOR,
                  z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT,
                  z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL}
    comparisons = {z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT, z3.Z3_OP_LE,
                   z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT}
    arithmetic = {z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL}

    def table_index(root):
        pending = [(root, False)]
        while pending:
            node, ready = pending.pop()
            key = node.get_id()
            if key in signatures:
                continue
            if not z3.is_app(node):
                signatures[key] = (node, unsupported)
                continue
            children = node.children()
            if children and not ready:
                pending.append((node, True))
                pending.extend((child, False) for child in children)
                continue
            kind = node.decl().kind()
            answer = unsupported
            if z3.is_int_value(node) or z3.is_true(node) or z3.is_false(node):
                answer = None
            elif kind in operations:
                records = [signatures[child.get_id()][1] for child in children]
                if all(record is not unsupported for record in records):
                    roots = {record.get_id(): record for record in records
                             if record is not None}
                    if len(roots) <= 1:
                        answer = next(iter(roots.values()), None)
            if answer is unsupported and kind in comparisons and len(children) == 2:
                left, right = children
                if _literal(left) is not None:
                    left, right = right, left
                if z3.is_int(left) and _literal(right) is not None:
                    answer = left
            # Both source node and index stay alive while their AST ids are keys.
            signatures[key] = (node, answer)
        return signatures[root.get_id()][1]

    def normalize_sum(node):
        nonlocal grouped_sums, combined_groups, cancelled_groups
        terms, offset = _linear_terms(node)
        groups, opaque = {}, []
        for atom, coefficient in terms:
            index = table_index(atom)
            if index is unsupported:
                opaque.append(coefficient * atom if coefficient != 1 else atom)
            elif index is None:
                # The recognizer only admits supported constant expressions.
                value = normalize_integer_piecewise_tables(atom).formula
                if z3.is_int_value(value):
                    offset += coefficient * value.as_long()
                else:
                    opaque.append(coefficient * atom if coefficient != 1 else atom)
            else:
                groups.setdefault(index.get_id(), [index, []])[1].append((atom, coefficient))
        changed = False
        for index, atoms in groups.values():
            if len(atoms) == 1 and atoms[0][1] == 1:
                opaque.append(atoms[0][0])
                continue
            expression = z3.Sum(*[coefficient * atom if coefficient != 1 else atom
                                  for atom, coefficient in atoms])
            value = normalize_integer_piecewise_tables(expression).formula
            combined_groups += 1
            changed = True
            if z3.is_int_value(value):
                offset += value.as_long()
                cancelled_groups += value.as_long() == 0
            else:
                opaque.append(value)
        grouped_sums += changed
        # Do not simplify only one partial sum: moving offsets through its
        # comparison guards can hide the exact index shared with later terms.
        # Explicit rebuilding also keeps quantifiers in opaque terms intact.
        if offset or not opaque:
            opaque.append(z3.IntVal(offset, ctx=formula.ctx))
        return opaque[0] if len(opaque) == 1 else z3.Sum(*opaque)

    pending = [(formula, False)]
    while pending:
        original, ready = pending.pop()
        key = original.get_id()
        if key in memo:
            continue
        if not z3.is_app(original):
            memo[key] = (original, original)
            continue
        children = original.children()
        if children and not ready:
            pending.append((original, True))
            pending.extend((child, False) for child in children)
            continue
        rewritten = [memo[child.get_id()][1] for child in children]
        node = (original if all(a.eq(b) for a, b in zip(children, rewritten))
                else original.decl()(*rewritten))
        if z3.is_int(node) and node.decl().kind() in arithmetic:
            node = normalize_sum(node)
        memo[key] = (original, node)
    return IntegerTableSumNormalization(memo[formula.get_id()][1], grouped_sums,
                                        combined_groups, cancelled_groups, len(memo))
