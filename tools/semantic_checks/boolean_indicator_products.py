"""Exact products of arithmetic Boolean indicators, without domain assumptions."""
from dataclasses import dataclass

import z3


@dataclass(frozen=True)
class IndicatorProductProjection:
    formula: z3.BoolRef
    product_nodes: int = 0
    combined_factors: int = 0
    complete_scan: bool = True


def _indicator_condition(value):
    if not (z3.is_app_of(value, z3.Z3_OP_ITE) and
            (z3.is_int(value) or z3.is_real(value))):
        return None
    condition, positive, negative = value.children()
    is_number = z3.is_int_value if z3.is_int(value) else z3.is_rational_value
    if not (is_number(positive) and is_number(negative)):
        return None
    if z3.is_int(value):
        a, b = positive.as_long(), negative.as_long()
    else:
        a, b = positive.as_fraction(), negative.as_fraction()
    if (a, b) == (1, 0):
        return condition
    if (a, b) == (0, 1):
        return z3.Not(condition)
    return None


def normalize_boolean_indicator_products(formula):
    """Combine indicator factors in the complete Boolean formula.

    Every other factor, coefficient, constraint and observation is retained.
    Quantifiers and loose bound variables leave the entire input unchanged;
    callers can apply this after opening an existential body capture-safely.
    ``complete_scan`` distinguishes a complete unchanged DAG from that refusal,
    so a caller need not rescan all shared subgraphs in individual conjuncts.
    """
    if not z3.is_bool(formula):
        raise ValueError('indicator normalization needs a Boolean formula')
    memo, parts, pending = {}, {}, [(formula, False)]
    products = factors = 0
    while pending:
        node, ready = pending.pop()
        identity = node.get_id()
        if identity in memo:
            continue
        if z3.is_quantifier(node) or z3.is_var(node):
            return IndicatorProductProjection(formula, complete_scan=False)
        children = node.children()
        if not ready:
            pending.append((node, True))
            pending.extend((child, False) for child in children
                           if child.get_id() not in memo)
            continue
        args = [memo[child.get_id()] for child in children]
        current = (node.decl()(*args) if any(not a.eq(b) for a, b in zip(args, children))
                   else node)
        if z3.is_app_of(current, z3.Z3_OP_MUL) and (z3.is_int(current) or z3.is_real(current)):
            conditions, other = [], []
            for original_child, child in zip(children, args):
                condition = _indicator_condition(child)
                if condition is not None:
                    conditions.append(condition)
                elif original_child.get_id() in parts:
                    condition, residual = parts[original_child.get_id()]
                    if condition is not None:
                        conditions.append(condition)
                    if residual is not None:
                        other.append(residual)
                else:
                    other.append(child)
            condition = z3.And(*conditions) if conditions else None
            residual = (z3.Product(*other) if len(other) > 1 else other[0]) if other else None
            # Factored summaries share their residual DAGs. This also handles
            # left-associated x * indicator(b) * indicator(c), without
            # repeatedly flattening a long chain of non-indicator factors.
            parts[identity] = condition, residual
            if len(conditions) >= 2:
                number = z3.IntVal if z3.is_int(current) else z3.RealVal
                combined = z3.If(condition, number(1, ctx=formula.ctx),
                                 number(0, ctx=formula.ctx))
                current = residual * combined if residual is not None else combined
                products += 1
                factors += len(conditions) - 1
        memo[identity] = current
    if not products:
        return IndicatorProductProjection(formula)
    return IndicatorProductProjection(z3.simplify(memo[formula.get_id()]), products, factors)
