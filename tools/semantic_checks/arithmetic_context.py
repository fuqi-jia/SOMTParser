"""Exact integer normalization under retained, input-local unary bounds.

Each Boolean replacement follows from the formula's own original bounds. Those
bounds are re-conjoined after rewriting. Integer quotient cancellation uses the
SMT identity d*div(a,d) = a-mod(a,d) only for a nonzero integer numeral d. No
fact from an opposite relation, solver assignment or assumed source profile is
used. The input formula is never mutated; quantifiers are left unchanged.
"""
from dataclasses import dataclass
import z3
from z3 import z3core
from .packed_tuple_cliques import _affine, _bounds
from .qf_conjuncts import _conjuncts, _unary_numeric_bound


@dataclass(frozen=True)
class ArithmeticContextProjection:
    formula: object
    retained_original_bounds: int = 0
    decided_comparisons: int = 0
    quotient_remainders: int = 0


def _interval(terms, offset, bounds):
    low = high = offset
    for value, coefficient in terms:
        a, b = bounds.get(value.get_id(), (None, None))
        if coefficient < 0:
            a, b = b, a
        low = None if low is None or a is None else low + coefficient * a
        high = None if high is None or b is None else high + coefficient * b
    return low, high


def _affine_difference(left, right, cache):
    """Reuse operand analyses only inside one input formula and Z3 context."""
    values = []
    for operand in (left, right):
        identity = operand.get_id()
        if identity not in cache:
            cache[identity] = _affine(operand)
        value = cache[identity]
        if value is None:
            return None
        values.append(value)
    terms = {}
    for (atoms, _), sign in zip(values, (1, -1)):
        for variable, coefficient in atoms:
            identity = variable.get_id()
            previous = terms.get(identity, (variable, 0))[1]
            terms[identity] = (variable, previous + sign * coefficient)
    return ([(variable, coefficient) for variable, coefficient in terms.values()
             if coefficient], values[0][1] - values[1][1])


def _comparison_truth(node, bounds, affine_cache=None):
    if (not z3.is_app(node) or node.num_args() != 2
            or node.decl().kind() not in (z3.Z3_OP_EQ, z3.Z3_OP_LE,
                                          z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT)
            or not all(z3.is_int(child) for child in node.children())):
        return None
    affine = (_affine(node.arg(0) - node.arg(1)) if affine_cache is None
              else _affine_difference(node.arg(0), node.arg(1), affine_cache))
    if affine is None:
        return None
    low, high = _interval(*affine, bounds)
    kind = node.decl().kind()
    if kind == z3.Z3_OP_EQ:
        if low == high == 0:
            return True
        if low is not None and low > 0 or high is not None and high < 0:
            return False
    elif kind in (z3.Z3_OP_LE, z3.Z3_OP_LT):
        threshold = 0 if kind == z3.Z3_OP_LE else -1
        if high is not None and high <= threshold:
            return True
        if low is not None and low > threshold:
            return False
    else:
        threshold = 0 if kind == z3.Z3_OP_GE else 1
        if low is not None and low >= threshold:
            return True
        if high is not None and high < threshold:
            return False
    return None


def _linear_atoms(root):
    """Integer linear combination of opaque terms; no nonlinear expansion."""
    terms, offset, pending = {}, 0, [(root, 1)]
    while pending:
        node, coefficient = pending.pop()
        kind = node.decl().kind()
        if z3.is_int_value(node):
            offset += coefficient * node.as_long()
        elif kind == z3.Z3_OP_ADD:
            pending.extend((child, coefficient) for child in node.children())
        elif kind == z3.Z3_OP_SUB:
            pending.extend((child, coefficient if i == 0 else -coefficient)
                           for i, child in enumerate(node.children()))
        elif kind == z3.Z3_OP_UMINUS:
            pending.append((node.arg(0), -coefficient))
        elif kind == z3.Z3_OP_MUL:
            atoms, scale = [], coefficient
            for child in node.children():
                if z3.is_int_value(child):
                    scale *= child.as_long()
                else:
                    atoms.append(child)
            if len(atoms) == 1:
                pending.append((atoms[0], scale))
            else:
                key = node.get_id()
                value, old = terms.get(key, (node, 0))
                terms[key] = (value, old + coefficient)
        else:
            key = node.get_id()
            value, old = terms.get(key, (node, 0))
            terms[key] = (value, old + coefficient)
    return terms, offset


def _cancel_quotients(root):
    memo, pending, count = {}, [(root, False)], 0
    while pending:
        node, ready = pending.pop()
        key = node.get_id()
        if key in memo:
            continue
        children = node.children()
        if not ready:
            pending.append((node, True))
            pending.extend((child, False) for child in children if child.get_id() not in memo)
            continue
        current = node.decl()(*[memo[child.get_id()] for child in children]) if children else node
        if (z3.is_int(current) and current.decl().kind() in
                (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL, z3.Z3_OP_UMINUS)):
            terms, offset = _linear_atoms(current)
            additions, removed = [], []
            for identity, (term, coefficient) in terms.items():
                if (coefficient and z3.is_app_of(term, z3.Z3_OP_IDIV)
                        and z3.is_int_value(term.arg(1))):
                    divisor = term.arg(1).as_long()
                    if divisor and coefficient % divisor == 0:
                        factor = coefficient // divisor
                        additions.extend((factor * term.arg(0), -factor * (term.arg(0) % divisor)))
                        removed.append(identity)
            if removed:
                count += len(removed)
                current = z3.simplify(z3.Sum(z3.IntVal(offset, ctx=root.ctx),
                    *[coefficient * term for identity, (term, coefficient) in terms.items()
                      if identity not in removed and coefficient], *additions))
        memo[key] = current
    return memo[root.get_id()], count


def _comparison_nodes(formula):
    """Scan the shared DAG without materializing every child as an ExprRef.

    The input formula owns all AST references for this traversal. Only Boolean
    comparisons that the normalizer can inspect need Python wrappers. Retain
    the previous conservative contract for any quantifier or bound variable.
    """
    context = formula.ctx_ref()
    comparisons, seen, pending = [], set(), [formula.as_ast()]
    has_integer_division = False
    kinds = {z3.Z3_OP_EQ, z3.Z3_OP_LE, z3.Z3_OP_LT,
             z3.Z3_OP_GE, z3.Z3_OP_GT}
    while pending:
        node = pending.pop()
        identity = z3core.Z3_get_ast_id(context, node)
        if identity in seen:
            continue
        seen.add(identity)
        kind = z3core.Z3_get_ast_kind(context, node)
        if kind in (z3.Z3_QUANTIFIER_AST, z3.Z3_VAR_AST):
            return None
        if kind != z3.Z3_APP_AST:
            continue
        application = z3core.Z3_to_app(context, node)
        declaration = z3core.Z3_get_app_decl(context, application)
        operator = z3core.Z3_get_decl_kind(context, declaration)
        has_integer_division |= operator == z3.Z3_OP_IDIV
        if operator in kinds:
            comparisons.append(z3.BoolRef(node, formula.ctx))
        pending.extend(z3core.Z3_get_app_arg(context, application, index)
                       for index in range(z3core.Z3_get_app_num_args(context, application)))
    return comparisons, has_integer_division


def normalize_arithmetic_context(formula):
    """Return an equivalent complete formula and explicit normalization counts."""
    if not z3.is_bool(formula):
        raise ValueError('arithmetic context needs a Boolean formula')
    scan = _comparison_nodes(formula)
    if scan is None:
        return ArithmeticContextProjection(formula)
    nodes, has_integer_division = scan
    clauses = _conjuncts(formula)
    bounds = _bounds(clauses)
    if any(low is not None and high is not None and low > high for low, high in bounds.values()):
        return ArithmeticContextProjection(formula)
    originals = [clause for clause in clauses if _unary_numeric_bound(clause)]
    replacements = []
    # AST identities are unique only within a context and lifetime. Keeping this
    # cache local, while formula owns every operand, prevents cross-input reuse.
    affine_cache = {}
    for node in nodes:
        answer = _comparison_truth(node, bounds, affine_cache)
        if answer is not None:
            replacements.append((node, z3.BoolVal(answer, ctx=formula.ctx)))
    rewritten = z3.substitute(formula, *replacements) if replacements else formula
    rewritten = z3.simplify(rewritten)
    # Cancellation is an optional equivalent rewrite. With no integer division
    # in the input, avoid rebuilding its entire DAG for this optimization.
    # Bounds and comparison replacements above remain unchanged.
    rewritten, count = (_cancel_quotients(rewritten) if has_integer_division
                        else (rewritten, 0))
    # The branch facts hold only under these original input conjuncts.
    complete = z3.simplify(z3.And(*originals, rewritten)) if replacements else z3.simplify(rewritten)
    return ArithmeticContextProjection(complete, len(originals), len(replacements), count)
