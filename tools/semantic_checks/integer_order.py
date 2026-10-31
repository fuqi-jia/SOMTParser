"""Exact integer order normalization for complete relation comparison.

Every integer comparison becomes a non-strict lower bound on its difference.
Strict order uses the discrete successor identity, including under negation.
No variable domains are inferred or added. Real and bit-vector order are not
given integer successor semantics.
"""
from dataclasses import dataclass
import z3


@dataclass(frozen=True)
class IntegerOrderNormalization:
    formula: object
    eligible_comparisons: int = 0


def normalize_integer_order(formula):
    pending, seen, substitutions = [formula], set(), []
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_quantifier(node):
            pending.append(node.body())
            continue
        if not z3.is_app(node):
            continue
        pending.extend(node.children())
        negated = z3.is_not(node)
        atom = node.arg(0) if negated else node
        if not z3.is_app(atom) or atom.num_args() != 2:
            continue
        kind = atom.decl().kind()
        if kind not in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
            continue
        left, right = atom.children()
        if any(term.sort().kind() != z3.Z3_INT_SORT for term in (left, right)):
            continue
        if negated:
            kind = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_LT: z3.Z3_OP_GE,
                    z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_GT: z3.Z3_OP_LE}[kind]
        difference = left - right if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT) else right - left
        threshold = 1 if kind in (z3.Z3_OP_LT, z3.Z3_OP_GT) else 0
        substitutions.append((node, difference >= threshold))
    # Simultaneous AST substitution retains binder structure and introduces no
    # symbols. Overlapping rewrites may leave nested orders in their original
    # form; that affects matching power, never the represented relation.
    rewritten = z3.substitute(formula, *substitutions) if substitutions else formula
    result = z3.simplify(rewritten, arith_lhs=True, sort_sums=True)
    return IntegerOrderNormalization(result, len(substitutions))
