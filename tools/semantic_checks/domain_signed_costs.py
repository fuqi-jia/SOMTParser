"""Sufficient ordered-cost identities under the complete original source domain.

This certificate alone is not a feasible-relation certificate. A caller may
compose it with full source/target feasibility equivalence only when the source
relation retains these domains. No opposite-side bounds or model are used.
"""
import z3
from .arithmetic_context import _comparison_nodes
from .boolean_structure import structural_equivalence
from .packed_tuple_cliques import _bounds
from .qf_conjuncts import _conjuncts


def _canonical_booleans(root, keepalive=None):
    """Give identical Boolean subterms one DAG before exact sum simplification.

    For example, If(And(a,b),1,0) + If(And(b,a),1,0) then shares its
    indicator and simplifies to twice that indicator. No term is dropped and
    no arithmetic multiplicity is treated as Boolean idempotence.
    """
    memo, pending = {}, [(root, False)]
    while pending:
        node, ready = pending.pop()
        identity = node.get_id()
        if identity in memo:
            continue
        if z3.is_quantifier(node) or z3.is_var(node):
            return None
        children = node.children()
        if not ready:
            pending.append((node, True))
            pending.extend((child, False) for child in children
                           if child.get_id() not in memo)
            continue
        args = [memo[child.get_id()] for child in children]
        if z3.is_and(node) or z3.is_or(node):
            args.sort(key=lambda value: value.get_id())
        elif z3.is_eq(node) and all(z3.is_const(value) for value in args):
            # Normalize atomic indicator tests, keeping numerals on the
            # right. Reversing the outer arithmetic cost equation instead
            # can make simplify move an offset across just one equality.
            args.sort(key=lambda value: (value.decl().kind() != z3.Z3_OP_UNINTERPRETED,
                                         value.get_id()))
        memo[identity] = node.decl()(*args) if args else node
    # The final simplifier can replace a canonical equality by its reversed
    # spelling. Retain intermediate nodes across the two sides so their AST
    # IDs cannot be recycled and change the ordering of an enclosing And.
    if keepalive is not None:
        keepalive.extend(memo.values())
    return z3.simplify(memo[root.get_id()])


def _normalize_cost(domains, coordinate, value, bounds, keepalive=None):
    equation = z3.simplify(coordinate == value)
    scan = _comparison_nodes(equation)
    if scan is None:
        return None, 0
    replacements = []
    for node in scan[0]:
        if not z3.is_eq(node) or node.num_args() != 2:
            continue
        variable, numeral = node.children()
        if z3.is_int_value(variable):
            variable, numeral = numeral, variable
        if not (z3.is_const(variable) and z3.is_int(variable)
                and variable.decl().kind() == z3.Z3_OP_UNINTERPRETED
                and z3.is_int_value(numeral)):
            continue
        low, high = bounds.get(variable.get_id(), (None, None))
        # Exactly two adjacent integers. This law is false for Reals, larger
        # intervals, one-sided bounds, and domains taken from another formula.
        if low is not None and high == low + 1 and numeral.as_long() == high:
            replacements.append((node, z3.Not(variable == low)))
    rewritten = z3.substitute(equation, *replacements) if replacements else equation
    # Bounds used by the rewrite remain inside EACH complete cost relation.
    return _canonical_booleans(z3.And(domains, z3.simplify(rewritten)), keepalive), len(replacements)


def prove_domain_signed_costs(domains, left, right):
    """Prove each ordered signed cost on every original domain assignment.

    Inputs are already signed (maximization negated). A nonmatch is merely
    inconclusive. This routine performs no Solver.check and invents no domain.
    """
    if not z3.is_bool(domains):
        raise ValueError('signed-cost domains must be Boolean')
    left, right = tuple(left), tuple(right)
    if len(left) != len(right):
        raise ValueError('ordered signed-cost counts differ')
    for a, b in zip(left, right):
        if a.ctx != domains.ctx or b.ctx != domains.ctx:
            raise ValueError('signed costs and domains need one Z3 context')
        if not a.sort().eq(b.sort()):
            raise ValueError('ordered signed-cost sorts differ')
    simplified_domains = z3.simplify(domains)
    bounds = _bounds(_conjuncts(simplified_domains))
    if any(lo is not None and hi is not None and lo > hi
           for lo, hi in bounds.values()):
        bounds = {}
    result = dict(equivalent=None, solver_queries=0,
                  method='ordered signed-cost identities under retained original source domains',
                  all_original_domains_retained=True, ordered_costs=len(left),
                  requires_complete_feasibility_certificate=True, components=[])
    for index, (a, b) in enumerate(zip(left, right)):
        coordinate = z3.FreshConst(a.sort(), prefix='domain_signed_cost')
        formulas, counts, keepalive = [], [], []
        for value in (a, b):
            formula, count = _normalize_cost(simplified_domains, coordinate, value, bounds, keepalive)
            if formula is None:
                return dict(result, reason='quantifier or loose bound variable in cost/domain')
            formulas.append(formula)
            counts.append(count)
        proof = structural_equivalence(*formulas)
        result['components'].append(dict(index=index, two_value_equalities=counts,
                                         structural=proof))
        if proof['equivalent'] is not True:
            return dict(result, reason='normalized full domain-cost relations do not correspond')
    return dict(result, equivalent=True, reason='all ordered domain-cost relations correspond')
