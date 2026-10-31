"""Prove redundant finite characteristic-array representations from hard domains.

Only positive asserted intersection equalities supply a carrier. Every lemma
is independently proved from that exact equality before it is returned. The
caller must keep all original assertions; no candidate assignment is used.
"""
import z3

from .ground_bool_arrays import simplify_ground_bool_arrays
from .target_solve import encode_value


def prove_finite_set_representations(assertions, record):
    """Call record(premise, lemma, answer, query_smt2) for every attempted proof."""
    pending, seen, lemmas = list(assertions), set(), []
    while pending:
        premise = pending.pop()
        if premise.get_id() in seen:
            continue
        seen.add(premise.get_id())
        if z3.is_and(premise):
            pending.extend(premise.children())
            continue
        if not z3.is_eq(premise):
            continue
        description = None
        for selected, intersection in [premise.children(), premise.children()[::-1]]:
            sort = selected.sort()
            if (sort.kind() != z3.Z3_ARRAY_SORT or sort.domain().kind() != z3.Z3_INT_SORT
                    or sort.range().kind() != z3.Z3_BOOL_SORT or not z3.is_app(intersection)
                    or intersection.decl().kind() != z3.Z3_OP_ARRAY_MAP
                    or intersection.num_args() != 2
                    or z3.get_map_func(intersection).kind() != z3.Z3_OP_AND):
                continue
            children = intersection.children()
            if children[0].eq(selected):
                carrier = children[1]
            elif children[1].eq(selected):
                carrier = children[0]
            else:
                continue
            try:
                carrier_value = encode_value(simplify_ground_bool_arrays(carrier))
            except (ValueError, z3.Z3Exception):
                continue
            if carrier_value['type'] != 'set-int':
                continue
            description = selected, [int(index) for index in carrier_value['elements']]
            break
        if description is None:
            continue
        selected, support = description
        representation = z3.K(selected.sort().domain(), z3.BoolVal(False, ctx=selected.ctx))
        for index in support:
            position = z3.IntVal(index, ctx=selected.ctx)
            representation = z3.Store(representation, position, z3.Select(selected, position))
        lemma = selected == representation
        solver = z3.Solver(ctx=selected.ctx)
        solver.add(premise, z3.Not(lemma))
        query = solver.sexpr() + '\n(check-sat)\n'
        answer = solver.check()
        record(premise, lemma, str(answer), query)
        if answer == z3.unsat:
            lemmas.append(lemma)
    return lemmas
