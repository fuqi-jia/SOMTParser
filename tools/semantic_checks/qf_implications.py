"""Complete QF equivalence from independently proved conjunct implications.

For every original conjunct of A, prove B implies it; then symmetrically prove
A implies every conjunct of B. Each local query may use a subset of the actual
opposite formula: this strengthens the obligation, so UNSAT remains sufficient.
No implication relies on a sibling implication having been accepted. In
particular, unequal but mutually redundant domain clauses do not create a
circular assumption. A SAT local query is inconclusive for the complete input.
"""
import z3
from .qf_conjuncts import _conjuncts, _signatures
from .nonnegative_sum_context import nonnegative_sum_plans, project_nonnegative_sums
from .renamed_unsat_cache import RenamedUnsatCache


def prove_qf_conjunct_implications(left, right):
    if left.ctx != right.ctx:
        raise ValueError('conjunct implication needs one Z3 context')
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('conjunct implication requires Boolean formulas')
    result = dict(equivalent=None, solver_queries=0, obligations=[],
                  method='both directions, every original conjunct implied by opposite input',
                  all_original_conjuncts_retained=True)
    # Keep generated Not nodes alive and include them in the signature DAG.
    parts = [_conjuncts(root) for root in (left, right)]
    signatures = _signatures(tuple(node for side in parts for node in side))
    if signatures is None:
        return dict(result, reason='quantifier or loose bound variable')
    sides = [{node.get_id(): node for node in side} for side in parts]
    sum_plans = [nonnegative_sum_plans(side) for side in sides]
    common = sides[0].keys() & sides[1].keys()
    result.update(left_unique_conjuncts=len(sides[0]),
                  right_unique_conjuncts=len(sides[1]),
                  shared_original_conjuncts=len(common))
    indexes, unary = [], []
    for side in sides:
        index, single = {}, {}
        for identity in side:
            signature = signatures[identity]
            for declaration in signature:
                index.setdefault(declaration, set()).add(identity)
            if len(signature) == 1:
                single.setdefault(next(iter(signature)), set()).add(identity)
        indexes.append(index)
        unary.append(single)
    result['covered_conjuncts'] = [len(common), len(common)]
    unsat_cache = RenamedUnsatCache(left.ctx)
    for side_number, side in enumerate(sides):
        opposite_number = 1 - side_number
        opposite = sides[opposite_number]
        index = indexes[opposite_number]
        groups = {}
        for identity, node in side.items():
            if identity not in common:
                groups.setdefault(signatures[identity], []).append(node)
        for key in sorted(groups, key=lambda item: (len(item), tuple(sorted(item)))):
            group = groups[key]
            # Original clauses mentioning the conclusion's symbols, and
            # original unary clauses for their immediate neighboring symbols.
            context_ids = {identity for declaration in key
                           for identity in index.get(declaration, ())}
            neighbors = {declaration for identity in context_ids
                         for declaration in signatures[identity]}
            context_ids.update(identity for declaration in neighbors
                               for identity in unary[opposite_number].get(declaration, ()))
            context_ids.update(identity for identity in opposite
                               if not signatures[identity])
            local_ids = {identity for identity in context_ids
                         if signatures[identity] <= key}
            projected, projections = project_nonnegative_sums(
                *sum_plans[opposite_number], context_ids - local_ids, key)
            contexts = []
            if local_ids != context_ids:
                contexts.append(('conclusion-symbols', local_ids, projected, projections))
            contexts.append(('original-neighbors', context_ids, (), []))
            # Both attempts use only original opposite clauses and necessary
            # consequences of their nonnegative sums. A small-context SAT or
            # unknown is not a counterexample to the full relation: retry the
            # complete existing neighborhood without assuming any conclusion.
            attempts = []
            for context_kind, selected, derived, projection_records in contexts:
                obligation = z3.And(*(opposite[identity] for identity in sorted(selected)),
                                    *derived, z3.Not(z3.And(*group)))
                candidate = unsat_cache.prepare(obligation,
                    (context_kind, len(selected), len(derived), len(group)))
                reused = unsat_cache.lookup(candidate)
                if reused is not None:
                    answer = z3.unsat
                else:
                    solver = z3.Solver(ctx=left.ctx)
                    solver.add(obligation)
                    answer = solver.check()
                    result['solver_queries'] += 1
                    if answer == z3.unsat:
                        unsat_cache.remember_unsat(candidate, result['solver_queries'])
                record = dict(direction='right-implies-left' if side_number == 0 else 'left-implies-right',
                              declarations=sorted(key), conclusion_conjuncts=len(group),
                              context_kind=context_kind,
                              opposite_original_context_conjuncts=len(selected),
                              necessary_sum_consequences=len(derived),
                              nonnegative_sum_projections=projection_records, answer=str(answer))
                record.update(solver_executed=reused is None, unsat_reuse=reused)
                if answer == z3.unknown:
                    record['reason_unknown'] = solver.reason_unknown()
                attempts.append(record)
                if answer == z3.unsat:
                    break
            result['obligations'].append(dict(record, attempts=attempts))
            if answer != z3.unsat:
                return dict(result, reason='unproved local implication; full relation undecided')
            result['covered_conjuncts'][side_number] += len(group)
    assert result['covered_conjuncts'] == [len(side) for side in sides]
    return dict(result, equivalent=True, reason='every original conjunct proved in both directions')
