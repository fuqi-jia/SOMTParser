"""Complete QF equivalence from independently proved conjunct implications.

For every original conjunct of A, prove B implies it; then symmetrically prove
A implies every conjunct of B. Each local query may use a subset of the actual
opposite formula: this strengthens the obligation, so UNSAT remains sufficient.
No implication relies on a sibling implication having been accepted. In
particular, unequal but mutually redundant domain clauses do not create a
circular assumption. A local SAT model is refined only with clauses from the
original opposite input that it does not satisfy. Each refinement strictly adds
an original clause, so this finite procedure eventually proves the implication,
finds a model of the full opposite input, or receives unknown. No inferred lemma
or candidate-side condition is assumed.
"""
import z3
from .qf_conjuncts import _conjuncts, _signatures


def prove_qf_refined_implications(left, right):
    if left.ctx != right.ctx:
        raise ValueError('conjunct implication needs one Z3 context')
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('conjunct implication requires Boolean formulas')
    result = dict(equivalent=None, solver_queries=0, obligations=[],
                  method='both directions, every original conjunct implied by opposite input',
                  all_original_conjuncts_retained=True)
    sides = [{node.get_id(): node for node in _conjuncts(root)}
             for root in (left, right)]
    signatures = _signatures(tuple(node for side in sides for node in side.values()))
    if signatures is None:
        return dict(result, reason='quantifier or loose bound variable')
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
            solver = z3.Solver(ctx=left.ctx)
            solver.add(*(opposite[identity] for identity in sorted(context_ids)))
            solver.add(z3.Not(z3.And(*group)))
            refinements = []
            full_opposite_model = False
            while True:
                answer = solver.check()
                result['solver_queries'] += 1
                if answer != z3.sat:
                    break
                model = solver.model()
                additions = [identity for identity in opposite if identity not in context_ids
                             and not z3.is_true(model.eval(opposite[identity], model_completion=True))]
                if not additions:
                    full_opposite_model = True
                    break
                # Every added premise belongs to the original opposite side.
                # A model of the complete implication counterexample must
                # satisfy it, regardless of how this local model was obtained.
                context_ids.update(additions)
                solver.add(*(opposite[identity] for identity in sorted(additions)))
                refinements.append(len(additions))
            record = dict(direction='right-implies-left' if side_number == 0 else 'left-implies-right',
                          declarations=sorted(key), conclusion_conjuncts=len(group),
                          opposite_original_context_conjuncts=len(context_ids), answer=str(answer),
                          refinement_added_conjuncts=refinements, full_opposite_model=full_opposite_model)
            if full_opposite_model:
                record['full_opposite_counterexample_model'] = solver.model().sexpr()
            if answer == z3.unknown:
                record['reason_unknown'] = solver.reason_unknown()
            result['obligations'].append(record)
            if answer != z3.unsat:
                return dict(result, reason='full opposite counterexample' if full_opposite_model else 'unproved implication')
            result['covered_conjuncts'][side_number] += len(group)
    assert result['covered_conjuncts'] == [len(side) for side in sides]
    return dict(result, equivalent=True, reason='every original conjunct proved in both directions')
