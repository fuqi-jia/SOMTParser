"""Check an attained candidate optimum with two complete ordinary SMT queries.

Candidate values are hints only. Feasibility at those values and absence of
ANY lexicographically better target solution are separately checked. In
particular, the no-better query never asserts the candidate-value equalities.
"""
import z3

from .source_oracles.target_relation import read_target
from .target_solve import _auxiliary_terms, _check_auxiliary, _need, decode_value, encode_value, projection_terms, solve_target


def solve_target_at_objectives(data, projection, candidate_objectives, *, candidate_witness=None,
                               auxiliary_candidate=None, ground_candidate=False, progress_callback=None):
    variables, imported, directions = read_target(data)
    terms = projection_terms(variables, projection)
    assertions, objectives = list(imported.assertions()), list(imported.objectives())
    _need(isinstance(candidate_objectives, list) and len(candidate_objectives) == len(objectives)
          and bool(objectives), 'candidate must cover every ordered optimization objective')
    bounds = []
    for term, direction, record in zip(objectives, directions, candidate_objectives):
        original_value = decode_value(record, term.sort())
        _need(z3.is_int_value(original_value) or z3.is_rational_value(original_value),
              'candidate optimum must be an exact finite number')
        bounds.append(original_value if direction == 'minimize' else z3.simplify(-original_value))
    def event(phase, **details):
        if progress_callback is not None:
            progress_callback(dict(phase=phase, **details))
    ground_result = None
    if ground_candidate and candidate_witness is not None:
        from .ground_candidate import verify_ground_candidate
        event('ground-candidate-evaluation', event='started')
        ground_result = verify_ground_candidate(data, projection, candidate_witness,
                                                candidate_objectives, auxiliary_candidate)
        event('ground-candidate-evaluation', event='completed', accepted=ground_result is not None)
    if ground_result is not None:
        result = ground_result
        result.pop('fixed_values', None)
        result.pop('fixed_objectives', None)
        result.update(mode='target-optimization-by-complete-bound-queries',
            candidate_objectives=candidate_objectives, candidate_feasibility='sat',
            candidate_values_assumed_optimal=False, candidate_witness_origin='caller',
            candidate_witness=candidate_witness)
        if auxiliary_candidate is not None:
            result.update(candidate_auxiliary=auxiliary_candidate,
                          candidate_auxiliary_attempt=result['auxiliary_attempt'])
    else:
        feasible = z3.Solver(ctx=imported.ctx)
        feasible.add(*assertions, *(term == value for term, value in zip(objectives, bounds)))
        if candidate_witness is not None:
            _need(isinstance(candidate_witness, dict) and set(candidate_witness) == set(terms),
                  'candidate witness must cover exactly every projection coordinate')
            feasible.add(*(term == decode_value(candidate_witness[name], term.sort())
                           for name, term in terms.items()))
        auxiliary, auxiliary_fixed = _auxiliary_terms(variables, projection, auxiliary_candidate)
        event('candidate-objective-feasibility', event='started',
              seeded=candidate_witness is not None)
        answer, auxiliary_attempt = _check_auxiliary(feasible, auxiliary_fixed, auxiliary_candidate, event)
        event('candidate-objective-feasibility', event='completed', answer=str(answer))
        if answer != z3.sat:
            result = dict(status='candidate-infeasible' if answer == z3.unsat else 'unknown',
                          optimal=False, candidate_objectives=candidate_objectives,
                          candidate_feasibility=str(answer), equivalence_claimed=False)
            if auxiliary_candidate is not None:
                result.update(auxiliary_candidate=auxiliary_candidate, auxiliary_attempt=auxiliary_attempt)
            if answer == z3.unknown:
                result['reason_unknown'] = feasible.reason_unknown()
            return result
        model = feasible.model()
        witness = {name: encode_value(model.eval(term, model_completion=True)) for name, term in terms.items()}
        replay_auxiliary, auxiliary_serialization_error = None, None
        if auxiliary_candidate is not None:
            try:
                replay_auxiliary = dict(projection=auxiliary_candidate['projection'],
                    values={name: encode_value(model.eval(term, model_completion=True))
                            for name, term in auxiliary.items()}, origin='complete feasibility model')
            except ValueError as error:
                if not auxiliary_attempt['fallback_to_public_witness']:
                    raise
                auxiliary_serialization_error = str(error)
        # Independently replay every serialized target coordinate AND objective.
        result = solve_target(data, projection, fixed_values=witness,
                              fixed_objectives=candidate_objectives, auxiliary_candidate=replay_auxiliary,
                              progress_callback=progress_callback)
        _need(result['status'] == 'sat' and result['target_witness_replay'] == 'sat',
              'candidate target witness failed complete serialization replay')
        result.pop('fixed_values', None)
        result.pop('fixed_objectives', None)
        result.update(mode='target-optimization-by-complete-bound-queries',
                      candidate_objectives=candidate_objectives, candidate_feasibility='sat',
                      candidate_values_assumed_optimal=False,
                      candidate_witness_origin='caller' if candidate_witness is not None else None,
                      candidate_witness=candidate_witness)
        if auxiliary_candidate is not None:
            result.update(candidate_auxiliary=auxiliary_candidate,
                          candidate_auxiliary_attempt=auxiliary_attempt)
            if auxiliary_serialization_error is not None:
                result['candidate_auxiliary_serialization_skipped'] = auxiliary_serialization_error
    prefix, alternatives = [], []
    for term, value in zip(objectives, bounds):
        alternatives.append(z3.And(*prefix, term < value))
        prefix.append(term == value)
    # Neither candidate coordinates nor objective equalities belong in this query.
    better = z3.Solver(ctx=imported.ctx)
    better.add(*assertions, z3.Or(*alternatives))
    event('candidate-objective-no-better', event='started')
    better_answer = better.check()
    event('candidate-objective-no-better', event='completed', answer=str(better_answer))
    result.update(optimal=better_answer == z3.unsat, optimality_status=str(better_answer),
                  optimality_method='complete original assertions and strict lexicographic improvement',
                  no_better_query_smt2=better.sexpr() + '\n(check-sat)\n',
                  no_candidate_equalities_in_optimality_query=True,
                  no_candidate_coordinates_in_optimality_query=True,
                  no_candidate_auxiliary_equalities_in_optimality_query=True)
    if better_answer == z3.unsat:
        # Feasibility and serialization replay establish attainment. Absence
        # of any lexicographically better model proves these exact bounds;
        # later objectives are conditioned on the preceding optimal values.
        result['objective_bounds'] = [dict(
            lower_smt2=value.sexpr(), upper_smt2=value.sexpr(),
            finite_attained=True,
            proof_method='complete feasible candidate and strict lexicographic improvement UNSAT',
            lexicographic_prefix=[dict(objective_index=j, signed_value=encode_value(bounds[j]))
                                  for j in range(index)])
            for index, value in enumerate(bounds)]
    elif better_answer == z3.unknown:
        result['optimality_reason_unknown'] = better.reason_unknown()
    elif better_answer == z3.sat:
        countermodel = better.model()
        values = [countermodel.eval(term, model_completion=True) for term in objectives]
        result['better_original_objective_values'] = [encode_value(value if direction == 'minimize' else -value)
                                                     for value, direction in zip(values, directions)]
        result['better_target_witness'] = {name: encode_value(countermodel.eval(term, model_completion=True))
                                           for name, term in terms.items()}
    return result
