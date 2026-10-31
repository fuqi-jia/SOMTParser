"""Verify one complete interpretation without searching for a satisfying model.

Array coordinates not supplied by the caller get arbitrary constant defaults.
These are candidate choices, never constraints added to an optimality query.
Every original assertion, public coordinate and ordered objective is checked;
unsupported or false evaluations simply decline this optional fast path.
"""
import hashlib

import z3

from .ground_bool_arrays import simplify_ground_bool_arrays
from .source_oracles.target_relation import read_target
from .source_oracles.fzn_json_source import Unsupported
from .target_solve import _auxiliary_terms, _need, decode_value, encode_value, projection_terms


def verify_ground_candidate(data, projection, fixed_values, fixed_objectives, auxiliary_candidate=None):
    """Return exact SAT/replay evidence, or None when this candidate is not certified."""
    try:
        variables, imported, directions = read_target(data)
    except Unsupported:
        return None
    assertions, objectives = list(imported.assertions()), list(imported.objectives())
    terms = projection_terms(variables, projection)
    _need(isinstance(fixed_values, dict) and set(fixed_values) == set(terms),
          'ground candidate must cover every public coordinate')
    if fixed_objectives is None:
        return None
    _need(isinstance(fixed_objectives, list) and len(fixed_objectives) == len(objectives),
          'ground candidate must include every ordered objective')
    auxiliary, _ = _auxiliary_terms(variables, projection, auxiliary_candidate)
    for key, term in terms.items():
        decode_value(fixed_values[key], term.sort())
    for term, record in zip(objectives, fixed_objectives):
        decode_value(record, term.sort())

    def default(sort):
        if sort.kind() == z3.Z3_INT_SORT:
            return z3.IntVal(0, ctx=sort.ctx)
        if sort.kind() == z3.Z3_REAL_SORT:
            return z3.RealVal(0, ctx=sort.ctx)
        if sort.kind() == z3.Z3_BOOL_SORT:
            return z3.BoolVal(False, ctx=sort.ctx)
        if sort.kind() == z3.Z3_ARRAY_SORT and sort.domain().kind() == z3.Z3_INT_SORT:
            return z3.K(sort.domain(), default(sort.range()))
        raise ValueError('unsupported total candidate default')

    def assemble(sort, cells):
        direct = [record for indices, record in cells if not indices]
        if direct:
            _need(len(cells) == len(direct) == 1, 'overlapping candidate array coordinates')
            return decode_value(direct[0], sort)
        _need(sort.kind() == z3.Z3_ARRAY_SORT and sort.domain().kind() == z3.Z3_INT_SORT,
              'candidate coordinates require integer-indexed arrays')
        groups = {}
        for indices, record in cells:
            groups.setdefault(indices[0], []).append((indices[1:], record))
        result = default(sort)
        for index, rows in sorted(groups.items()):
            result = z3.Store(result, z3.IntVal(index, ctx=sort.ctx), assemble(sort.range(), rows))
        return result

    groups = {}
    supplied = [(projection, fixed_values)]
    if auxiliary_candidate is not None:
        supplied.append((auxiliary_candidate['projection'], auxiliary_candidate['values']))
    for coordinates, values in supplied:
        for row in coordinates:
            groups.setdefault(row['symbol'], []).append((row.get('indices', []), values[row['id']]))
    try:
        values = {name: assemble(term.sort(), groups[name]) if name in groups else default(term.sort())
                  for name, term in variables.items()}
    except ValueError:
        return None

    def verify(assignments):
        # Substitute the complete interpretation once. Rebuilding all N symbol
        # bindings for each of M assertions/coordinates makes model checking
        # quadratic even when every assertion mentions only a few symbols.
        checks = list(assertions)
        for coordinate, value in fixed_values.items():
            term = terms[coordinate]
            checks.append(term == decode_value(value, term.sort()))
        for coordinate, term in auxiliary.items():
            checks.append(term == decode_value(auxiliary_candidate['values'][coordinate], term.sort()))
        for term, direction, record in zip(objectives, directions, fixed_objectives):
            original = term if direction == 'minimize' else -term
            checks.append(original == decode_value(record, term.sort()))
        conjunction = z3.And(*checks) if checks else z3.BoolVal(True, ctx=imported.ctx)
        grounded = z3.substitute(conjunction, *[(variables[name], value)
                                               for name, value in assignments.items()])
        if not z3.is_true(simplify_ground_bool_arrays(z3.simplify(grounded))):
            return None
        # Every equality above was checked against the total interpretation;
        # normalize those exact values without repeating a whole-model
        # substitution for each scalar in the returned witness.
        signed = [encode_value(z3.simplify(decode_value(record, term.sort()) *
                                          (1 if direction == 'minimize' else -1)))
                  for term, direction, record in zip(objectives, directions, fixed_objectives)]
        witness = {key: encode_value(decode_value(fixed_values[key], term.sort()))
                   for key, term in terms.items()}
        extra = {key: encode_value(decode_value(auxiliary_candidate['values'][key], term.sort()))
                 for key, term in auxiliary.items()}
        return signed, witness, extra

    try:
        checked = verify(values)
    except (ValueError, z3.Z3Exception):
        return None
    if checked is None:
        return None
    # Parse every serialized assignment back into the original declaration
    # environment and re-evaluate the complete original model a second time.
    serialized, model_lines, replay_values = [], [], {}
    for name, value in values.items():
        variable = variables[name]
        equality = '(assert (= ' + variable.sexpr() + ' ' + value.sexpr() + '))'
        serialized.append(equality)
        model_lines.append('(define-fun ' + variable.sexpr() + ' () ' + variable.sort().sexpr()
                           + ' ' + value.sexpr() + ')')
    # Build the parser's declaration environment once for the whole model.
    replay = z3.parse_smt2_string('\n'.join(serialized), decls=variables, ctx=imported.ctx)
    _need(len(replay) == len(values), 'serialized candidate assignment count changed')
    for (name, _), equality in zip(values.items(), replay):
        _need(z3.is_eq(equality) and equality.arg(0).eq(variables[name]),
              'serialized candidate assignment changed declaration')
        replay_values[name] = equality.arg(1)
    replayed = verify(replay_values)
    _need(replayed == checked, 'complete ground candidate serialization replay failed')
    signed, witness, extra = checked
    result = dict(schema='complete-target-witness-v1', status='sat', mode='source-witness-replay',
        equivalence_claimed=False, optimal=False, target_sha256=hashlib.sha256(data).hexdigest(),
        target_assertions=len(assertions), target_objectives=len(objectives),
        objective_directions=directions, objective_priority='lex', projection=projection,
        projection_coordinates=len(terms), all_target_assertions_retained=True,
        all_target_objectives_retained=True, limits=dict(timeout=None, memory=None),
        witness=witness, fixed_values=fixed_values, fixed_objectives=fixed_objectives,
        signed_objective_values=signed, original_objective_values=fixed_objectives,
        model_smt2='\n'.join(model_lines), target_witness_replay='sat',
        target_witness_replay_method='parse exact total assignments and evaluate every original assertion',
        feasibility_method='exact complete ground interpretation', solver_search_performed=False,
        ground_candidate_certificate=dict(all_original_assertions_true=len(assertions),
            serialized_replay_assertions_true=len(assertions), source_coordinates_rechecked=len(terms),
            original_objectives_rechecked=len(objectives), total_variables=len(variables),
            arbitrary_defaults_are_candidate_choices=True,
            serialized_assignments_smt2='\n'.join(serialized),
            original_assertion_sha256=[hashlib.sha256(term.sexpr().encode()).hexdigest()
                                       for term in assertions]))
    if auxiliary_candidate is not None:
        result.update(auxiliary_candidate=auxiliary_candidate, auxiliary_witness=extra,
            auxiliary_witness_replay='sat', auxiliary_attempt=dict(status='sat',
                origin=auxiliary_candidate['origin'], coordinates=len(auxiliary),
                fallback_to_public_witness=False, use='feasibility-only',
                method='exact complete ground interpretation'))
    return result
