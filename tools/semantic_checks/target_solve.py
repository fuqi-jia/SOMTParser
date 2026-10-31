"""Solve a complete target and replay explicit source-coordinate witnesses.

This is an execution check, not an equivalence certificate. The caller must
justify the complete source-coordinate map and independently check the target
witness in the original source model. No timeout or memory budget is imposed.
"""
import hashlib
import re

import z3

from .source_oracles.target_relation import read_target


def _need(condition, message):
    if not condition:
        raise ValueError(message)


def encode_value(value):
    """Use exact values, including complete finite sets rather than samples."""
    value = z3.simplify(value)
    if z3.is_true(value) or z3.is_false(value):
        return dict(type='bool', value=z3.is_true(value))
    if z3.is_int_value(value):
        return dict(type='int', value=str(value.as_long()))
    if z3.is_rational_value(value):
        return dict(type='real', numerator=str(value.numerator_as_long()),
                    denominator=str(value.denominator_as_long()))
    if (z3.is_array(value) and value.sort().domain().kind() == z3.Z3_INT_SORT
            and value.sort().range().kind() == z3.Z3_BOOL_SORT):
        entries = {}
        while z3.is_store(value):
            key, present = z3.simplify(value.arg(1)), z3.simplify(value.arg(2))
            _need(z3.is_int_value(key), 'nonliteral set index')
            _need(z3.is_true(present) or z3.is_false(present), 'nonliteral set membership')
            entries.setdefault(key.as_long(), z3.is_true(present))
            value = value.arg(0)
        _need(z3.is_const_array(value) and z3.is_false(z3.simplify(value.arg(0))),
              'set witness has no explicit finite false-default representation')
        return dict(type='set-int', elements=[str(key) for key in sorted(entries)
                                            if entries[key]])
    raise ValueError('witness value is not an exact supported scalar or finite set')


def _integer(text):
    _need(isinstance(text, str) and re.fullmatch(r'0|-?[1-9][0-9]*', text),
          'integer witness must be canonical decimal text')
    return int(text)


def decode_value(record, sort):
    _need(isinstance(record, dict), 'witness value must be a typed record')
    kind = record.get('type')
    if kind == 'bool':
        _need(set(record) == {'type', 'value'} and type(record['value']) is bool
              and sort.kind() == z3.Z3_BOOL_SORT, 'Boolean witness sort/shape')
        return z3.BoolVal(record['value'], ctx=sort.ctx)
    if kind == 'int':
        _need(set(record) == {'type', 'value'} and sort.kind() == z3.Z3_INT_SORT,
              'integer witness sort/shape')
        return z3.IntVal(_integer(record['value']), ctx=sort.ctx)
    if kind == 'real':
        _need(set(record) == {'type', 'numerator', 'denominator'}
              and sort.kind() == z3.Z3_REAL_SORT, 'real witness sort/shape')
        numerator, denominator = _integer(record['numerator']), _integer(record['denominator'])
        _need(denominator > 0, 'real witness denominator must be positive')
        return z3.RealVal(str(numerator) + '/' + str(denominator), ctx=sort.ctx)
    if kind == 'set-int':
        _need(set(record) == {'type', 'elements'} and isinstance(record['elements'], list)
              and sort.kind() == z3.Z3_ARRAY_SORT
              and sort.domain().kind() == z3.Z3_INT_SORT
              and sort.range().kind() == z3.Z3_BOOL_SORT, 'set witness sort/shape')
        elements = [_integer(item) for item in record['elements']]
        _need(elements == sorted(set(elements)), 'set witness elements must be sorted and unique')
        value = z3.K(sort.domain(), z3.BoolVal(False, ctx=sort.ctx))
        for element in elements:
            value = z3.SetAdd(value, z3.IntVal(element, ctx=sort.ctx))
        return value
    raise ValueError('unsupported witness value type')


def projection_terms(variables, projection):
    _need(isinstance(projection, list), 'projection must be an explicit list')
    terms = {}
    for row in projection:
        _need(isinstance(row, dict) and set(row) <= {'id', 'symbol', 'indices', 'source_name', 'source_indices'}
              and {'id', 'symbol'} <= set(row), 'projection row shape')
        identity, symbol = row['id'], row['symbol']
        _need(isinstance(identity, str) and identity and identity not in terms,
              'projection identities must be nonempty and unique')
        _need(isinstance(symbol, str) and symbol in variables,
              'projection symbol absent from complete target')
        if 'source_name' in row:
            _need(row['source_name'] == symbol, 'source name metadata differs from mapped symbol')
        if 'source_indices' in row:
            _need(isinstance(row['source_indices'], list)
                  and all(type(index) is int for index in row['source_indices']),
                  'source index metadata must be an integer list')
        term = variables[symbol]
        indices = row.get('indices', [])
        _need(isinstance(indices, list), 'projection indices must be a list')
        for index in indices:
            _need(type(index) is int and z3.is_array(term)
                  and term.sort().domain().kind() == z3.Z3_INT_SORT,
                  'projection requires an explicit integer array coordinate')
            term = z3.Select(term, z3.IntVal(index, ctx=term.ctx))
        terms[identity] = term
    return terms


def _objective_records(model, objectives, directions):
    signed = [model.eval(term, model_completion=True) for term in objectives]
    original = [value if direction == 'minimize' else -value
                for value, direction in zip(signed, directions)]
    return signed, [encode_value(value) for value in signed], [encode_value(value) for value in original]


def _auxiliary_terms(variables, projection, candidate):
    """Decode optional search suggestions; never extend public observables."""
    if candidate is None:
        return {}, []
    _need(isinstance(candidate, dict) and set(candidate) == {'projection', 'values', 'origin'},
          'auxiliary candidate requires projection, values, and origin')
    _need(isinstance(candidate['origin'], str) and bool(candidate['origin']),
          'auxiliary candidate origin must be nonempty text')
    extra = projection_terms(variables, candidate['projection'])
    public_symbols = {row['symbol'] for row in projection}
    _need(all(row['symbol'] not in public_symbols for row in candidate['projection']),
          'auxiliary candidate may only refer to symbols outside public projection')
    _need(isinstance(candidate['values'], dict) and set(candidate['values']) == set(extra),
          'auxiliary candidate must cover every auxiliary coordinate')
    fixed = [term == decode_value(candidate['values'][key], term.sort())
             for key, term in extra.items()]
    return extra, fixed


def _check_auxiliary(solver, fixed, candidate, event):
    """Try extra feasibility equalities, then discard unsuccessful suggestions."""
    if candidate is None:
        return solver.check(), None
    solver.push()
    solver.add(*fixed)
    event('auxiliary-candidate', event='started', origin=candidate['origin'])
    answer = solver.check()
    attempt = dict(origin=candidate['origin'], status=str(answer),
                   coordinates=len(fixed), fallback_to_public_witness=answer != z3.sat,
                   use='feasibility-only')
    if answer == z3.unknown:
        attempt['reason_unknown'] = solver.reason_unknown()
    event('auxiliary-candidate', event='completed', answer=str(answer))
    if answer == z3.sat:
        return answer, attempt
    solver.pop()
    event('auxiliary-candidate-fallback', event='started')
    answer = solver.check()
    event('auxiliary-candidate-fallback', event='completed', answer=str(answer))
    attempt['fallback_status'] = str(answer)
    return answer, attempt


def solve_target(data, projection, *, fixed_values=None, fixed_objectives=None,
                 auxiliary_candidate=None, ground_candidate=False, progress_callback=None,
                 candidate_callback=None):
    """Solve all assertions/objectives, or replay a complete supplied witness.

    `indices` are actual SMT coordinates supplied by a separately checked map.
    Fixed optimization witnesses must include ALL original, ordered objectives.
    Target optimality requires exact finite attained lower and upper bounds.
    The returned target witness is also rechecked with all target assertions.
    Auxiliary candidates provide typed values for non-public symbols ONLY in
    fixed-witness feasibility checks. An UNSAT/unknown suggestion is discarded
    before retrying the original public witness. They never assert optimality.
    An optional candidate_callback receives plain-data incumbent snapshots while
    Optimize continues searching. These are unverified candidates, not optimal
    results: replay them separately against all assertions and the source model.
    Returning False disables further snapshots without stopping optimization.
    The callback must not invoke a solver in this active Z3 context. Its errors
    are re-raised after check() returns, rather than escaping through a C callback.
    """
    _need(isinstance(data, bytes), 'target must be complete SMT-LIB bytes')
    def event(phase, **details):
        if progress_callback is not None:
            progress_callback(dict(phase=phase, **details))
    event('target-parse', event='started')
    variables, imported, directions = read_target(data)
    assertions, objectives = list(imported.assertions()), list(imported.objectives())
    terms = projection_terms(variables, projection)
    _need(candidate_callback is None or callable(candidate_callback),
          'candidate callback must be callable')
    _need(candidate_callback is None or (bool(objectives) and fixed_values is None),
          'intermediate candidates require independent target optimization')
    event('target-parse', event='completed', assertions=len(assertions), objectives=len(objectives))
    result = dict(schema='complete-target-witness-v1', equivalence_claimed=False,
                  target_sha256=hashlib.sha256(data).hexdigest(),
                  target_assertions=len(assertions), target_objectives=len(objectives),
                  objective_directions=directions, objective_priority='lex',
                  projection=projection, projection_coordinates=len(terms),
                  all_target_assertions_retained=True, all_target_objectives_retained=True,
                  limits=dict(timeout=None, memory=None), optimal=False)
    _need(auxiliary_candidate is None or fixed_values is not None,
          'auxiliary candidates require a fixed public feasibility witness')
    auxiliary, auxiliary_fixed = _auxiliary_terms(variables, projection, auxiliary_candidate)
    handles, fixed = [], []
    if fixed_values is not None:
        _need(isinstance(fixed_values, dict) and set(fixed_values) == set(terms),
              'fixed witness must cover exactly every projection coordinate')
        fixed = [term == decode_value(fixed_values[key], term.sort()) for key, term in terms.items()]
        _need(isinstance(fixed_objectives, list) and len(fixed_objectives) == len(objectives),
              'fixed witness must include all ordered objective values (empty list for SAT)')
        for term, direction, record in zip(objectives, directions, fixed_objectives):
            original = term if direction == 'minimize' else -term
            fixed.append(original == decode_value(record, original.sort()))
        solver = z3.Solver(ctx=imported.ctx)
        result['mode'] = 'source-witness-replay'
    elif objectives:
        _need(fixed_objectives is None, 'objective values require a fixed witness')
        solver = z3.Optimize(ctx=imported.ctx)
        solver.set(priority='lex')
        # Optimize.objectives() already negates maximization expressions.
        handles = [solver.minimize(term) for term in objectives]
        result['mode'] = 'target-optimization'
    else:
        _need(fixed_objectives is None, 'objective values require a fixed witness')
        solver = z3.Solver(ctx=imported.ctx)
        result['mode'] = 'target-satisfiability'
    if ground_candidate and fixed_values is not None:
        from .ground_candidate import verify_ground_candidate
        event('ground-candidate-evaluation', event='started')
        verified = verify_ground_candidate(data, projection, fixed_values, fixed_objectives,
                                           auxiliary_candidate)
        event('ground-candidate-evaluation', event='completed', accepted=verified is not None)
        if verified is not None:
            return verified
    solver.add(*assertions, *fixed)
    candidate_state = dict(emitted=0, skipped=0, enabled=True)
    callback_errors = []
    if candidate_callback is not None:
        _need(hasattr(solver, 'set_on_model'), 'installed Z3 lacks optimization model callbacks')

        def on_candidate(candidate_model):
            # Z3 owns this model only during the callback. Materialize exact
            # Python values now; no ModelRef or AST may escape its lifetime.
            if callback_errors or not candidate_state['enabled']:
                return
            try:
                try:
                    values = {key: encode_value(candidate_model.eval(term, model_completion=True))
                              for key, term in terms.items()}
                    _, signed_costs, original_costs = _objective_records(candidate_model, objectives, directions)
                except (ValueError, z3.Z3Exception) as error:
                    # A provisional model can lack an exportable finite set.
                    # Do not publish a partial witness or change final solving.
                    candidate_state['skipped'] += 1
                    candidate_state['last_skip_reason'] = str(error)
                    return
                candidate_state['emitted'] += 1
                snapshot = dict(schema='complete-target-candidate-v1', status='candidate',
                    sequence=candidate_state['emitted'], target_sha256=result['target_sha256'],
                    witness=values, signed_objective_values=signed_costs,
                    original_objective_values=original_costs, objective_directions=list(directions),
                    objective_priority='lex', projection_coordinates=len(terms),
                    target_assertions=len(assertions), target_objectives=len(objectives),
                    all_target_assertions_retained=True, all_target_objectives_retained=True,
                    independent_target_search=True, optimal=False,
                    target_witness_replay='pending', equivalence_claimed=False)
                if candidate_callback(snapshot) is False:
                    candidate_state['enabled'] = False
            except BaseException as error:
                # ctypes would otherwise print and swallow callback failures.
                callback_errors.append(error)

        solver.set_on_model(on_candidate)
    event('target-solve', event='started', mode=result['mode'])
    answer, auxiliary_attempt = _check_auxiliary(solver, auxiliary_fixed, auxiliary_candidate, event)
    if callback_errors:
        raise callback_errors[0]
    if candidate_callback is not None:
        result['candidate_output'] = candidate_state
    if auxiliary_candidate is not None:
        result.update(auxiliary_candidate=auxiliary_candidate, auxiliary_attempt=auxiliary_attempt)
    event('target-solve', event='completed', answer=str(answer))
    result['status'] = str(answer)
    if answer == z3.unknown:
        result['reason_unknown'] = solver.reason_unknown()
    if answer != z3.sat:
        return result
    model = solver.model()
    witness = {key: encode_value(model.eval(term, model_completion=True)) for key, term in terms.items()}
    result['witness'] = witness
    auxiliary_witness = None
    if auxiliary_candidate is not None:
        try:
            auxiliary_witness = {key: encode_value(model.eval(term, model_completion=True))
                                 for key, term in auxiliary.items()}
        except ValueError as error:
            # A rejected finite-set hint can fall back to a perfectly valid
            # infinite hidden set. Optional hints must not make an otherwise
            # supported public witness unreportable.
            if not auxiliary_attempt['fallback_to_public_witness']:
                raise
            result['auxiliary_serialization_skipped'] = str(error)
        if auxiliary_witness is not None:
            result['auxiliary_witness'] = auxiliary_witness
    values, signed, original = _objective_records(model, objectives, directions)
    result['model_smt2'] = model.sexpr()
    result.update(signed_objective_values=signed, original_objective_values=original)
    if handles:
        bounds, attained = [], True
        for handle, value in zip(handles, values):
            lower, upper = handle.lower(), handle.upper()
            finite = all(z3.is_int_value(v) or z3.is_rational_value(v) for v in (lower, upper, value))
            exact = finite and z3.is_true(z3.simplify(lower == upper)) and z3.is_true(z3.simplify(lower == value))
            bounds.append(dict(lower_smt2=lower.sexpr(), upper_smt2=upper.sexpr(), finite_attained=bool(exact)))
            attained = attained and exact
        result.update(optimal=bool(attained), objective_bounds=bounds)
    # Replay the exported, exact values, including ordered costs. This also
    # catches any serialization or coordinate-mapping bug before cross-check.
    replay = z3.Solver(ctx=imported.ctx)
    replay.add(*assertions)
    replay.add(*(term == decode_value(witness[key], term.sort()) for key, term in terms.items()))
    replay.add(*(term == decode_value(record, term.sort()) for term, record in zip(objectives, signed)))
    # Reconstruct every auxiliary value actually returned by the model, even
    # when the original suggestion failed. All original assertions remain.
    if auxiliary_witness is not None:
        replay.add(*(term == decode_value(auxiliary_witness[key], term.sort())
                     for key, term in auxiliary.items()))
    event('target-witness-replay', event='started')
    replay_answer = replay.check()
    event('target-witness-replay', event='completed', answer=str(replay_answer))
    result['target_witness_replay'] = str(replay_answer)
    if auxiliary_candidate is not None:
        result['auxiliary_witness_replay'] = (str(replay_answer) if auxiliary_witness is not None
                                              else 'not-applicable-after-candidate-fallback')
    if replay_answer == z3.unknown:
        result['target_witness_replay_reason_unknown'] = replay.reason_unknown()
    if fixed_values is not None:
        # Return exactly the supplied values, not an alternative successful
        # assignment, as the inputs bound by the replay evidence.
        result.update(fixed_values=fixed_values, fixed_objectives=fixed_objectives)
    return result
