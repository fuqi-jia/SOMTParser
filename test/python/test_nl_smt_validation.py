"""Direct SMT proposals must pass native checks before repair can stop."""
import copy
import json

import pytest
import z3
import somtparser as sp
from somtparser.natural_language import Candidate


SOURCE = 'Choose an integer x between zero and three and maximize x.'
GOOD = '(declare-const x Int)(assert (and (>= x 0) (<= x 3)))(maximize x)(check-sat)'


def model(program=GOOD, decision='optimization'):
    return dict(schema='somt-nl-formal-v1', language='smtlib2', program=program,
                decision=decision, assumptions=[], unresolved=[],
                links=[dict(span=[0, len(SOURCE)], fragment=program)])


def propose(value):
    return sp.propose_nl(SOURCE, language='smtlib2', provider=lambda request: value)


@pytest.mark.parametrize('program', [
    '(declare-const x Int)(assert',
    '(assert (> undeclared 0))',
    '(declare-const x Int)(assert (and x true))',
    '(declare-const x Int)(assert (+ x 1))',
    '(declare-const b Bool)(minimize b)',
    '(assert true)(check-sat)(assert (> undeclared 0))',
])
def test_bad_program_is_invalid_before_compile(program):
    candidate = propose(model(program, 'satisfiability'))
    assert not candidate.valid
    assert candidate.diagnostics
    detail = candidate.diagnostic_details[0]
    assert detail['json_pointer'] == '/program'
    assert detail['value_present']
    assert not sp.compile_candidate(candidate, accept_digest=candidate.digest).ok


@pytest.mark.parametrize('program,decision', [
    ('(declare-const x Int)(assert (>= x 0))', 'optimization'),
    (GOOD, 'satisfiability'),
])
def test_decision_mismatch_is_repair_feedback(program, decision):
    candidate = propose(model(program, decision))
    assert not candidate.valid
    assert 'objectives disagree' in candidate.diagnostics[0]
    assert candidate.diagnostic_details[0]['json_pointer'] == '/decision'


@pytest.mark.parametrize('bad', [
    model('(declare-const x Int)(assert', 'optimization'),
    model('(declare-const x Int)(assert (and x true))(maximize x)'),
    model(GOOD, 'satisfiability'),
])
def test_repair_reaches_program_errors_and_preserves_the_task(bad):
    requests = []
    context = {'domain': 'Mathematical integers; exact stated objective.'}

    def provider(request):
        requests.append(copy.deepcopy(request))
        return bad if len(requests) == 1 else model()

    trace = sp.propose_nl_with_repair(SOURCE, language='smtlib2', provider=provider,
                                    context=context, max_attempts=3)
    assert len(trace.attempts) == 2
    assert not trace.attempts[0].valid and trace.attempts[1].valid
    assert len(requests) == 2
    assert requests[0]['source'] == requests[1]['source'] == SOURCE
    assert requests[0]['context'] == requests[1]['context'] == context
    assert requests[0]['schema'] == requests[1]['schema']
    assert requests[1]['repair']['previous_candidate'] == bad
    assert requests[1]['repair']['previous_digest'] == trace.attempts[0].digest
    assert requests[1]['repair']['diagnostic_details'][0]['json_pointer'] in ('/program', '/decision')
    candidate = trace.attempts[-1]
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert result.ok, result.diagnostics
    solver = z3.Optimize()
    solver.from_string(result.to_smt2())
    assert solver.check() == z3.sat
    assert solver.model().eval(z3.Int('x')).as_long() == 3
    assert result.report()['intent_preservation'] == 'not-proved'


def test_invalid_program_exhausts_the_declared_retry_budget():
    calls = []

    def provider(request):
        calls.append(request)
        return model('(assert missing)', 'satisfiability')

    trace = sp.propose_nl_with_repair(SOURCE, language='smtlib2', provider=provider,
                                    max_attempts=2)
    assert len(calls) == len(trace.attempts) == 2
    assert not any(c.valid for c in trace.attempts)


def test_valid_unsatisfiable_program_is_accepted_without_solver(monkeypatch):
    def forbidden(*args, **kwargs):
        raise AssertionError('proposal validation must not solve')

    monkeypatch.setattr(z3.Solver, 'check', forbidden)
    monkeypatch.setattr(z3.Optimize, 'check', forbidden)
    assert propose(model('(assert false)(check-sat)', 'satisfiability')).valid


def test_compile_reuses_its_checked_translation_and_requested_options(monkeypatch):
    candidate = propose(model())
    calls = []
    original = sp.translate

    def translate(*args, **kwargs):
        calls.append(kwargs)
        return original(*args, **kwargs)

    monkeypatch.setattr(sp, 'translate', translate)
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest,
                                  profile='bv32', dialect=sp.OmtDialect.Z3)
    assert result.ok, result.diagnostics
    assert len(calls) == 1
    assert calls[0]['profile'] == 'bv32' and calls[0]['dialect'] == sp.OmtDialect.Z3
    assert result.translation.report.fidelity.bounds
    calls.clear()
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest,
                                  dialect=sp.OmtDialect.NONE)
    assert not result.ok and result.diagnostics
    assert len(calls) == 1 and calls[0]['dialect'] == sp.OmtDialect.NONE


def test_saved_and_directly_constructed_snapshots_cannot_bypass_checks():
    candidate = propose(model())
    restored = Candidate.from_json(candidate.to_json())
    assert restored.valid and restored.digest == candidate.digest
    assert not sp.compile_candidate(restored, accept_digest='wrong').ok
    bad = model('(assert missing)', 'satisfiability')
    bad['context'] = {}
    forged = Candidate(SOURCE, json.dumps(bad), 'external:test', ())
    result = sp.compile_candidate(forged, accept_digest=forged.digest)
    assert not result.ok and result.diagnostics


def test_soft_objective_counts_as_optimization():
    program = '(declare-const b Bool)(assert-soft b :weight 3)(check-sat)'
    candidate = propose(model(program))
    assert candidate.valid, candidate.diagnostics
    assert not propose(model(program, 'satisfiability')).valid
