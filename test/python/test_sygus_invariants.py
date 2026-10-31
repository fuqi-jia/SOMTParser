"""Bounded invariant synthesis retains initiation, consecution, and safety."""

import z3
import somtparser as sp


def solve(source):
    translated = sp.translate(source=source, language='sygus', profile='bmc',
                              options={'grammar_depth': '1'})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert translated.report.fidelity.sound
    assert not translated.report.fidelity.complete
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(translated.to_smt2()))
    verdict = solver.check()
    assert verdict != z3.unknown
    return translated, verdict


def problem(pre, trans, post, body='(< x 1)'):
    return ('(set-logic LIA) '
            f'(synth-inv inv ((x Int)) ((Start Bool ({body})))) '
            '(declare-primed-var x Int) '
            f'(define-fun pre ((a Int)) Bool {pre}) '
            f'(define-fun trans ((a Int) (b Int)) Bool {trans}) '
            f'(define-fun post ((a Int)) Bool {post}) '
            '(inv-constraint inv pre trans post) (check-synth)')


def test_invariant_elaboration_quantifies_current_and_primed_state():
    # The sole candidate is true, so all three obligations hold without asking
    # Z3 to solve a nontrivial quantified LIA/UF formula. This test checks the
    # universal current/primed-state binding; separate tests require each
    # obligation by making its single candidate UNSAT.
    translated, verdict = solve(problem('true', '(= b a)', 'true', 'true'))
    assert verdict == z3.sat
    smt = translated.to_smt2()
    assert '(forall ((x Int) (x! Int))' in smt


def test_sat_invariant_uses_boolean_default_grammar():
    source = ('(set-logic SAT) '
              '(synth-inv inv ((x Bool))) '
              '(declare-primed-var x Bool) '
              '(define-fun pre ((a Bool)) Bool (let ((q Bool a)) q)) '
              '(define-fun trans ((a Bool) (b Bool)) Bool (= b a)) '
              '(define-fun post ((a Bool)) Bool a) '
              '(inv-constraint inv pre trans post) (check-synth)')
    translated, verdict = solve(source)
    assert verdict == z3.sat
    assert '(forall ((x Bool) (x! Bool))' in translated.to_smt2()
    assert '((q Bool a))' not in translated.to_smt2()


def test_zero_arity_invariant_obligations_use_constant_symbols():
    source = ('(set-logic LIA) '
              '(synth-inv inv () ((Start Bool (true)))) '
              '(define-fun pre () Bool true) '
              '(define-fun trans () Bool true) '
              '(define-fun post () Bool true) '
              '(inv-constraint inv pre trans post) (check-synth)')
    translated, verdict = solve(source)
    assert verdict == z3.sat
    assert '(forall' not in translated.to_smt2()


def test_typed_let_sort_annotations_are_checked_before_lowering():
    common = ('(set-logic LIA) '
              '(synth-inv inv () ((Start Bool (true)))) '
              '{pre}'
              '(define-fun trans () Bool true) '
              '(define-fun post () Bool true) '
              '(inv-constraint inv pre trans post) (check-synth)')
    mismatches = (
        '(define-fun pre () Bool (let ((q Bool 1)) true)) ',
        '(define-fun pre () Bool (let ((q Int true)) true)) ',
    )
    for definition in mismatches:
        result = sp.translate(source=common.format(pre=definition), language='sygus',
                              profile='bmc', options={'grammar_depth': '1'})
        assert not result.ok
        assert any('typed let binding' in diagnostic.message
                   for diagnostic in result.diagnostic_items)

    shadowed = ('(define-fun pre ((outer Bool)) Bool '
                '(let ((outer ghost)) (let ((q Bool outer)) true))) ')
    result = sp.translate(source=common.format(pre=shadowed), language='sygus',
                          profile='bmc', options={'grammar_depth': '1'})
    assert not result.ok
    assert any('typed let binding' in diagnostic.message
               for diagnostic in result.diagnostic_items)


def test_initiation_obligation_is_required():
    # The only candidate is false; it is inductive and safe, but precondition
    # true does not imply it.
    _, verdict = solve(problem('true', '(= b a)', 'true', 'false'))
    assert verdict == z3.unsat


def test_consecution_obligation_is_required():
    # The only candidate x is initiated vacuously and is safe, but the
    # transition can move from x=0 to x=1.
    _, verdict = solve(problem('false', '(= b (+ a 1))', 'true', '(< x 1)'))
    assert verdict == z3.unsat


def test_safety_obligation_is_required():
    _, verdict = solve(problem('true', '(= b a)', 'false', 'true'))
    assert verdict == z3.unsat


def test_inv_constraint_rejects_wrong_signature_and_missing_primed_scope():
    wrong = problem('true', '(= b a)', 'true').replace(
        '(define-fun trans ((a Int) (b Int)) Bool',
        '(define-fun trans ((a Bool) (b Int)) Bool')
    translated = sp.translate(source=wrong, language='sygus', profile='bmc',
                              options={'grammar_depth': '1'})
    assert not translated.ok

    missing_prime = problem('true', '(= b a)', 'true').replace(
        '(declare-primed-var x Int)', '(declare-var x Int)')
    translated = sp.translate(source=missing_prime, language='sygus', profile='bmc',
                              options={'grammar_depth': '1'})
    assert not translated.ok

    wrong_arity = problem('true', '(= b a)', 'true').replace(
        '(define-fun trans ((a Int) (b Int)) Bool',
        '(define-fun trans ((a Int)) Bool')
    translated = sp.translate(source=wrong_arity, language='sygus', profile='bmc',
                              options={'grammar_depth': '1'})
    assert not translated.ok

    duplicate_parameter = problem('true', '(= b a)', 'true').replace(
        '((x Int))', '((x Int) (x Int))', 1)
    translated = sp.translate(source=duplicate_parameter, language='sygus', profile='bmc',
                              options={'grammar_depth': '1'})
    assert not translated.ok
