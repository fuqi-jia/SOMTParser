"""Default LIA grammar holes preserve arbitrary integer constants."""

import re

import z3
import somtparser as sp


def translate(source, depth='1'):
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': depth})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and not result.report.fidelity.complete
    return result


def check(result):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    verdict = solver.check()
    assert verdict != z3.unknown
    return verdict


def test_default_lia_can_choose_an_arbitrary_integer_constant():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int) '
              '(declare-var x Int) '
              '(constraint (= (f x) 17)) '
              '(check-synth)')
    assert check(translate(source)) == z3.sat


def test_default_nia_grammar_contains_nonlinear_integer_products():
    source = ('(set-logic NIA) '
              '(synth-fun square ((x Int)) Int) '
              '(declare-var x Int) '
              '(constraint (= (square x) (* x x))) '
              '(check-synth)')
    assert check(translate(source)) == z3.sat


def test_default_lia_constant_is_shared_across_all_source_constraints():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int) '
              '(declare-var x Int) '
              '(constraint (= (f x) 17)) '
              '(constraint (= (f x) 18)) '
              '(check-synth)')
    assert check(translate(source)) == z3.unsat


def test_two_constant_occurrences_are_independent_and_shared_across_calls():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int '
              '((Start Int) (C Int)) '
              '((Start Int ((+ (* C x) C))) (C Int ((Constant Int))))) '
              '(declare-var x Int) '
              '(constraint (= (f 0) 17)) '
              '(constraint (= (f 1) 19)) '
              '(check-synth)')
    assert check(translate(source)) == z3.sat

    contradictory = source.replace(
        '(check-synth)', '(constraint (= (f 1) 20)) (check-synth)')
    assert check(translate(contradictory)) == z3.unsat


def test_negative_integer_constant_is_a_positive_hole_under_unary_minus():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int '
              '((Start Int) (C Int)) '
              '((Start Int ((- C))) (C Int ((Constant Int))))) '
              '(declare-var x Int) '
              '(constraint (= (f x) (- 17))) '
              '(check-synth)')
    assert check(translate(source)) == z3.sat


def test_constant_only_grammar_does_not_admit_negative_numerals():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int '
              '((Start Int) (C Int)) '
              '((Start Int ((Constant Int))) (C Int ((Constant Int))))) '
              '(declare-var x Int) '
              '(constraint (= (f x) (- 17))) '
              '(check-synth)')
    assert check(translate(source)) == z3.unsat


def test_default_grammar_nonterminals_do_not_capture_formal_names():
    source = ('(set-logic LIA) '
              '(synth-fun f ((I Int) (C Int) (B Bool)) Int) '
              '(declare-var I Int) (declare-var C Int) (declare-var B Bool) '
              '(constraint (= (f I C B) I)) '
              '(check-synth)')
    assert check(translate(source, depth='0')) == z3.sat


def test_legacy_grouped_int_bool_grammar_is_normalized_and_semantic():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int '
              '((Start Int ((ite Pred Value Value))) '
              '(Value Int (0 1)) '
              '(Pred Bool ((<= x 0) true)))) '
              '(declare-var x Int) '
              '(constraint (= (f x) (ite (<= x 0) 0 1))) '
              '(check-synth)')
    assert check(translate(source, depth='1')) == z3.sat


def test_malformed_legacy_grouped_grammar_is_rejected():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int '
              '((Start Int (x)) (Pred Bool true))) '
              '(declare-var x Int) (constraint (= (f x) x)) (check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert 'malformed grouped grammar rule listing' in result.diagnostic_items[0].message


def test_four_selectors_are_exactly_one_for_all_assignments():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int '
              '((Start Int)) ((Start Int (0 1 2 3)))) '
              '(declare-var x Int) '
              '(constraint (= (f x) (f x))) '
              '(check-synth)')
    result = translate(source, depth='0')
    selector_names = re.findall(
        r'\(declare-fun (__somt_sygus_candidate_[^ ]+) \(\) Bool\)',
        result.to_smt2())
    assert len(selector_names) == 4
    assertions = z3.parse_smt2_string(result.to_smt2())
    for mask in range(1 << len(selector_names)):
        solver = z3.Solver()
        solver.add(*assertions)
        solver.add(*[
            z3.Bool(name) == bool(mask & (1 << index))
            for index, name in enumerate(selector_names)
        ])
        expected = z3.sat if bin(mask).count("1") == 1 else z3.unsat
        assert solver.check() == expected, f'selector assignment {mask:04b}'


def test_define_fun_helper_semantics_are_checked_by_z3():
    source = ('(set-logic LIA) '
              '(define-fun successor ((v Int)) Int (+ v 1)) '
              '(synth-fun f ((x Int)) Int ((Start Int)) ((Start Int (x)))) '
              '(declare-var x Int) '
              '(constraint (= (successor x) (f x))) '
              '(check-synth)')
    assert check(translate(source, depth='0')) == z3.unsat


def test_define_fun_helper_can_call_the_synthesized_function():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int ((Start Int)) ((Start Int (x)))) '
              '(define-fun twice ((v Int)) Int (* 2 (f v))) '
              '(declare-var x Int) '
              '(constraint (= (twice x) 2)) '
              '(check-synth)')
    result = translate(source, depth='0')
    assert '(f v)' not in result.to_smt2()
    assert check(result) == z3.unsat


def test_define_fun_parameters_can_shadow_the_synthesized_name():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int ((Start Int)) ((Start Int (x)))) '
              '(define-fun add-shadow ((x Int) (f Int)) Int (+ x f)) '
              '(declare-var x Int) '
              '(constraint (= (add-shadow (f x) 3) (+ x 3))) '
              '(check-synth)')
    assert check(translate(source, depth='0')) == z3.sat


def test_recursive_define_fun_is_rejected():
    source = ('(set-logic LIA) '
              '(synth-fun f ((x Int)) Int ((Start Int)) ((Start Int (x)))) '
              '(define-fun rec ((x Int)) Int (rec x)) '
              '(declare-var x Int) '
              '(constraint (= (f x) x)) '
              '(check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert 'recursive SyGuS define-fun' in result.diagnostic_items[0].message
