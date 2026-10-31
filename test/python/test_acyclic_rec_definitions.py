"""Safe source normalization for retained but acyclic SMT helper definitions."""
import z3

from tools.semantic_checks.acyclic_rec_definitions import (
    normalize_acyclic_recursive_definitions,
)
from tools.semantic_checks.projection import free_constants


def test_acyclic_singleton_definition_becomes_exact_macro_and_keeps_formula():
    source = '''; comment mentioning define-fun-rec fake\n
(define-fun-rec sum_helper ((x Int) (y Int)) Int (+ x y))
(declare-const visible Int)
(assert (= visible (sum_helper 3 4)))
'''
    normalized = normalize_acyclic_recursive_definitions(source)
    assert normalized.count('(define-fun sum_helper') == 1
    assert normalized == source.replace(
        '(define-fun-rec sum_helper', '(define-fun sum_helper', 1)
    assert '(assert (= visible (sum_helper 3 4)))' in normalized
    for script in (source, normalized):
        context = z3.Context()
        assertions = list(z3.parse_smt2_string(script, ctx=context))
        visible = z3.Int('visible', ctx=context)
        solver = z3.Solver(ctx=context)
        solver.add(*assertions, visible != 7)
        assert solver.check() == z3.unsat


def test_indirect_cycle_through_ordinary_definition_is_retained():
    source = '''
(declare-fun loop_f (Int) Int)
(define-fun loop_g ((x Int)) Int (loop_f x))
(define-fun-rec loop_f ((x Int)) Int (loop_g x))
(assert (= (loop_f 0) 0))
'''
    assert normalize_acyclic_recursive_definitions(source) == source


def test_direct_recursion_is_retained():
    source = '''
(define-fun-rec countdown ((n Int)) Int
  (ite (<= n 0) 0 (+ 1 (countdown (- n 1)))))
(assert (= (countdown 2) 2))
'''
    assert normalize_acyclic_recursive_definitions(source) == source


def test_mutually_recursive_group_is_never_rewritten():
    source = '''
(define-funs-rec
  ((even ((n Int)) Bool) (odd ((n Int)) Bool))
  ((ite (= n 0) true (odd (- n 1)))
   (ite (= n 0) false (even (- n 1)))))
(assert (even 4))
'''
    assert normalize_acyclic_recursive_definitions(source) == source


def test_expanded_definition_keeps_global_constants_visible_to_projection():
    source = '''
(declare-const hidden_global Int)
(define-fun-rec acyclic_with_global ((x Int)) Int (+ x hidden_global))
(declare-const output Int)
(assert (= output (acyclic_with_global 2)))
'''
    normalized = normalize_acyclic_recursive_definitions(source)
    assert '(define-fun acyclic_with_global' in normalized
    assertions = list(z3.parse_smt2_string(normalized))
    names = {str(term.decl().name()) for term in free_constants(assertions)}
    assert names == {'hidden_global', 'output'}


def test_malformed_or_nontext_input_is_not_silently_rewritten():
    malformed = '(define-fun-rec broken ((x Int)) Int (+ x 1)'
    assert normalize_acyclic_recursive_definitions(malformed) == malformed
    try:
        normalize_acyclic_recursive_definitions(None)
    except TypeError as error:
        assert 'must be text' in str(error)
    else:
        raise AssertionError('non-text input should be rejected')
