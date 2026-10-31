"""Explicit SyGuS bit-vector grammars preserve SMT bit-vector semantics."""

import z3
from itertools import product
import pytest
import somtparser as sp


def translate(source, depth='1'):
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': depth})
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    assert result.report.fidelity.sound
    assert not result.report.fidelity.complete
    return result


def eliminate_finite_quantifiers(expr):
    # An exact test oracle: every value of each small BV sort is instantiated.
    # The production translator keeps its quantified formula unchanged.
    if z3.is_quantifier(expr):
        sorts = [expr.var_sort(i) for i in range(expr.num_vars())]
        assert all(z3.is_bv_sort(sort) for sort in sorts)
        assert sum(sort.size() for sort in sorts) <= 8
        terms = []
        for values in product(*(range(1 << sort.size()) for sort in sorts)):
            replacements = [z3.BitVecVal(value, sort) for value, sort in zip(values, sorts)]
            terms.append(eliminate_finite_quantifiers(
                z3.substitute_vars(expr.body(), *reversed(replacements))))
        return z3.And(*terms) if expr.is_forall() else z3.Or(*terms)
    if expr.num_args() == 0:
        return expr
    return expr.decl()(*(eliminate_finite_quantifiers(arg) for arg in expr.children()))


def check(result, finite=False):
    solver = z3.Solver()
    solver.set(timeout=10000)
    assertions = z3.parse_smt2_string(result.to_smt2())
    solver.add([eliminate_finite_quantifiers(a) for a in assertions] if finite else assertions)
    verdict = solver.check()
    assert verdict != z3.unknown
    return verdict


def test_explicit_bv_arithmetic_grammar_keeps_fixed_width_semantics():
    source = ('(set-logic BV) '
              '(synth-fun successor ((x (_ BitVec 8))) (_ BitVec 8) '
              '((Start (_ BitVec 8))) '
              '((Start (_ BitVec 8) ((bvadd x #x01))))) '
              '(declare-var x (_ BitVec 8)) '
              '(constraint (= (successor x) (bvadd x #x01))) '
              '(check-synth)')
    result = translate(source, depth='0')
    assert '(_ BitVec 8)' in result.to_smt2()
    assert 'bvadd' in result.to_smt2()
    assert check(result) == z3.sat


def test_left_associative_bv_operators_accept_three_equal_width_operands():
    source = ('(set-logic BV) '
              '(synth-fun triple ((x (_ BitVec 8))) (_ BitVec 8) '
              '((Start (_ BitVec 8))) '
              '((Start (_ BitVec 8) ((bvadd x x x))))) '
              '(declare-var x (_ BitVec 8)) '
              '(constraint (= (triple x) (bvadd x x x))) '
              '(check-synth)')
    result = translate(source, depth='0')
    assert 'bvadd' in result.to_smt2()
    assert check(result) == z3.sat


def test_bv_constant_holes_remain_bv_sorted_in_the_candidate_relation():
    source = ('(set-logic BV) '
              '(synth-fun magic ((x (_ BitVec 8))) (_ BitVec 8) '
              '((Start (_ BitVec 8)) (C (_ BitVec 8))) '
              '((Start (_ BitVec 8) (C)) '
              '(C (_ BitVec 8) ((Constant (_ BitVec 8)))))) '
              '(declare-var x (_ BitVec 8)) '
              '(constraint (= (magic x) #x2a)) '
              '(check-synth)')
    result = translate(source, depth='1')
    assert '(_ BitVec 8)' in result.to_smt2()
    assert 'int2bv' not in result.to_smt2()
    assert check(result) == z3.sat


def test_multiple_synthesized_bv_functions_share_one_coupled_relation():
    def benchmark(expected):
        return ('(set-logic BV) '
                '(synth-fun left () (_ BitVec 8) '
                '((Start (_ BitVec 8))) '
                '((Start (_ BitVec 8) (#x00 #x01)))) '
                '(synth-fun right () (_ BitVec 8) '
                '((Start (_ BitVec 8))) '
                '((Start (_ BitVec 8) (#x00 #x01)))) '
                '(constraint (= (bvadd left right) #x' + expected + ')) '
                '(check-synth)')

    # Each synthesized function has its own exactly-one grammar selector, but
    # the shared equation couples both wrappers in the same target formula.
    assert check(translate(benchmark('01'), depth='0')) == z3.sat
    # The only possible sum of the two allowed constants is 0, 1, or 2.
    assert check(translate(benchmark('03'), depth='0')) == z3.unsat


def test_default_bv_grammar_matches_the_documented_b3_operator_fragment():
    source = ('(set-logic BV) '
              '(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)) '
              '(declare-var x (_ BitVec 8)) '
              '(constraint (= (f x) (bvadd x #x01))) '
              '(check-synth)')
    result = translate(source, depth='1')
    text = result.to_smt2()
    assert '__somt_sygus_function_0' not in text
    assert 'bvudiv' in text and 'bvlshr' in text
    assert check(result) == z3.sat


def test_default_bv_boolean_grammar_includes_signed_and_unsigned_comparisons():
    source = ('(set-logic BV) '
              '(synth-fun pred ((x (_ BitVec 8))) Bool) '
              '(declare-var x (_ BitVec 8)) '
              '(constraint (= (pred x) (bvslt x #x80))) '
              '(check-synth)')
    result = translate(source, depth='1')
    text = result.to_smt2()
    assert all(operator in text for operator in
               ('bvult', 'bvule', 'bvugt', 'bvuge',
                'bvslt', 'bvsle', 'bvsgt', 'bvsge'))
    assert check(result) == z3.sat


@pytest.mark.parametrize(
    "operator,expected,verdict",
    [('bvult', 'true', z3.sat), ('bvslt', 'false', z3.sat),
     ('bvult', 'false', z3.unsat), ('bvslt', 'true', z3.unsat)],
)
def test_signed_and_unsigned_bv_comparisons_have_boolean_result(
    operator, expected, verdict
):
    source = ('(set-logic BV) '
              '(synth-fun pred ((x (_ BitVec 8))) Bool '
              '((Start Bool)) '
              '((Start Bool ((' + operator + ' x #x80))))) '
              '(constraint (= (pred #x7f) ' + expected + ')) '
              '(check-synth)')
    assert check(translate(source, depth='0')) == verdict


@pytest.mark.parametrize(
    "high,low,width,accepted",
    [('7', '0', 8, True), ('0', '0', 1, True),
     ('8', '0', 9, False), ('3', '4', 1, False)],
)
def test_extract_bounds_match_input_width_and_nonempty_slice(high, low, width, accepted):
    source = ('(set-logic BV) '
              '(synth-fun nibble ((x (_ BitVec 8))) (_ BitVec ' + str(width) + ') '
              '((Start (_ BitVec ' + str(width) + '))) '
              '((Start (_ BitVec ' + str(width) + ') '
              '(((_ extract ' + high + ' ' + low + ') x))))) '
              '(check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert result.ok == accepted


def test_concat_rejects_result_width_overflow_before_target_lowering():
    source = ('(set-logic BV) '
              '(synth-fun join ((x (_ BitVec 4294967295)) (y (_ BitVec 1))) '
              '(_ BitVec 1) ((Start (_ BitVec 1))) '
              '((Start (_ BitVec 1) ((concat x y))))) '
              '(check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any('concat result width overflows' in d.message
               for d in result.diagnostic_items)


@pytest.mark.parametrize("expected,verdict", [("2", z3.sat), ("3", z3.unsat)])
def test_indexed_extract_production_checks_and_preserves_result_width(expected, verdict):
    source = ('(set-logic BV) '
              '(synth-fun high_nibble ((x (_ BitVec 8))) (_ BitVec 4) '
              '((Start (_ BitVec 4))) '
              '((Start (_ BitVec 4) (((_ extract 7 4) x))))) '
              '(declare-var x (_ BitVec 8)) '
              '(constraint (= (high_nibble #x2a) #x' + expected + ')) '
              '(check-synth)')
    result = translate(source, depth='0')
    assert check(result) == verdict


@pytest.mark.parametrize("expected,verdict", [("42", z3.sat), ("43", z3.unsat)])
def test_indexed_bv_numeral_is_a_typed_grammar_terminal(expected, verdict):
    source = ('(set-logic BV) '
              '(synth-fun constant ((x (_ BitVec 8))) (_ BitVec 8) '
              '((Start (_ BitVec 8))) '
              '((Start (_ BitVec 8) ((_ bv42 8))))) '
              '(constraint (= (constant #x00) (_ bv' + expected + ' 8))) '
              '(check-synth)')
    result = translate(source, depth='0')
    assert check(result) == verdict


def test_bv_grammar_rejects_width_mismatched_operator_arguments():
    source = ('(set-logic BV) '
              '(synth-fun bad ((x (_ BitVec 8)) (wide (_ BitVec 16))) (_ BitVec 8) '
              '((Start (_ BitVec 8))) '
              '((Start (_ BitVec 8) ((bvadd x wide))))) '
              '(check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any('equal-width bit-vector operands' in diagnostic.message
               for diagnostic in result.diagnostic_items)


def test_indexed_bv_literal_reduces_modulo_its_declared_width():
    source = ('(set-logic BV) '
              '(synth-fun wraps ((x (_ BitVec 8))) (_ BitVec 8) '
              '((Start (_ BitVec 8))) '
              '((Start (_ BitVec 8) ((_ bv256 8))))) '
              '(constraint (= (wraps #x00) #x00)) '
              '(check-synth)')
    result = translate(source, depth='0')
    assert check(result) == z3.sat


def test_bitvector_sort_and_index_reject_signed_decimal_spellings():
    malformed = [
        '(set-logic BV) (synth-fun f ((x (_ BitVec +8))) (_ BitVec 8) '
        '((Start (_ BitVec 8))) ((Start (_ BitVec 8) (x)))) (check-synth)',
        '(set-logic BV) (synth-fun f ((x (_ BitVec 8))) (_ BitVec 4) '
        '((Start (_ BitVec 4))) '
        '((Start (_ BitVec 4) (((_ extract +7 4) x))))) (check-synth)',
    ]
    for source in malformed:
        result = sp.translate(source=source, language='sygus', profile='bmc',
                              options={'grammar_depth': '0'})
        assert not result.ok


@pytest.mark.parametrize("increment,expected", [("01", z3.sat), ("02", z3.unsat)])
def test_legacy_bitvector_sorts_and_grammar_helpers_keep_their_definitions(increment, expected):
    # The original 2019 BV/PBE tracks use (BitVec W) in every sort position.
    source = ('(set-logic BV) '
              '(define-fun inc ((x (BitVec 8))) (BitVec 8) '
              ' (let ((y (BitVec 8) (bvadd x #x01))) y)) '
              '(synth-fun f ((x (BitVec 8))) (BitVec 8) '
              ' ((Start (BitVec 8) ((inc x))))) '
              '(define-fun via_f ((x (BitVec 8))) (BitVec 8) (f x)) '
              '(declare-var x (BitVec 8)) '
              '(constraint (= (via_f x) (bvadd x #x' + increment + '))) '
              '(constraint (forall ((y (BitVec 8))) (= (f y) (inc y)))) '
              '(check-synth)')
    result = translate(source, depth='0')
    assert '(BitVec ' not in result.to_smt2()
    assert check(result) == expected


def test_nullary_bitvector_helper_is_a_grammar_terminal():
    source = ('(set-logic BV) (define-fun one () (BitVec 8) #x01) '
              '(synth-fun f () (BitVec 8) ((Start (BitVec 8) (one)))) '
              '(constraint (= f #x01)) (check-synth)')
    assert check(translate(source, depth='0')) == z3.sat


def test_grammar_helper_does_not_accept_wrong_width_argument():
    source = ('(set-logic BV) '
              '(define-fun inc ((x (BitVec 8))) (BitVec 8) (bvadd x #x01)) '
              '(synth-fun f ((x (BitVec 16))) (BitVec 8) '
              ' ((Start (BitVec 8) ((inc x))))) (check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any('wrong sort' in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize(
    "parameters,result_sort,body,application,samples",
    [
        ("((x (BitVec 4)) (y (BitVec 2)))", "(BitVec 6)",
         "(concat x y)", "(typed x y)",
         [("#b0000 #b00", "#b000000"), ("#b1010 #b11", "#b101011"),
          ("#b1111 #b11", "#b111111")]),
        ("((x (BitVec 4)) (y (BitVec 4)))", "(BitVec 1)",
         "(bvcomp x y)", "(typed x y)",
         [("#b0000 #b0000", "#b1"), ("#b0000 #b1111", "#b0"),
          ("#b1111 #b1111", "#b1")]),
        *[("((x (BitVec 8)))", "Int", f"({operator} x)", "(typed x)",
           [("#x00", "0"), ("#x7f", "127"), ("#x80", "128"), ("#xff", "255")])
          for operator in ("bv2int", "bv2nat", "ubv_to_int")],
        ("((x (BitVec 8)))", "Int", "(sbv_to_int x)", "(typed x)",
         [("#x00", "0"), ("#x7f", "127"), ("#x80", "(- 128)"), ("#xff", "(- 1)")]),
    ],
)
@pytest.mark.parametrize("negate", [False, True])
def test_typed_let_infers_concat_comparison_and_conversion_result_sorts(
    parameters, result_sort, body, application, samples, negate
):
    # Expected ground values are independent of the helper's expression. The
    # singleton grammar must satisfy all of them and reject their negations.
    constraints = []
    for arguments, expected in samples:
        equality = f"(= (f {arguments}) {expected})"
        constraints.append(f"(constraint {'(not ' + equality + ')' if negate else equality})")
    source = ("(set-logic ALL) "
              f"(define-fun typed {parameters} {result_sort} "
              f"(let ((value {result_sort} {body})) value)) "
              f"(synth-fun f {parameters} {result_sort} "
              f"((Start {result_sort})) "
              f"((Start {result_sort} ({application})))) "
              + " ".join(constraints) + " "
              "(check-synth)")
    result = translate(source, depth='0')
    assert "(BitVec " not in result.to_smt2()
    assert check(result, finite=True) == (z3.unsat if negate else z3.sat)


def test_typed_let_rejects_bvcomp_with_mixed_operand_widths():
    source = ('(set-logic BV) '
              '(define-fun typed ((x (BitVec 8)) (y (BitVec 4))) (BitVec 1) '
              ' (let ((value (BitVec 1) (bvcomp x y))) value)) '
              '(synth-fun f ((x (BitVec 8)) (y (BitVec 4))) (BitVec 1) '
              ' ((Start (BitVec 1))) ((Start (BitVec 1) ((typed x y))))) '
              '(check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any("typed let binding 'value'" in d.message
               for d in result.diagnostic_items)


def test_reserved_store_helper_call_has_single_function_semantics():
    def benchmark(expected_zero, expected_one):
        return ('(set-logic BV) '
                '(define-fun store ((x (BitVec 4))) (BitVec 4) '
                ' (bvadd x #x1)) '
                '(synth-fun f ((x (BitVec 4))) (BitVec 4) '
                ' ((Start (BitVec 4))) '
                ' ((Start (BitVec 4) ((store x) x)))) '
                '(constraint (= (f #x0) ' + expected_zero + ')) '
                '(constraint (= (f #x1) ' + expected_one + ')) '
                '(check-synth)')

    assert check(translate(benchmark('#x1', '#x2'), depth='0')) == z3.sat
    assert check(translate(benchmark('#x2', '#x3'), depth='0')) == z3.unsat


def test_reserved_store_helper_call_preserves_nullary_candidate_alias():
    def benchmark(expected):
        return ('(set-logic BV) '
                '(define-fun store () (BitVec 4) #x1) '
                '(synth-fun f () (BitVec 4) '
                ' ((Start (BitVec 4))) '
                ' ((Start (BitVec 4) (store #x0)))) '
                '(constraint (= f ' + expected + ')) (check-synth)')

    assert check(translate(benchmark('#x1'), depth='0')) == z3.sat
    assert check(translate(benchmark('#x2'), depth='0')) == z3.unsat


def test_reserved_store_helper_calls_are_coupled_across_synth_functions():
    def benchmark(expected):
        return ('(set-logic BV) '
                '(define-fun store ((x (BitVec 4))) (BitVec 4) '
                ' (bvadd x #x1)) '
                '(synth-fun f ((x (BitVec 4))) (BitVec 4) '
                ' ((Start (BitVec 4))) '
                ' ((Start (BitVec 4) ((store x) x)))) '
                '(synth-fun g ((x (BitVec 4))) (BitVec 4) '
                ' ((Start (BitVec 4))) '
                ' ((Start (BitVec 4) ((store x) x)))) '
                '(constraint (= (bvadd (f #x0) (g #x0)) ' + expected + ')) '
                '(check-synth)')

    assert check(translate(benchmark('#x2'), depth='0')) == z3.sat
    assert check(translate(benchmark('#x3'), depth='0')) == z3.unsat


def test_reserved_store_alias_keeps_shadowed_parameter_and_let_bindings():
    def benchmark(last_expected):
        return ('(set-logic BV) '
                '(define-fun store ((x (BitVec 4))) (BitVec 4) '
                ' (bvadd x #x1)) '
                '(define-fun param-shadow ((store (BitVec 4))) (BitVec 4) store) '
                '(define-fun let-shadow ((x (BitVec 4))) (BitVec 4) '
                ' (let ((store (BitVec 4) x)) store)) '
                '(synth-fun f ((x (BitVec 4))) (BitVec 4) '
                ' ((Start (BitVec 4))) '
                ' ((Start (BitVec 4) ((param-shadow x) (let-shadow x) '
                '                     (store x))))) '
                '(constraint (= (f #x0) #x0)) '
                '(constraint (= (f #x1) ' + last_expected + ')) '
                '(check-synth)')

    assert check(translate(benchmark('#x1'), depth='0')) == z3.sat
    assert check(translate(benchmark('#x0'), depth='0')) == z3.unsat


@pytest.mark.parametrize("name", [
    "bvadd", "extract", "int_to_bv", "bvnego", "bvuaddo",
])
@pytest.mark.parametrize("dependent", [False, True])
def test_bv_builtin_helper_names_are_rejected_before_candidate_specialization(
    name, dependent
):
    helper = f"(define-fun {name} ((x (BitVec 8))) (BitVec 8) "
    helper += "(f x))" if dependent else "x)"
    synth = ('(synth-fun f ((x (BitVec 8))) (BitVec 8) '
             '((Start (BitVec 8))) ((Start (BitVec 8) (x))))')
    commands = ['(set-logic BV)']
    commands.extend([synth, helper] if dependent else [helper, synth])
    commands.extend(['(constraint (= (f #x00) #x00))', '(check-synth)'])
    result = sp.translate(source=' '.join(commands), language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any("reserved by source logic BV" in d.message
               for d in result.diagnostic_items)


@pytest.mark.parametrize("name", [
    "bvadd", "extract", "int_to_bv", "bvnego", "bvuaddo",
])
def test_bv_builtin_names_cannot_be_synthesized_as_functions(name):
    source = ('(set-logic BV) '
              f'(synth-fun {name} ((x (BitVec 8))) (BitVec 8) '
              '((Start (BitVec 8))) ((Start (BitVec 8) (x)))) '
              '(declare-var x (BitVec 8)) '
              '(constraint (= (bvadd x #x00) x)) (check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any("reserved by source logic BV" in d.message
               for d in result.diagnostic_items)


@pytest.mark.parametrize("name", ["bvadd", "bvnego"])
def test_bv_builtin_names_cannot_be_synthesized_as_invariants(name):
    source = ('(set-logic BV) '
              f'(synth-inv {name} ((x (BitVec 8))) '
              '((Start Bool ((= x x))))) '
              '(check-synth)')
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any("reserved by source logic BV" in d.message
               for d in result.diagnostic_items)


def test_bv_builtin_spelling_remains_valid_as_a_scoped_parameter():
    source = ('(set-logic BV) '
              '(define-fun keep ((bvadd (BitVec 8))) (BitVec 8) bvadd) '
              '(synth-fun f ((x (BitVec 8))) (BitVec 8) '
              '((Start (BitVec 8))) ((Start (BitVec 8) ((keep x))))) '
              '(constraint (= (f #x2a) #x2a)) (check-synth)')
    assert check(translate(source, depth='0')) == z3.sat


@pytest.mark.parametrize("declaration", [
    '(synth-fun clash () Int ((Start Int (0))))',
    '(define-fun clash () Int 0)',
    '(synth-inv clash ((x Int)))',
])
@pytest.mark.parametrize("variable_first", [False, True])
def test_universal_variables_cannot_redeclare_a_function_symbol(declaration, variable_first):
    # SyGuS-IF 2.1 3.3/3.4 forbids reuse of a current-signature symbol.
    variable = '(declare-var clash Int)'
    commands = [variable, declaration] if variable_first else [declaration, variable]
    if declaration.startswith('(define-fun'):
        commands.append('(synth-fun witness () Int ((Start Int (0))))')
    source = '(set-logic LIA) ' + ' '.join(commands) + ' (check-synth)'
    result = sp.translate(source=source, language='sygus', profile='bmc',
                          options={'grammar_depth': '0'})
    assert not result.ok
    assert any('duplicat' in diagnostic.message and 'clash' in diagnostic.message
               for diagnostic in result.diagnostic_items)
