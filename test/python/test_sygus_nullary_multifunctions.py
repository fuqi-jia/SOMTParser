"""Regression coverage for parenthesized nullary calls in joint SyGuS."""

import pytest
import z3
import somtparser as sp


def translate(source):
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_depth": "1"})
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.report.fidelity.sound
    assert not result.report.fidelity.complete
    return result


def verdict(source):
    translated = translate(source)
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(translated.to_smt2()))
    answer = solver.check()
    assert answer != z3.unknown
    return translated, answer


GRAMMAR = "((Start Int ((Constant Int))))"


def two_nullary_functions(constraint):
    return ("(set-logic LIA) "
            f"(synth-fun fb () Int {GRAMMAR}) "
            f"(synth-fun fc () Int {GRAMMAR}) "
            f"{constraint} (check-synth)")


def test_official_general_plus10_parenthesized_nullary_calls():
    # Official r33 case 680, General_plus10.sl. In source SyGuS syntax these
    # nullary calls arrive as one-element S-expressions, while the generated
    # target must refer to each wrapper as a bare SMT constant.
    translated, answer = verdict(two_nullary_functions(
        "(constraint (= (fc) (+ (fb) 10)))"))
    assert answer == z3.sat
    text = translated.to_smt2()
    assert "(__somt_sygus_function_0)" not in text
    assert "(__somt_sygus_function_1)" not in text


def test_bare_nullary_symbols_remain_valid_joint_synthesis_terms():
    _, answer = verdict(two_nullary_functions(
        "(constraint (= fc (+ fb 10)))"))
    assert answer == z3.sat


def test_helper_parameter_captures_name_of_nullary_synth_function():
    source = ("(set-logic LIA) "
              f"(synth-fun fb () Int {GRAMMAR}) "
              f"(synth-fun fc () Int {GRAMMAR}) "
              "(define-fun capture ((fb Int)) Int fb) "
              "(constraint (= (fc) (capture (+ (fb) 10)))) "
              "(constraint (= (fc) (+ (fb) 10))) "
              "(check-synth)")
    translated, answer = verdict(source)
    # If renaming captures the helper's formal `fb` as the synthesized
    # function wrapper, the first constraint becomes fc = fb and conflicts
    # with the second. Correct lexical scoping makes them equivalent.
    assert answer == z3.sat
    # The independent SAT result above checks capture even if lowering
    # alpha-renames the helper or its formal parameter in the emitted script.


def test_wrong_arity_parenthesized_nullary_call_is_still_rejected():
    source = two_nullary_functions(
        "(constraint (= (fc) (+ (fb 1) 10)))")
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_depth": "1"})
    assert not result.ok


@pytest.mark.parametrize("expected", [11, 12])
def test_parenthesized_nullary_reserved_helper_keeps_its_value(expected):
    # Reserved helper names are renamed too. A value-changing normalization
    # would incorrectly admit the contradictory case as well as the SAT case.
    source = ("(set-logic LIA) "
              "(define-fun store () Int 1) "
              f"(synth-fun fb () Int {GRAMMAR}) "
              f"(synth-fun fc () Int {GRAMMAR}) "
              "(constraint (= (fb) (store))) "
              "(constraint (= (fc) (+ (fb) 10))) "
              f"(constraint (= (fc) {expected})) (check-synth)")
    _, answer = verdict(source)
    assert answer == (z3.sat if expected == 11 else z3.unsat)
