"""Declared SyGuS universals stay universal through source helper definitions."""

import z3
import somtparser as sp


def translate(source, depth="0"):
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_depth": depth})
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    return result


def check(result):
    assertions = z3.parse_smt2_string(result.to_smt2())
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(assertions)
    verdict = solver.check()
    assert verdict != z3.unknown
    return verdict


def _problem(definitions, constraint, sort="Int", logic="LIA"):
    return ("(set-logic " + logic + ") "
            "(synth-fun f () Bool ((B Bool (true false)))) "
            "(declare-var g " + sort + ") "
            + definitions + " (constraint " + constraint + ") (check-synth)")


def test_nullary_helper_global_is_universally_closed_not_existential():
    result = translate(_problem("(define-fun is-zero () Bool (= g 0))", "is-zero"))
    assert "(is-zero __somt_sygus_universal_0)" in result.to_smt2()
    assert "(forall ((__somt_sygus_universal_0 Int))" in result.to_smt2()
    # SAT would mean the implementation chose g=0 existentially. The source
    # declare-var is universally quantified, so g=1 is a counterexample.
    assert check(result) == z3.unsat


def test_transitive_helpers_receive_only_closed_global_arguments():
    definitions = ("(define-fun base () Bool (= g 0)) "
                   "(define-fun wrapper () Bool base)")
    result = translate(_problem(definitions, "wrapper"))
    text = result.to_smt2()
    assert "(wrapper __somt_sygus_universal_0)" in text
    assert check(result) == z3.unsat


def test_universal_closure_keeps_a_total_tautological_helper_satisfiable():
    definitions = ("(define-fun base () Bool (= g g)) "
                   "(define-fun wrapper () Bool base)")
    result = translate(_problem(definitions, "wrapper"))
    assert check(result) == z3.sat


def test_helper_global_is_not_captured_by_same_named_let_actual():
    definitions = "(define-fun matches-global ((x Int)) Bool (= x g))"
    result = translate(_problem(definitions,
                                "(let ((g 5)) (matches-global g))"))
    # The call's ordinary argument is the local 5, while its closure argument
    # is the outer universal. Confusing the two would make this SAT.
    assert check(result) == z3.unsat


def test_function_parameter_with_global_spelling_shadows_the_global():
    definitions = "(define-fun shadows ((g Int)) Bool (= g 5))"
    result = translate(_problem(definitions, "(shadows 5)"))
    # The helper does not capture the declared g: its formal parameter shadows
    # that name, so this universally quantified relation remains satisfiable.
    assert check(result) == z3.sat


def test_candidate_dependent_helper_is_closed_after_candidate_substitution():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(synth-fun f () Bool ((B Bool (true false)))) "
              "(define-fun check () Bool (and (= g 0) f)) "
              "(constraint check) (check-synth)")
    result = translate(source)
    assert "helper_0_check" in result.to_smt2()
    assert check(result) == z3.unsat


def test_candidate_introduced_helper_capture_is_added_to_outer_helper():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(define-fun base () Bool (= g 0)) "
              "(synth-fun f () Bool ((B Bool (base)))) "
              "(define-fun h () Bool f) "
              "(constraint h) (check-synth)")
    result = translate(source)
    assert check(result) == z3.unsat


def _capturing_macro_problem(body, *, joint):
    source = ("(set-logic LIA) (declare-var g Int) "
              "(define-fun base () Bool " + body + ") "
              "(synth-fun f () Bool ((B Bool (base)))) ")
    if joint:
        source += "(synth-fun h () Bool ((H Bool (true)))) "
    source += "(constraint (= f base)) (check-synth)"
    return source


def test_single_synth_capture_varies_with_global_and_has_no_fixed_witness():
    result = translate(_capturing_macro_problem("(= g 0)", joint=False))
    assert check(result) == z3.unsat


def test_joint_synth_capture_varies_with_global_and_has_no_fixed_witness():
    result = translate(_capturing_macro_problem("(= g 0)", joint=True))
    assert check(result) == z3.unsat


def test_single_synth_tautological_global_macro_has_fixed_witness():
    result = translate(_capturing_macro_problem("(= g g)", joint=False))
    assert check(result) == z3.sat


def test_joint_synth_tautological_global_macro_has_fixed_witness():
    result = translate(_capturing_macro_problem("(= g g)", joint=True))
    assert check(result) == z3.sat


def test_captured_helper_is_not_confused_with_same_named_synth_parameter():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(define-fun base () Bool (= g 0)) "
              "(synth-fun f ((g Int)) Bool ((B Bool (base)))) "
              "(constraint (= (f g) base)) (check-synth)")
    result = translate(source)
    assert check(result) == z3.unsat


def test_define_fun_cannot_capture_a_later_declare_var():
    source = ("(set-logic LIA) (synth-fun f () Bool ((B Bool (true false)))) "
              "(define-fun earlier () Bool (= later 0)) "
              "(declare-var later Int) (constraint earlier) (check-synth)")
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_depth": "0"})
    assert not result.ok
    assert any("unknown" in diagnostic.message.lower()
               or "undeclared" in diagnostic.message.lower()
               for diagnostic in result.diagnostic_items)


def test_quantifier_shadowing_is_restored_after_the_nested_body():
    definitions = ("(define-fun nested ((x Int)) Bool "
                   "(and (exists ((g Int)) (= g 7)) (= x g)))")
    result = translate(_problem(definitions, "(nested 7)"))
    # The exists binder shadows g only in its own body. The final equality
    # still refers to the declare-var and therefore fails for some universal g.
    assert check(result) == z3.unsat


def test_bitvector_global_closure_keeps_exact_width():
    definitions = "(define-fun is-zero () Bool (= g #b0000))"
    result = translate(_problem(definitions, "is-zero", sort="(_ BitVec 4)",
                                logic="BV"))
    assert "(__somt_sygus_universal_0 (_ BitVec 4))" in result.to_smt2()
    assert check(result) == z3.unsat


def test_joint_synthesis_closes_globals_in_grammar_helpers():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(define-fun base () Bool (= g 0)) "
              "(synth-fun f () Bool ((B Bool (base)))) "
              "(synth-fun h () Bool ((B Bool (true)))) "
              "(constraint (and f h)) (check-synth)")
    assert check(translate(source)) == z3.unsat


def test_joint_synthesis_transitive_dependent_helper_stays_satisfiable():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(define-fun base () Bool (= g g)) "
              "(synth-fun f () Bool ((B Bool (base)))) "
              "(synth-fun h () Bool ((B Bool (true)))) "
              "(define-fun combine () Bool (and f h (= g g))) "
              "(constraint combine) (check-synth)")
    assert check(translate(source)) == z3.sat


def test_joint_synth_parameter_can_share_an_uncaptured_universal_name():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(synth-fun f ((g Int)) Int ((I Int (g)))) "
              "(synth-fun h () Bool ((B Bool (true)))) "
              "(constraint (and (= (f g) g) h)) (check-synth)")
    assert check(translate(source)) == z3.sat
