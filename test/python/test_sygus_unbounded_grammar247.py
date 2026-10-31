"""Finite-tree SyGuS grammar encoding tests; runtime qualification is remote."""

import z3
import somtparser as sp


def _translate(source, options=None):
    translated = sp.translate(source=source, language="sygus", profile="bmc",
                              options=options or {})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    return translated.to_smt2()


def _status(smt2):
    # Each translation is an independent SMT module. Keep its declarations in
    # a fresh Z3 context so same-spelled generated helpers from earlier modules
    # do not collide in Z3's process-global context.
    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(smt2, ctx=ctx))
    status = solver.check()
    assert status != z3.unknown
    return status


def test_unbounded_recursive_tree_is_sat_and_depth_mode_stays_explicit():
    source = (
        "(set-logic LIA) "
        "(synth-fun f ((x Int)) Int "
        " ((Start Int (x 0 (+ Start Start) (- Start Start))))) "
        "(declare-var x Int) (constraint (= (f x) x)) (check-synth)"
    )
    unbounded = _translate(source, {"grammar_mode": "unbounded"})
    assert "declare-datatypes" in unbounded
    assert "define-funs-rec" in unbounded
    assert _status(unbounded) == z3.sat

    bounded_source = (
        "(set-logic LIA) "
        "(synth-fun f ((x Int)) Int ((Start Int (0 (+ Start Start))))) "
        "(declare-var x Int) (constraint (= (f x) x)) (check-synth)"
    )
    bounded = _translate(bounded_source, {"grammar_depth": "1"})
    assert "declare-datatypes" not in bounded
    assert _status(bounded) == z3.unsat


def test_recursive_boolean_scc_and_string_constant_rendering_parse():
    boolean_source = (
        "(set-logic LIA) "
        "(synth-fun p ((x Bool)) Bool "
        " ((Start Bool (true false x (not Start) "
        "(and (Constant Bool) Start))))) "
        "(declare-var x Bool) (constraint (= (p x) x)) (check-synth)"
    )
    boolean_smt = _translate(boolean_source)
    assert "define-funs-rec" in boolean_smt
    assert _status(boolean_smt) == z3.sat

    string_source = (
        '(set-logic SLIA) (synth-fun s () String '
        ' ((Start String ((Constant String))))) '
        '(constraint (= s "a")) (check-synth)'
    )
    string_smt = _translate(string_source)
    assert _status(string_smt) == z3.sat

    # A single Constant rule has an exact direct-witness encoding. Add a
    # recursive production to exercise the AST String renderer as well.
    recursive_string = (
        '(set-logic SLIA) (synth-fun s () String '
        ' ((Start String ((Constant String) (str.++ Start Start))))) '
        '(constraint (= s "a")) (check-synth)'
    )
    rendered_smt = _translate(recursive_string)
    assert "declare-datatypes" in rendered_smt
    assert "str.replace_all" in rendered_smt
    z3.parse_smt2_string(rendered_smt, ctx=z3.Context())

    nested_variable = (
        "(set-logic LIA) (synth-fun inc ((x Int)) Int "
        " ((Start Int ((+ (Variable Int) 1))))) "
        "(declare-var x Int) (constraint (= (inc x) (+ x 1))) (check-synth)"
    )
    assert _status(_translate(nested_variable)) == z3.sat


def test_grammar_without_finite_derivations_is_exactly_unsat():
    source = (
        "(set-logic LIA) (synth-fun z () Int ((A Int (A)))) "
        "(constraint (= z 0)) (check-synth)"
    )
    assert _status(_translate(source)) == z3.unsat


def test_nested_constants_choose_independent_values():
    source = (
        "(set-logic LIA) (synth-fun q () Bool "
        " ((Start Bool ((xor (Constant Bool) (Constant Bool)))))) "
        "(constraint q) (check-synth)"
    )
    # Satisfiable only when the two Constant occurrences can differ.
    smt = _translate(source)
    assert "__somt_sygus_grammar_literal_" not in smt
    assert _status(smt) == z3.sat
