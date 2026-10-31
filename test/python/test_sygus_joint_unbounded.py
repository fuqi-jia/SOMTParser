"""Joint syntax trees, invariant obligations, and source witness round trips."""
import re

import pytest
import z3
import somtparser as sp


def translate(source):
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_mode": "unbounded"})
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


def solve(text):
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(text, ctx=context))
    status = solver.check()
    assert status != z3.unknown, solver.reason_unknown()
    return solver, status


def witnesses(result):
    text = result.to_smt2(sp.OmtDialect.Z3)
    solver, status = solve(text)
    assert status == z3.sat
    names = re.findall(
        r"\(declare-(?:const|fun)\s+(__somt_sygus_witness_(text|value)_(\d+))\s+"
        r"(?:\(\)\s+)?(String|Int|Bool|\(_ BitVec \d+\))\)", text)
    terms = {}
    for name, kind, index, sort in names:
        if sort.startswith("(_ BitVec"):
            term = z3.BitVec(name, int(re.search(r"\d+", sort).group()), ctx=solver.ctx)
        else:
            term = {"String": z3.String, "Int": z3.Int, "Bool": z3.Bool}[sort](name, ctx=solver.ctx)
        value = solver.model().eval(term, model_completion=True)
        terms[int(index)] = value.as_string() if kind == "text" else value.sexpr()
    assert terms
    return text, terms


def test_official_general_plus10_projects_independent_constants():
    # Exact official SyGuS2019 index680: SHA256
    # 3e799eae6ba6e39fc777360ebce01355d30df08499683b42156dc7d64e98f77c.
    source = """(set-logic LIA)

(synth-fun fb () Int
    ((Start Int ((Constant Int)))))

(synth-fun fc () Int
    ((Start Int ((Constant Int)))))

(constraint (= (fc) (+ (fb) 10)))

(check-synth)
"""
    result = translate(source)
    _, terms = witnesses(result)
    assert set(terms) == {0, 1}
    _, status = solve(f"(define-fun fb () Int {terms[0]}) "
                      f"(define-fun fc () Int {terms[1]}) "
                      "(assert (not (= fc (+ fb 10))))")
    assert status == z3.unsat
    assert {choice.site for choice in result.report.choices
            if choice.strategy == "unbounded-grammar-direct-constant"} == {"fb", "fc"}


def test_joint_wrappers_share_universals_and_helper_capture():
    result = translate(
        "(set-logic LIA) (declare-var x Int) (declare-var y Int) "
        "(define-fun base () Int (- x x)) "
        "(synth-fun f ((arg Int)) Int ((Start Int ((Variable Int) base)))) "
        "(synth-fun g ((arg Int)) Int ((Start Int ((Variable Int) base)))) "
        "(constraint (= (f y) 0)) (constraint (= (g y) (f y))) (check-synth)")
    text, terms = witnesses(result)
    assert terms == {0: "base", 1: "base"}
    assert "__somt_sygus_universal_" in text
    # Check a counterexample to the original specification under explicit
    # closure parameters, using only source helper names from the witnesses.
    _, status = solve(
        "(define-fun base ((captured_x Int)) Int (- captured_x captured_x)) "
        f"(define-fun f ((arg Int) (captured_x Int)) Int ({terms[0]} captured_x)) "
        f"(define-fun g ((arg Int) (captured_x Int)) Int ({terms[1]} captured_x)) "
        "(declare-const x Int) (declare-const y Int) "
        "(assert (not (and (= (f y x) 0) (= (g y x) (f y x)))))")
    assert status == z3.unsat


def test_joint_cross_calls_do_not_lose_inconsistent_obligations():
    result = translate(
        "(set-logic LIA) "
        "(synth-fun f ((x Int)) Int ((Start Int (x (+ Start 1))))) "
        "(synth-fun g ((x Int)) Int ((Start Int (x (+ Start 1))))) "
        "(declare-var x Int) (constraint (= (f x) x)) "
        "(constraint (= (g x) (+ x 1))) (constraint (= (g x) (f x))) (check-synth)")
    _, status = solve(result.to_smt2(sp.OmtDialect.Z3))
    assert status == z3.unsat


def test_unbounded_invariant_projects_a_source_inductive_invariant():
    result = translate(
        "(set-logic LIA) (declare-primed-var x Int) "
        "(define-fun pre ((x Int)) Bool (= x 0)) "
        "(define-fun trans ((x Int) (xp Int)) Bool (= xp x)) "
        "(define-fun post ((x Int)) Bool (= x 0)) "
        "(synth-inv inv ((x Int)) ((Start Bool (true false (= x 0))))) "
        "(inv-constraint inv pre trans post) (check-synth)")
    _, terms = witnesses(result)
    assert set(terms) == {0}
    _, status = solve(
        f"(define-fun inv ((x Int)) Bool {terms[0]}) "
        "(declare-const x Int) (declare-const xp Int) "
        "(assert (not (and (=> (= x 0) (inv x)) "
        "(=> (and (inv x) (= xp x)) (inv xp)) (=> (inv x) (= x 0)))))")
    assert status == z3.unsat


@pytest.mark.parametrize("sort,first,second", [
    ("Int", "(- 7)", "19"), ("Bool", "true", "false"),
    ("String", '"left"', '"right"'), ("(_ BitVec 4)", "#x1", "#xe"),
])
def test_joint_direct_constants_keep_sorts_and_distinct_witnesses(sort, first, second):
    result = translate(
        f"(set-logic ALL) (synth-fun f () {sort} ((S {sort} ((Constant {sort}))))) "
        f"(synth-fun g () {sort} ((S {sort} ((Constant {sort}))))) "
        f"(constraint (= f {first})) (constraint (= g {second})) (check-synth)")
    _, terms = witnesses(result)
    assert set(terms) == {0, 1}
    _, status = solve(f"(define-fun f () {sort} {terms[0]}) "
                      f"(define-fun g () {sort} {terms[1]}) "
                      f"(assert (not (and (= f {first}) (= g {second}))))")
    assert status == z3.unsat


def test_joint_embedded_constants_have_disjoint_datatype_selectors():
    result = translate(
        "(set-logic ALL) "
        "(synth-fun f () Bool ((S Bool ((not (Constant Bool)))))) "
        "(synth-fun g () Int ((S Int ((+ (Constant Int) 1))))) "
        "(constraint f) (constraint (= g 4)) (check-synth)")
    _, terms = witnesses(result)
    assert set(terms) == {0, 1}
    _, status = solve(f"(define-fun f () Bool {terms[0]}) "
                      f"(define-fun g () Int {terms[1]}) "
                      "(assert (not (and f (= g 4))))")
    assert status == z3.unsat


def test_two_empty_grammars_are_unsat_without_duplicate_renderer_names():
    result = translate(
        "(set-logic ALL) (synth-fun f () Int ((S Int (S)))) "
        "(synth-fun g () Bool ((S Bool (S)))) (constraint true) (check-synth)")
    _, status = solve(result.to_smt2(sp.OmtDialect.Z3))
    assert status == z3.unsat


def test_single_unbounded_function_cannot_vary_with_captured_universal():
    result = translate(
        "(set-logic LIA) (declare-var x Int) "
        "(define-fun captured () Int x) "
        "(synth-fun f () Int ((S Int (captured)))) "
        "(constraint (= f x)) (check-synth)")
    _, status = solve(result.to_smt2(sp.OmtDialect.Z3))
    assert status == z3.unsat


def test_joint_unbounded_functions_cannot_hide_global_capture_in_helper():
    result = translate(
        "(set-logic LIA) (declare-var x Int) "
        "(define-fun captured () Int x) "
        "(synth-fun f () Int ((S Int (captured)))) "
        "(synth-fun g () Int ((S Int ((Constant Int))))) "
        "(constraint (= f g)) (check-synth)")
    _, status = solve(result.to_smt2(sp.OmtDialect.Z3))
    assert status == z3.unsat


@pytest.mark.parametrize("target", [1, 5])
def test_nested_nonterminal_occurrences_choose_independent_subtrees(target):
    # Reduced from the nested weighted ite production in official CrCi inputs.
    # Reusing one field for every B would permit only 0 or 15, not 1 or 5.
    result = translate(
        "(set-logic LIA) "
        "(synth-fun f () Int "
        "((Start Int ((+ (ite B 1 0) (+ (ite B 2 0) "
        "(+ (ite B 4 0) (ite B 8 0)))))) (B Bool (true false)))) "
        f"(constraint (= f {target})) (check-synth)")
    _, terms = witnesses(result)
    _, status = solve(f"(define-fun f () Int {terms[0]}) "
                      f"(assert (not (= f {target})))")
    assert str(status) == "unsat"


def test_nested_variable_and_nonterminal_choices_do_not_alias():
    result = translate(
        "(set-logic LIA) "
        "(synth-fun f ((x Int) (y Int)) Int "
        "((Start Int ((+ (* 2 (Variable Int)) "
        "(+ (Variable Int) (ite B 10 0))))) (B Bool (true false)))) "
        "(declare-var a Int) (declare-var b Int) "
        "(constraint (= (f a b) (+ (* 2 a) b 10))) (check-synth)")
    _, terms = witnesses(result)
    _, status = solve(f"(define-fun f ((x Int) (y Int)) Int {terms[0]}) "
                      "(declare-const a Int) (declare-const b Int) "
                      "(assert (not (= (f a b) (+ (* 2 a) b 10))))")
    assert str(status) == "unsat"
