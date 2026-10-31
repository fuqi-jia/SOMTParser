"""Parallel SMT-LIB let scope, independently checked before/after HIR lifting."""
import shutil
import subprocess

import pytest
import z3
import somtparser as sp


CASES = [
    ("(declare-const x Int)(assert (= x 10))",
     "(= (let ((x 1) (y x)) (+ x y)) 11)"),
    ("", "(= (let ((x 3)) (let ((x 1) (y x)) (+ x y))) 4)"),
    ("(declare-const x Int)(assert (= x 10))",
     "(let ((x false) (y (+ x 1))) (= y 11))"),
    ("", "(forall ((x Int)) (= (let ((x 0) (y x)) y) x))"),
    ("(declare-const x Int)(assert (= x 10))",
     "(= (let ((a (let ((x 1) (y x)) (+ x y))) (b x)) (+ a b)) 21)"),
]


def solver_statuses(script):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(script))
    z3_status = str(solver.check())
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for the second independent let oracle")
    result = subprocess.run(
        [executable, "--lang=smt2", "--tlimit=5000"],
        input=script + "\n(check-sat)\n", text=True,
        capture_output=True, timeout=10,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    answers = [line for line in result.stdout.splitlines()
               if line in {"sat", "unsat", "unknown"}]
    assert answers, result.stdout + result.stderr
    return z3_status, answers[-1]


@pytest.mark.parametrize("base,claim", CASES)
@pytest.mark.parametrize("negated", [False, True])
def test_parallel_rhs_scope_survives_source_to_hir(base, claim, negated):
    expected = "unsat" if negated else "sat"
    formula = f"(not {claim})" if negated else claim
    source = f"(set-logic ALL)\n{base}\n(assert {formula})\n"
    assert solver_statuses(source) == (expected, expected)
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert solver_statuses(translated.to_smt2()) == (expected, expected)


@pytest.mark.parametrize("preserve", [False, True])
def test_native_parallel_scope_evaluation_and_free_variables(preserve):
    parser = sp.parse("(set-logic QF_LIA)(declare-const x Int)")
    parser.set_option("keep_let", preserve)
    model = parser.parse_model("(model (define-fun x () Int 10))")
    expression = parser.expr("(let ((x 1) (y x)) (+ x y))")
    assert parser.evaluate(expression, model).value == 11
    assert {v.name for v in parser.collect_vars(expression)} == {"x"}
    assert parser.evaluate(parser.expr("x"), model).value == 10
    assert parser.evaluate(
        parser.expr("(let ((x false) (y (+ x 1))) y)"), model
    ).value == 11


@pytest.mark.parametrize("preserve", [False, True])
@pytest.mark.parametrize("term", ["(let () 1)", "(let ((fresh 1) (other fresh)) other)"])
def test_empty_or_sibling_only_binding_is_rejected(preserve, term):
    parser = sp.Parser()
    parser.set_option("keep_let", preserve)
    with pytest.raises((sp.ParseError, ValueError, RuntimeError)):
        parser.expr(term)
