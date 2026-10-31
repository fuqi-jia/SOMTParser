"""Exact Bool/BV1 array translation, including native OptiMathSAT acceptance."""
import os
import shutil
import subprocess

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


CASES = [
    ("(declare-const a (Array Int Bool))"
     "(assert (= a (store ((as const (Array Int Bool)) false) 3 true)))"
     "(assert (select a 3))(assert (not (select a 4)))", "sat"),
    ("(declare-const a (Array Int Bool))"
     "(assert (= a (store ((as const (Array Int Bool)) false) 3 true)))"
     "(assert (select a 4))", "unsat"),
    ("(declare-const a (Array Bool Int))"
     "(assert (= (select a true) 1))(assert (= (select a false) 2))"
     "(assert (= a (store ((as const (Array Bool Int)) 1) false 2)))", "sat"),
    ("(declare-const a (Array Bool Bool))"
     "(assert (distinct a ((as const (Array Bool Bool)) false)))"
     "(assert (not (select a true)))(assert (not (select a false)))", "unsat"),
    ("(declare-const a (Array Int (Array Int Bool)))"
     "(define-fun table () (Array Int Bool) (store ((as const (Array Int Bool)) false) 2 true))"
     "(assert (= a (store ((as const (Array Int (Array Int Bool))) table) 3 table)))"
     "(assert (select (select a 3) 2))(assert (not (select (select a 5) 4)))", "sat"),
    ("(declare-const a (Array Int Bool))"
     "(define-fun f ((a (Array Int Bool))) Bool (select a 0))"
     "(assert (let ((a true) (v a)) (and a (f v))))", "sat"),
    ("(declare-const a (Array Int Bool))"
     "(assert (let ((a (store a 0 true)))"
     "(let ((a (store a 1 false))) (and (select a 0) (not (select a 1))))))", "sat"),
]


def export(source, route):
    source = "(set-logic ALL)" + source + "(check-sat)"
    if route == "parser":
        return sp.parse(source).dump_smt2(dialect=sp.OmtDialect.OptiMathSAT)
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, translated.diagnostic_items
    return translated.to_smt2(dialect=sp.OmtDialect.OptiMathSAT)


@pytest.mark.parametrize("source,expected", CASES)
@pytest.mark.parametrize("route", ["parser", "hir"])
def test_status_and_reimport(source, expected, route):
    result = export(source, route)
    assert "(_ BitVec 1)" in result
    for text in [source, result, sp.parse(result).dump_smt2()]:
        solver = z3.Solver()
        solver.set(timeout=10000)
        solver.from_string(text)
        assert str(solver.check()) == expected


@pytest.mark.parametrize("source,expected", CASES)
def test_native_optimathsat_accepts_and_solves(source, expected):
    executable = os.environ.get("SOMTPARSER_OPTIMATHSAT") or shutil.which("optimathsat")
    if not executable:
        pytest.skip("OptiMathSAT executable unavailable")
    process = subprocess.run([executable], input=export(source, "parser"), text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
    assert process.returncode == 0, process.stderr
    assert "(error" not in process.stdout, process.stdout
    assert expected in process.stdout.splitlines(), process.stdout


def test_extensional_bool_array_bijection_and_objective_preservation():
    # Bool indices have exactly two points. Link both encodings completely,
    # then prove the entire hard relation and the cost agree for ALL arrays.
    source = (
        "(declare-const a (Array Bool Bool))(declare-const b (Array Bool Bool))"
        "(assert (= b (store a false (not (select a true)))))"
        "(assert (distinct a b))"
        "(minimize (+ (ite (select a true) 2 0) (ite (select b false) 3 0)))"
    )
    original, lowered = z3.Optimize(), z3.Optimize()
    original.from_string(source)
    lowered.from_string(export(source, "parser"))
    links = []
    for name in ["a", "b"]:
        old = z3.Array(name, z3.BoolSort(), z3.BoolSort())
        new = z3.Array(name, z3.BitVecSort(1), z3.BitVecSort(1))
        for value in [False, True]:
            links.append(old[value] == (new[z3.BitVecVal(int(value), 1)] == 1))
    solver = z3.Solver()
    solver.add(*links)
    solver.add(z3.Or(z3.Xor(z3.And(*original.assertions()), z3.And(*lowered.assertions())),
                     original.objectives()[0] != lowered.objectives()[0]))
    assert solver.check() == z3.unsat


def test_stream_and_string_agree_and_keep_responses(tmp_path):
    source = ("(declare-const a (Array Int Bool))(assert (select a 0))"
              "(minimize (ite (select a 1) 2 1))(check-sat)(get-objectives)")
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, translated.diagnostic_items
    destination = tmp_path / "arrays.smt2"
    translated.write_smt2(str(destination), dialect=sp.OmtDialect.OptiMathSAT)
    assert destination.read_text() == translated.to_smt2(dialect=sp.OmtDialect.OptiMathSAT)
    assert "(get-objectives)" in destination.read_text()


@pytest.mark.parametrize("route", ["parser", "hir"])
def test_acyclic_retained_definition_uses_ordinary_oms_macro(route):
    source = "(define-fun-rec f ((x Int)) Int (+ x 1))(assert (= (f 3) 4))"
    if route == "hir":
        # An ordinary source definition exceeds HIR's macro-expansion budget.
        # Explicit source recursion takes a different, quantified encoding.
        terms = " ".join(f"(ite (< x {i}) {i} (- {i}))" for i in range(600))
        source = f"(define-fun f ((x Int)) Int (+ {terms}))(assert (= (f 0) 179700))"
    result = export(source, route)
    assert "define-fun-rec" not in result
    solver = z3.Solver()
    solver.from_string(result)
    assert str(solver.check()) == "sat"
    executable = os.environ.get("SOMTPARSER_OPTIMATHSAT")
    if executable:
        process = subprocess.run([executable], input=result, text=True,
                                 capture_output=True, timeout=20)
        assert process.returncode == 0, process.stderr
        assert "sat" in process.stdout.splitlines()


def test_true_recursion_is_not_silently_rewritten_as_acyclic():
    source = "(define-fun-rec f ((x Int)) Int (ite (<= x 0) 0 (+ 1 (f (- x 1)))))"
    with pytest.raises(RuntimeError, match="recursive"):
        export(source, "parser")
