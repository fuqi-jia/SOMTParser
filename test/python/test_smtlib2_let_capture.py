"""SMT-LIB lifting captures let values before entering shadowing binders."""
from _public_relation import public_relation

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize(
    "formula, expected",
    [
        ("(exists ((x Int)) (and (= x 0) (let ((a x)) "
         "(exists ((x Int)) (and (= x 1) (= a 0))))))", "sat"),
        ("(exists ((x Int)) (and (= x 0) (let ((a x)) "
         "(forall ((x Int)) (= a 0)))))", "sat"),
        ("(exists ((x Int)) (and (= x 0) (let ((a x)) "
         "(exists ((x Bool)) (and x (= a 0))))))", "sat"),
        ("(exists ((x Int)) (and (= x 0) (let ((a x) (x 9)) "
         "(let ((b a)) (exists ((x Int)) (and (= x 1) (= b 0)))))))", "sat"),
        ("(and (exists ((x Int)) (and (= x 0) (let ((a x)) (= a 0)))) "
         "(exists ((x Int)) (and (= x 1) (let ((a x)) (= a 1)))))", "sat"),
        ("(exists ((x Int)) (and (= x 0) (let ((a x)) "
         "(exists ((x Int)) (and (= x 1) (= a 1))))))", "unsat"),
        ("(let ((x 0)) (exists ((x Int)) (= x 1)))", "sat"),
        ("(exists ((|x| Int)) (and (= x 0) (let ((a |x|) (x 9)) "
         "(exists ((|x| Int)) (and (= x 1) (= a 0))))))", "sat"),
        ("(exists ((|x| Int)) (and (= |x| 0) (let ((a |x|)) "
         "(exists ((x Int)) (and (= x 1) (= a 0))))))", "sat"),
    ],
    ids=["exists", "forall", "different-sort", "parallel-and-chain", "siblings", "unsat",
         "let-then-quantifier", "quoted-shadowing", "mixed-quoted-shadowing"],
)
def test_let_value_keeps_enclosing_binding(formula, expected):
    source = f"(set-logic ALL)\n(assert {formula})\n"
    translation = sp.translate(source=source, language="smtlib2")
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    output = translation.to_smt2(sp.OmtDialect.Z3)
    context = z3.Context()
    reference = z3.And(*z3.parse_smt2_string(source, ctx=context))
    actual = public_relation(translation, output, ctx=context)
    for value in (reference, actual):
        solver = z3.Solver(ctx=context)
        solver.set(timeout=5000)
        solver.add(value)
        assert str(solver.check()) == expected, output
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.Xor(reference, actual))
    assert solver.check() == z3.unsat, output
