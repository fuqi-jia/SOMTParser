"""Sharing must preserve lexical binding, including shadowed variable names."""

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def repeated(name):
    term = f"(* (+ {name} 1) 2)"
    return "(+ " + " ".join([term] * 4) + ")"


P = repeated("x")


@pytest.mark.parametrize(
    "inner, expected",
    [
        (f"(exists ((x Int)) (= {P} 8))", "sat"),
        (f"(forall ((x Int)) (= {P} 0))", "unsat"),
        (f"(let ((x 0) (y {P})) (and (= y 0) (= {P} 8)))", "sat"),
        (f"(let ((x 0)) (let ((y {P})) (= y 8)))", "sat"),
        (f"(match (some 0) ((none false) ((some x) (= {P} 8))))", "sat"),
    ],
    ids=["exists", "forall", "parallel-let", "nested-let", "match"],
)
def test_shadowing_preserves_reference_relation(inner, expected):
    source = (
        "(set-logic ALL)\n"
        "(declare-datatype MaybeInt ((none) (some (value Int))))\n"
        f"(assert (exists ((x Int)) (and (= {P} 0) (>= {P} 0) {inner})))\n"
    )
    output = sp.parse(source).dump_smt2()
    context = z3.Context()
    reference = z3.And(*z3.parse_smt2_string(source, ctx=context))
    actual = z3.And(*z3.parse_smt2_string(output, ctx=context))
    for formula in (reference, actual):
        solver = z3.Solver(ctx=context)
        solver.set(timeout=5000)
        solver.add(formula)
        assert str(solver.check()) == expected, output

    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.Xor(reference, actual))
    assert solver.check() == z3.unsat, output
