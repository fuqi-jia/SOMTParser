"""QDIMACS 1.1 implicit closure checked against independent Boolean formulas.

Specification: https://www.qbflib.org/qdimacs.html, Input format, third
additional constraint. An implicit variable must never depend on a universal.
"""
import itertools
import pytest
import z3
from z3.z3util import get_vars

import somtparser as sp


def translated(source):
    result = sp.translate(source=source, language="qdimacs")
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    formula = z3.And(*z3.parse_smt2_string(script))
    private = get_vars(formula)
    assert all(str(v.decl().name()).startswith("!somt_exists_") for v in private)
    # These constants are implementation witnesses, not QDIMACS free variables.
    return z3.Exists(private, formula) if private else formula


@pytest.mark.parametrize("clauses,expected", [
    ("1 0\n", z3.sat),
    ("1 0\n-1 0\n", z3.unsat),
    ("0\n", z3.unsat),
    ("", z3.sat),
])
def test_prefixless_dimacs_is_legal(clauses, expected):
    formula = translated(f"p cnf 1 {clauses.count(chr(10))}\n" + clauses)
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == expected


@pytest.mark.parametrize("prefix", ["a 1 0\ne 3 0\n", "e 2 0\na 1 0\ne 3 0\n"])
def test_implicit_exists_precedes_universal(prefix):
    # The two inputs must mean the same closed formula. An inner completion
    # forall x1. exists x2,x3. (x1 == x2) and x3 is true instead of false.
    source = "p cnf 3 3\n" + prefix + "-1 2 0\n1 -2 0\n3 0\n"
    actual = translated(source)
    x1, x2, x3 = z3.Bools("x1 x2 x3")
    expected = z3.Exists(x2, z3.ForAll(x1, z3.Exists(x3, z3.And(x1 == x2, x3))))
    proof = z3.Solver()
    proof.add(z3.Xor(actual, expected))
    assert proof.check() == z3.unsat
    verdict = z3.Solver()
    verdict.add(actual)
    assert verdict.check() == z3.unsat
    wrong = z3.Solver()
    wrong.add(z3.ForAll(x1, z3.Exists([x2, x3], z3.And(x1 == x2, x3))))
    assert wrong.check() == z3.sat


@pytest.mark.parametrize("explicit_outer", [False, True])
@pytest.mark.parametrize("flip", [False, True])
def test_partial_prefix_preserves_implicit_choices(explicit_outer, flip):
    # One implicit variable is fixed true (or false), independently of x1.
    # An accidental universal closure would reject this satisfiable formula.
    prefix = ("e 4 0\n" if explicit_outer else "") + "a 1 0\ne 3 0\n"
    literal = "-2" if flip else "2"
    clauses = f"{literal} 0\n-1 3 0\n1 -3 0\n4 -4 0\n{literal} {literal} 0\n"
    actual = translated("p cnf 4 5\n" + prefix + clauses)
    x1, x2, x3, x4 = z3.Bools("x1 x2 x3 x4")
    condition = z3.Not(x2) if flip else x2
    expected = z3.Exists([x2, x4], z3.ForAll(x1, z3.Exists(x3, z3.And(condition, x1 == x3))))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(actual)
    assert solver.check() == z3.sat


def test_literal_magnitude_must_fit_before_absolute_value():
    result = sp.translate(source="p cnf 1 1\n-9223372036854775808 0\n", language="qdimacs")
    assert not result.ok
    assert any("not a literal" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("source", [
    "p cnf 1 1 junk\ne 1 0\n1 0\n",
    "p cnf 1 1\ne 1 0 -1 0\n1 0\n",
])
def test_header_and_prefix_lines_do_not_discard_trailing_tokens(source):
    result = sp.translate(source=source, language="qdimacs")
    assert not result.ok
    assert any("unexpected token" in d.message for d in result.diagnostic_items)


def _qbf_truth(prefix, clauses):
    """Exhaustive Boolean semantics independent of Z3 and the translator."""
    variables = [variable for _, block in prefix for variable in block]
    truth = []
    for values in itertools.product((False, True), repeat=len(variables)):
        assignment = dict(zip(variables, values))
        truth.append(all(any(assignment[abs(lit)] == (lit > 0) for lit in clause)
                         for clause in clauses))
    for kind, block in reversed(prefix):
        width = 1 << len(block)
        reduce = any if kind == "e" else all
        truth = [reduce(truth[at:at + width]) for at in range(0, len(truth), width)]
    return truth[0]



@pytest.mark.parametrize("outer", ["e", "a"])
@pytest.mark.parametrize("clauses", [((1, -2), (-1, 2)), ((1, 2), (-1, -2)),
                                    ((1, -1),), ((1,), (-1,))])
def test_quantifier_order_matches_exhaustive_boolean_semantics(outer, clauses):
    prefix = [(outer, (1,)), ("a" if outer == "e" else "e", (2,))]
    source = "p cnf 2 %d\n" % len(clauses)
    source += "".join(kind + " " + " ".join(map(str, variables)) + " 0\n"
                      for kind, variables in prefix)
    source += "".join(" ".join(map(str, clause)) + " 0\n" for clause in clauses)
    actual = translated(source)
    expected = _qbf_truth(prefix, clauses)
    solver = z3.Solver(); solver.add(z3.Xor(actual, z3.BoolVal(expected)))
    assert solver.check() == z3.unsat
    solver = z3.Solver(); solver.add(actual)
    assert solver.check() == (z3.sat if expected else z3.unsat)
