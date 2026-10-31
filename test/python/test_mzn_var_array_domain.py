"""Var-array predicate element domains constrain actual cells outside negation."""

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _check(call, value):
    source = (
        "set of int: allowed = 1..3;"
        "array[1..1] of var int: x;"
        "predicate p(array[int] of var allowed: a) = true;"
        f"constraint {call}; constraint x[1] = {value}; solve satisfy;"
    )
    result = sp.translate(source=source, language="minizinc", profile="bmc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


def test_var_array_domain_is_hard_for_positive_call():
    assert _check("p(x)", 7) == z3.unsat
    assert _check("p(x)", 2) == z3.sat


def test_var_array_domain_is_hard_under_predicate_negation():
    assert _check("not p(x)", 7) == z3.unsat
    # The body is true, so its negation is false independently of the domain.
    assert _check("not p(x)", 2) == z3.unsat
