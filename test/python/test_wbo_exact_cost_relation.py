"""WBO cost is exactly the sum of violated rows, on every source assignment."""
import pytest
import z3
from z3.z3util import get_vars

import somtparser as sp


def _relation(source):
    translated = sp.translate(source=source, language="opb")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    target = z3.Optimize()
    target.from_string(translated.to_smt2(sp.OmtDialect.Z3))
    assert len(target.objectives()) == 1
    x1, x2 = z3.Ints("x1 x2")
    cost = z3.Int("__wbo_observed_cost")
    body = z3.And(*target.assertions(), cost == target.objectives()[0])
    private = [v for v in get_vars(body)
               if not any(v.eq(observed) for observed in (x1, x2, cost))]
    return z3.Exists(private, body) if private else body, x1, x2, cost


@pytest.mark.parametrize("operator", ["=", "!=", ">=", "<=", ">", "<"])
@pytest.mark.parametrize("weight", [2, 10**80 + 1])
def test_all_assignments_have_exact_nonlinear_violation_cost(operator, weight):
    top = weight + 3
    source = (f"soft: {top} ;\n"
              f"[{weight}] +1 x1 ~x2 {operator} 1 ;\n"
              "[3] +1 ~x1 +1 x2 >= 1 ;\n"
              "+1 x1 +1 x2 >= 1 ;\n")
    actual, x1, x2, cost = _relation(source)
    lhs = x1 * (1 - x2)
    first = {"=": lhs == 1, "!=": lhs != 1, ">=": lhs >= 1,
             "<=": lhs <= 1, ">": lhs > 1, "<": lhs < 1}[operator]
    second = (1 - x1) + x2 >= 1
    expected_cost = z3.If(first, 0, weight) + z3.If(second, 0, 3)
    expected = z3.And(x1 >= 0, x1 <= 1, x2 >= 0, x2 <= 1,
                      x1 + x2 >= 1, expected_cost < top, cost == expected_cost)
    # Quantifies only introduced target variables. This compares the entire
    # feasible decision/cost relation, not just the optimal value or a witness.
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("top", [2, 5, 6])
def test_strict_threshold_and_native_soft_use_the_same_source_cost(top):
    actual, x1, x2, cost = _relation(
        f"soft: {top} ;\n[2] +1 x1 >= 1 ;\n[3] +1 x2 >= 1 ;\n")
    exact_cost = z3.If(x1 == 1, 0, 2) + z3.If(x2 == 1, 0, 3)
    expected = z3.And(x1 >= 0, x1 <= 1, x2 >= 0, x2 <= 1,
                      exact_cost < top, cost == exact_cost)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_oracle_detects_the_old_satisfied_row_with_positive_cost():
    x1, x2, r0, r1, cost = z3.Ints("x1 x2 r0 r1 cost")
    old = z3.Exists([r0, r1], z3.And(
        x1 >= 0, x1 <= 1, x2 >= 0, x2 <= 1,
        r0 >= 0, r0 <= 1, r1 >= 0, r1 <= 1,
        z3.Or(x1 == 1, r0 == 1), z3.Or(x2 == 1, r1 == 1),
        cost == 2 * r0 + 3 * r1, cost < 5))
    solver = z3.Solver()
    solver.add(old, x1 == 1, x2 == 1, cost == 2)
    assert solver.check() == z3.sat
    exact_cost = z3.If(x1 == 1, 0, 2) + z3.If(x2 == 1, 0, 3)
    solver.add(cost == exact_cost)
    assert solver.check() == z3.unsat
