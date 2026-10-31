"""Compact hard rows preserve the entire feasible relation and WBO cost."""
from itertools import product

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.fixture(scope="module")
def wide_identity_row():
    # Reach the real term-count threshold without adding another restriction.
    # The zero coefficient still declares a binary output xpad.
    return "+0000 xpad " * 65536 + "= -0000 ;\n"


def translate(source):
    result = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream and not result.has_parser
    assert any(choice.strategy == "packed-linear-rows" for choice in result.report.choices)
    opt = z3.Optimize()
    opt.from_string(result.to_smt2(sp.OmtDialect.Z3))
    return result, opt


@pytest.mark.parametrize("direction", ["min", "max"])
def test_packed_opb_preserves_complete_relation_exact_objective_and_binary_domains(wide_identity_row, direction):
    big = 10**70 + 1
    source = wide_identity_row + (
        "+0001 x01 +0001 x01 <= +0002 ;\n"
        f"+{big} x01 -{big-1} x01 +1 x1 >= 1 ;\n"
        "+1 x1 -1 x2 = -0000 ;\n"
        "+1 ~x01 +1 x2 > 0 ;\n"
        "+1 x01 x2 != 2 ;\n"
        f"{direction}: +{big} x01 -7 x1 +3 ~x2 ;\n")
    _, opt = translate(source)
    a, b, c, pad = z3.Ints("x01 x1 x2 xpad")
    expected = z3.And(*(z3.And(x >= 0, x <= 1) for x in (a, b, c, pad)),
                      2*a <= 2, a+b >= 1, b == c, 1-a+c > 0, a*c != 2)
    check = z3.Solver()
    check.add(z3.Xor(z3.And(*opt.assertions()), expected))
    assert check.check() == z3.unsat
    cost = big*a - 7*b + 3*(1-c)
    check = z3.Solver()
    check.add(opt.objectives()[0] != (cost if direction == "min" else -cost))
    assert check.check() == z3.unsat
    # Explicitly retain a coordinate used only by zero coefficients.
    for outside in (-1, 2):
        check = z3.Solver()
        check.add(*opt.assertions(), pad == outside)
        assert check.check() == z3.unsat


@pytest.mark.parametrize("top", [None, 0, 4, 20])
def test_packed_wbo_hard_rows_keep_soft_threshold_and_each_assignment_cost(wide_identity_row, top):
    source = "soft: " + ("" if top is None else str(top)) + " ;\n"
    source += wide_identity_row + "+1 x01 +1 x1 >= 1 ;\n"
    source += "[3] +1 x01 >= 1 ;\n[4] +1 ~x1 >= 1 ;\n"
    result, parsed = translate(source)
    assert result.report.fidelity.preserves_optimum
    script = result.to_smt2(sp.OmtDialect.Z3)
    for a, b in product((0, 1), repeat=2):
        cost = 3*(1-a)+4*b
        feasible = a+b >= 1 and (top is None or cost < top)
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(z3.Int("x01") == a, z3.Int("x1") == b, z3.Int("xpad") == 0)
        assert opt.check() == (z3.sat if feasible else z3.unsat)
        if feasible:
            assert opt.model().eval(opt.objectives()[0]).as_long() == cost


def test_packed_hard_rows_do_not_drop_a_duplicate_coefficient(wide_identity_row):
    _, opt = translate(wide_identity_row + "+1 x1 +1 x1 <= 1 ;\n")
    solver = z3.Solver()
    solver.add(*opt.assertions(), z3.Int("x1") == 1)
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(*opt.assertions(), z3.Int("x1") == 0)
    assert solver.check() == z3.sat
