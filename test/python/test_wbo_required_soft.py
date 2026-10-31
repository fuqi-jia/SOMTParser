"""Compare WBO feasibility and optimum with the source violation-cost definition."""

from itertools import product

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("top", ["0", "+0000", "1", "3", "4", "5", "6",
                                  "7", "+0007", "10", "11", "12", "13",
                                  "14", "16", "17", "18", None])
def test_required_soft_rows_preserve_projected_models_and_optimum(top):
    # These independent Python predicates are the source constraints. They
    # exercise products, complements, signed coefficients, and all relations.
    soft = [
        (3, "+1 x1 >= 1", lambda x, y, w: x >= 1),
        (4, "+1 ~x2 = 1", lambda x, y, w: 1 - y == 1),
        (2, "+2 x1 ~x2 +1 x3 > 1", lambda x, y, w: 2*x*(1-y) + w > 1),
        (5, "+1 x1 -1 x3 <= 0", lambda x, y, w: x - w <= 0),
        (1, "+1 x2 +1 x3 < 2", lambda x, y, w: y + w < 2),
        (2, "+1 x1 x3 != 1", lambda x, y, w: x*w != 1),
    ]
    source = "soft: " + (top or "") + " ;\n"
    source += "+1 x1 +1 x2 +1 x3 >= 1 ;\n"
    source += "\n".join(f"[{cost}] {expr} ;" for cost, expr, _ in soft)
    translated = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    script = translated.to_smt2(sp.OmtDialect.Z3)
    for assignment in product((0, 1), repeat=3):
        expected_cost = sum(cost for cost, _, pred in soft if not pred(*assignment))
        expected_feasible = (sum(assignment) >= 1 and
                             (top is None or expected_cost < int(top)))
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(*(z3.Int(f"x{i}") == value for i, value in enumerate(assignment, 1)))
        actual = opt.check()
        assert actual == (z3.sat if expected_feasible else z3.unsat), assignment
        if expected_feasible:
            assert len(opt.objectives()) == 1
            actual_cost = opt.model().eval(opt.objectives()[0], model_completion=True)
            assert actual_cost.as_long() == expected_cost, assignment


@pytest.mark.parametrize("top", ["0", "+0000", "1", "2", "3", None])
def test_empty_soft_sum_keeps_strict_threshold(top):
    translated = sp.translate(source="soft: " + (top or "") + " ;\n+1 x1 = 1 ;\n",
                              language="opb", dialect=sp.OmtDialect.Z3)
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    opt = z3.Optimize()
    opt.from_string(translated.to_smt2(sp.OmtDialect.Z3))
    assert opt.check() == (z3.unsat if top is not None and int(top) == 0 else z3.sat)


@pytest.mark.parametrize("top", ["9007199254740993", "+09007199254740994",
                                  "184467440737095516160", None])
def test_threshold_and_costs_use_exact_unsigned_decimal_arithmetic(top):
    costs = (9007199254740993, 9007199254740992, 184467440737095516160)
    source = "soft: " + (top or "") + " ;\n"
    source += "\n".join(f"[+0{cost}] +1 x{i} = 1 ;"
                        for i, cost in enumerate(costs, 1))
    translated = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    for assignment in product((0, 1), repeat=3):
        expected_cost = sum(cost for value, cost in zip(assignment, costs) if value == 0)
        expected_feasible = top is None or expected_cost < int(top)
        opt = z3.Optimize()
        opt.from_string(translated.to_smt2(sp.OmtDialect.Z3))
        opt.add(*(z3.Int(f"x{i}") == value for i, value in enumerate(assignment, 1)))
        assert opt.check() == (z3.sat if expected_feasible else z3.unsat), assignment
        if expected_feasible:
            assert opt.model().eval(opt.objectives()[0]).as_long() == expected_cost


@pytest.mark.parametrize("zero", ["0", "00", "+0", "+000", "-0", "-000"])
def test_every_spelling_of_zero_soft_cost_is_rejected(zero):
    translated = sp.translate(source=f"soft: 3 ;\n[{zero}] +1 x1 = 1 ;\n",
                              language="opb", dialect=sp.OmtDialect.Z3)
    assert not translated.ok
    assert any("strictly positive" in item.message for item in translated.diagnostic_items)
