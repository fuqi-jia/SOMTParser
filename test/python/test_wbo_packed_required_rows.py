"""Required weighted comparisons retain strict WBO feasibility and exact costs."""
from itertools import product

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.fixture(scope="module")
def padding():
    # Reach the existing threshold through one weighted row, so no unrelated
    # unweighted row can activate compact storage and hide a missing promotion.
    return "+0 xpad " * 65536


def translate(source):
    result = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert result.ok, [item.message for item in result.diagnostic_items]
    return result, result.to_smt2(sp.OmtDialect.Z3)


@pytest.mark.parametrize("relation,rhs,wanted", [(">=", 1, 1), ("<=", 0, 0), ("=", 1, 1)])
@pytest.mark.parametrize("extra_weight", [0, 1])
def test_bigint_required_weighted_rows_preserve_each_assignment_cost(padding, relation, rhs, wanted, extra_weight):
    top = 10**80 + 1
    source = f"soft: {top};\n[{top + extra_weight}] {padding}+1 x1 {relation} {rhs};\n"
    source += "[3] +1 x2 >= 1;\n[4] +1 ~x3 >= 1;\n"
    result, script = translate(source)
    assert result.uses_packed_smt_stream
    assert any(choice.strategy in ("packed-linear-rows", "packed-exact-weighted-violations") for choice in result.report.choices)
    for x1, x2, x3 in product((0, 1), repeat=3):
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(z3.Int("x1") == x1, z3.Int("x2") == x2,
                z3.Int("x3") == x3, z3.Int("xpad") == 0)
        assert opt.check() == (z3.sat if x1 == wanted else z3.unsat)
        if x1 == wanted:
            assert opt.model().eval(opt.objectives()[0]).as_long() == 3*(1-x2)+4*x3
    # The zero-only source coordinate is still a binary declaration.
    for outside in (-1, 2):
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(z3.Int("xpad") == outside)
        assert opt.check() == z3.unsat


def test_weight_below_top_must_stay_soft_and_strict_sum_boundary_is_retained(padding):
    # The first weighted row activates compact storage. The second weighs
    # T-1 and must remain violable; violating the third as well reaches T and
    # must be rejected. A >= versus > mistake at either boundary is observable.
    top = 10**75 + 3
    source = f"soft: {top};\n[{top}] {padding}= 0;\n"
    source += f"[{top-1}] +1 x1 >= 1;\n[1] +1 x2 >= 1;\n"
    result, script = translate(source)
    assert result.uses_packed_smt_stream
    for x1, x2 in product((0, 1), repeat=2):
        expected_cost = (top-1)*(1-x1)+(1-x2)
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(z3.Int("x1") == x1, z3.Int("x2") == x2)
        assert opt.check() == (z3.sat if expected_cost < top else z3.unsat)
        if expected_cost < top:
            assert opt.model().eval(opt.objectives()[0]).as_long() == expected_cost


def test_zero_top_is_unsatisfiable_even_if_every_required_row_holds(padding):
    result, script = translate(f"soft: 0;\n[1] {padding}+1 x1 >= 0;\n")
    assert result.uses_packed_smt_stream
    opt = z3.Optimize()
    opt.from_string(script)
    assert opt.check() == z3.unsat


def test_infinite_top_does_not_turn_weighted_rows_into_hard_rows(padding):
    # A weighted row remains violable, with its actual cost, when the top is
    # infinite. No finite value may replace infinity.
    result, script = translate(f"soft: ;\n[9] {padding}+1 x1 >= 1;\n")
    assert result.uses_packed_smt_stream
    opt = z3.Optimize()
    opt.from_string(script)
    opt.add(z3.Int("x1") == 0)
    assert opt.check() == z3.sat
    assert opt.model().eval(opt.objectives()[0]).as_long() == 9
