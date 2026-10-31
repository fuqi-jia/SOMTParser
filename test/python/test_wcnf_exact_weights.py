"""Both WCNF representations preserve complete relations and exact costs."""
import pytest
import z3

import somtparser as sp


@pytest.mark.parametrize("packed", ["0", "1"])
@pytest.mark.parametrize("old_format", [False, True])
@pytest.mark.parametrize("weight", [2**53 + 1, 2**63 - 1, 2**64 - 1, 10**80 + 1])
def test_exact_cost_and_top_classification(packed, old_format, weight):
    top = weight + 9
    header = f"p wcnf 3 5 000{top}\n" if old_format else ""
    hard_equal = f"000{top}" if old_format else "h"
    hard_above = str(top + 1) if old_format else "h"
    source = (header + hard_equal + " 1 2 0\n" + hard_above + " -3 0\n"
              + f"000{weight} -1 0\n{weight - 1} 3 0\n7 0\n")
    result = sp.translate(source=source, language="wcnf", options={"packed": packed})
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    x1, x2, x3 = z3.Bools("x1 x2 x3")
    expected_hard = z3.And(z3.Or(x1, x2), z3.Not(x3))
    expected_cost = z3.If(x1, weight, 0) + z3.If(x3, 0, weight - 1) + 7
    assert len(target.objectives()) == 1
    # Covers every Boolean assignment, including infeasible ones: an exact
    # optimum alone could hide a changed clause or a rounded coefficient.
    proof = z3.Solver()
    proof.add(z3.Or(z3.Xor(z3.And(*target.assertions()), expected_hard),
                    target.objectives()[0] != expected_cost))
    assert proof.check() == z3.unsat


@pytest.mark.parametrize("packed", ["0", "1"])
@pytest.mark.parametrize("top", [None, 10])
def test_large_weight_with_small_or_absent_top(packed, top):
    weight = 10**80 + 1
    marker = "" if top is None else f" {top}"
    source = f"p wcnf 1 2{marker}\n{weight} 1 0\n7 -1 0\n"
    result = sp.translate(source=source, language="wcnf", options={"packed": packed})
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    x1 = z3.Bool("x1")
    expected_hard = z3.BoolVal(True) if top is None else x1
    cost = z3.If(x1, 7, 0)
    if top is None:
        cost += z3.If(x1, 0, weight)
    assert len(target.objectives()) == 1
    proof = z3.Solver()
    proof.add(z3.Or(z3.Xor(z3.And(*target.assertions()), expected_hard),
                    target.objectives()[0] != cost))
    assert proof.check() == z3.unsat


@pytest.mark.parametrize("packed", ["0", "1"])
@pytest.mark.parametrize("token", ["0", "000", "-1", "+1", "1.5", "1e3", "12x"])
def test_weights_remain_positive_decimal_integers(packed, token):
    result = sp.translate(source=f"{token} 1 0\n", language="wcnf",
                          options={"packed": packed})
    assert not result.ok
    assert any(d.severity == sp.Severity.ERROR for d in result.diagnostic_items)


def test_file_stream_matches_inline_input_and_preserves_parser(tmp_path):
    source = "c test\r\np wcnf 2 3 9007199254740994\r\n9007199254740994 1 0\r\n9007199254740993 -2 0\r\n2 2 0"
    path = tmp_path / "stream.wcnf"
    path.write_bytes(source.encode())
    inline = sp.translate(source=source, language="wcnf")
    streamed = sp.translate(path=str(path), language="wcnf")
    assert inline.ok and streamed.ok
    assert streamed.has_parser
    assert inline.to_smt2(sp.OmtDialect.Z3) == streamed.to_smt2(sp.OmtDialect.Z3)
