"""Constant BV -> FP folding must match independent SMT floating-point semantics."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("signed", [False, True])
@pytest.mark.parametrize("mode", ["RNE", "RNA", "RTP", "RTN", "RTZ"])
@pytest.mark.parametrize("format_", [(3, 4), (5, 11), (8, 24), (11, 53)])
def test_bv_fp_rounding_matches_z3_for_small_and_boundary_values(signed, mode, format_):
    eb, sb = format_
    parser = sp.Parser()
    operation = "to_fp" if signed else "to_fp_unsigned"
    # Exhaust a small BV domain; cover target ties, host sign boundaries, and
    # 64-bit unsigned values that cannot fit in a signed host integer.
    cases = [(4, n) for n in range(16)]
    for width in (8, 16, 32, 64):
        mask = (1 << width) - 1
        values = {0, 1, mask, mask >> 1, 1 << (width - 1)}
        values.update(n & mask for n in (16777217, 16777219, -16777217,
                                         (1 << 53) + 1, (1 << 53) + 3))
        cases.extend((width, n) for n in sorted(values))
    for width, value in cases:
        source = f"((_ {operation} {eb} {sb}) {mode} (_ bv{value} {width}))"
        emitted = parser.to_string(parser.expr(source))
        equality = z3.parse_smt2_string(f"(assert (= {source} {emitted}))")[0]
        assert z3.is_true(z3.simplify(equality)), (source, emitted)
        # Evaluating with an empty model must preserve the same value too.
        evaluated = parser.to_string(parser.evaluate(parser.expr(source), sp.Model()))
        equality = z3.parse_smt2_string(f"(assert (= {source} {evaluated}))")[0]
        assert z3.is_true(z3.simplify(equality)), (source, evaluated)
