"""The representable signed endpoint must survive tokenization and folding."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")
MINIMUM = -(2**63)


@pytest.mark.parametrize("literal", [
    "-9223372036854775808", "-0009223372036854775808",
    "-0x8000000000000000", "-0o1000000000000000000000",
])
@pytest.mark.parametrize("context", ["term", "parameter", "domain"])
def test_signed_minimum_is_the_exact_integer(literal, context):
    if context == "term":
        source = f"var int:x; constraint x={literal}; solve satisfy;"
    elif context == "parameter":
        source = f"int:k={literal}; var int:x; constraint x=k; solve satisfy;"
    else:
        source = f"var {literal}..{literal}:x; solve satisfy;"
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, z3.Int("x") == MINIMUM))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("expression", [
    "9223372036854775808", "+9223372036854775808",
    "0x8000000000000000", "0o1000000000000000000000",
    "-9223372036854775809", "-0x8000000000000001", "-0o1000000000000000000001",
    "-(-9223372036854775808)", "abs(-9223372036854775808)",
])
def test_out_of_range_constant_still_reports_input_error(expression):
    result = sp.translate(source=f"int:k={expression}; solve satisfy;", language="minizinc")
    assert not result.ok
    assert any("64-bit" in d.message or "overflows" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("tail", ["^0", "default 1"])
def test_minimum_shortcut_does_not_move_minus_inside_tighter_operator(tail):
    # Here the *positive* operand remains outside the frontend's fixed Int64
    # literal subset. Accepting it by folding the adjacent minus would change
    # MiniZinc precedence. The ordinary range diagnostic must be retained.
    result = sp.translate(source=f"int:k=-9223372036854775808 {tail}; solve satisfy;",
                          language="minizinc")
    assert not result.ok
    assert any("64-bit" in d.message for d in result.diagnostic_items)
