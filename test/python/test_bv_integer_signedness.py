"""Cross-frontend conversions agree with independent signed/unsigned values."""
import pytest
import somtparser as sp
import z3


def relation(source, language="smtlib2"):
    result = sp.translate(source=source, language=language)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


@pytest.mark.parametrize("operator", ["bv2int", "bv2nat", "ubv_to_int", "sbv_to_int"])
@pytest.mark.parametrize("width", [1, 4, 8, 65])
def test_symbolic_conversion_preserves_full_signed_or_unsigned_relation(operator, width):
    source = (f"(declare-const x (_ BitVec {width})) (declare-const y Int) "
              f"(assert (= y ({operator} x))) (check-sat)")
    x, y = z3.BitVec("x", width), z3.Int("y")
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(relation(source), y == z3.BV2Int(x, operator == "sbv_to_int")))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("operator", ["bv2int", "bv2nat", "ubv_to_int", "sbv_to_int"])
@pytest.mark.parametrize("width", [1, 8, 65])
def test_constant_conversion_uses_same_interpretation_as_symbolic_input(operator, width):
    for bits in {0, (1 << (width - 1)) - 1, 1 << (width - 1), (1 << width) - 1}:
        expected = bits - (1 << width) if operator == "sbv_to_int" and bits >= (1 << (width - 1)) else bits
        source = ("(declare-const y Int) "
                  f"(assert (= y ({operator} (_ bv{bits} {width})))) (check-sat)")
        solver = z3.Solver()
        solver.set(timeout=5000)
        solver.add(z3.Xor(relation(source), z3.Int("y") == expected))
        assert solver.check() == z3.unsat


@pytest.mark.parametrize("signed", [False, True])
@pytest.mark.parametrize("width", [8, 64])
@pytest.mark.parametrize("wrong", [False, True])
def test_cryptoline_algebraic_postcondition_reads_declared_signedness(signed, width, wrong):
    bits = (1 << width) - 1
    expected = (-1 if signed else bits) + int(wrong)
    source = ("proc main() =\n{ true && true }\n"
              f"mov y {'-1' if signed else bits}@{'sint' if signed else 'uint'}{width};\n"
              f"{{ eqn y = {expected} && true }}\n")
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(relation(source, "cryptoline"))
    # CryptoLine exports a counterexample query for the postcondition.
    assert solver.check() == (z3.sat if wrong else z3.unsat)
