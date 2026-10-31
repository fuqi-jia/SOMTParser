"""The standard integer-to-bitvector spelling preserves modular conversion."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("width", [1, 8, 64])
def test_int_to_bv_preserves_negative_and_wide_integer_values(width):
    result = sp.translate(
        source=f'(set-logic ALL)(declare-const n Int)(declare-const b (_ BitVec {width}))'
               f'(assert (= b ((_ int_to_bv {width}) n)))(check-sat)',
        language="smtlib2")
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    n = z3.Int('n')
    b = z3.BitVec('b', width)
    modulus = 1 << width
    for value in [-2**100-1, -modulus-1, -modulus, -1, 0, 1, modulus-1,
                  modulus, modulus+1, 2**100+255]:
        # Ground the input before solving: this checks the emitted modular
        # relation without asking the solver to synthesize a 64-bit division.
        solver = z3.Solver()
        solver.set(timeout=5000)
        solver.add(z3.simplify(z3.substitute(formula, (n, z3.IntVal(value)))))
        assert solver.check() == z3.sat
        assert solver.model().eval(b).as_long() == value % modulus
        solver.add(b != z3.BitVecVal(value % modulus, width))
        assert solver.check() == z3.unsat


@pytest.mark.parametrize("contradiction", [
    '(not ((_ is cell) (|cell| 3)))',
    '(distinct (|value| (cell 3)) 3)',
    '(not ((_ is |empty|) empty))',
])
def test_quoted_datatype_members_keep_their_declared_identity(contradiction):
    result = sp.translate(
        source='(set-logic ALL)(declare-datatypes ((|Cell| 0)) '
               '(((|cell| (|value| Int)) (|empty|))))'
               f'(assert {contradiction})(check-sat)',
        language="smtlib2")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat
