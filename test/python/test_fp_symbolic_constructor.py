"""Independent round-trip checks for symbolic IEEE bit constructors."""
import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize("eb,sb", [(8,24),(11,53)])
@pytest.mark.parametrize("predicate", [
    "(= {term} (_ +zero {eb} {sb}))",
    "(fp.eq {term} (_ +zero {eb} {sb}))",
    "(distinct {term} (_ +zero {eb} {sb}))",
    "(fp.isNormal {term})", "(fp.isSubnormal {term})",
    "(fp.isZero {term})", "(fp.isInfinite {term})",
    "(fp.isNaN {term})", "(fp.isNegative {term})", "(fp.isPositive {term})",
])
def test_symbolic_fp_constructor_preserves_predicate(eb,sb,predicate):
    width=eb+sb
    term=f"(fp ((_ extract {width-1} {width-1}) bits) ((_ extract {width-2} {sb-1}) bits) ((_ extract {sb-2} 0) bits))"
    source=(f"(set-logic QF_FPBV)(declare-const bits (_ BitVec {width}))"
            f"(assert {predicate.format(term=term,eb=eb,sb=sb)})(check-sat)")
    parser=sp.Parser();parser.set_command_logging(True);parser.parse_string(source)
    target=parser.dump_smt2()
    solver=z3.Solver();solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(source)),z3.And(*z3.parse_smt2_string(target))))
    assert solver.check()==z3.unsat, target
