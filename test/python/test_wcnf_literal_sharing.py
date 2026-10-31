"""Check complete hard relations and weighted costs after literal sharing."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("old_format", [False, True])
def test_repeated_literals_preserve_hard_constraints_and_exact_total_cost(old_format):
    header = "p wcnf 4 6 1000000000000000000\n" if old_format else ""
    hard = "1000000000000000000" if old_format else "h"
    source = (header + hard + " 1 1 -2 0\n"
              "3 1 1 -2 0\n11 1 1 -2 0\n7 -1 2 0\n"
              "9007199254740993 -2 0\n5 0\n")
    result = sp.translate(source=source, language="wcnf")
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2(sp.OmtDialect.Z3)
    target = z3.Optimize()
    target.from_string(text)
    x1, x2 = z3.Bools("x1 x2")
    hard_formula = z3.Or(x1, z3.Not(x2))
    cost = (z3.If(hard_formula, 0, 14)
            + z3.If(z3.Or(z3.Not(x1), x2), 0, 7)
            + z3.If(x2, 9007199254740993, 0) + 5)
    assert len(target.objectives()) == 1
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Or(z3.Xor(z3.And(*target.assertions()), hard_formula),
                     target.objectives()[0] != cost))
    assert solver.check() == z3.unsat
    if old_format:
        assert "declare-fun x4 () Bool" in text


def test_hard_empty_clause_stays_infeasible():
    result = sp.translate(source="h 0\n3 1 0\n4 1 0\n", language="wcnf")
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert target.check() == z3.unsat


def test_unrepresentable_literal_is_diagnosed_before_absolute_value():
    result = sp.translate(source="h 1 0\n7 -9223372036854775808 0\n", language="wcnf")
    assert not result.ok
    error = next(d for d in result.diagnostic_items if d.severity == sp.Severity.ERROR)
    assert error.line == 2
    assert "magnitude" in error.message
