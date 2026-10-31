"""LP compact matrix storage preserves the whole public relation and signed cost."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def load(source, options=None):
    translated = sp.translate(source=source, language="lp", options=options or {},
                              dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert translated.uses_packed_smt_stream
    optimizer = z3.Optimize()
    optimizer.from_string(translated.to_smt2(sp.OmtDialect.Z3))
    return translated, optimizer


def equal_relation(optimizer, expected):
    check = z3.Solver()
    check.add(z3.Xor(z3.And(*optimizer.assertions()), expected))
    assert check.check() == z3.unsat


@pytest.mark.parametrize("relation", ["<=", ">=", "=", "range"])
def test_wide_rows_preserve_duplicates_constants_domains_and_signed_cost(relation):
    repeated = " + 0.125 x - 0.25 y\n" * 32768
    row = (" -2.5 <= " + repeated.replace("\n", " ") + " + 0.25 - 0.5 <= 7.5\n" if relation == "range"
           else "\n" + repeated + " + 0.25 - 0.5 " + relation + " 7.5\n")
    text = ("Maximize\n cost: x - 0.5 y + 0.75 s + 1.25\nSubject To\n r:" + row
            + "Bounds\n x free\n y = 0\n 2 <= s <= 4\nBinary\n y\nSemi Continuous\n s\nEnd\n")
    _, optimizer = load(text)
    x, s = z3.Reals("x s")
    y = z3.Int("y")
    total = 4096 * x - 8192 * y - z3.RealVal("0.25")
    bound = {"<=": total <= z3.RealVal("7.5"), ">=": total >= z3.RealVal("7.5"),
             "=": total == z3.RealVal("7.5"),
             "range": z3.And(total >= z3.RealVal("-2.5"), total <= z3.RealVal("7.5"))}[relation]
    equal_relation(optimizer, z3.And(y == 0, z3.Or(s == 0, z3.And(s >= 2, s <= 4)), bound))
    check = z3.Solver()
    check.add(optimizer.objectives()[0] != -(x - z3.RealVal("0.5") * y
              + z3.RealVal("0.75") * s + z3.RealVal("1.25")))
    assert check.check() == z3.unsat


def test_packed_matrix_keeps_quadratic_row_and_quadratic_objective():
    text = ("Minimize\n cost: [ 2 x^2 ] / 3 + 0.1\nSubject To\n row:\n"
            + " + 1 x\n" * 65536 + " <= 65536\n q: [ x^2 ] <= 4\nBounds\n x free\nEnd\n")
    _, optimizer = load(text)
    x = z3.Real("x")
    equal_relation(optimizer, z3.And(x <= 1, x * x <= 4))
    check = z3.Solver()
    check.add(optimizer.objectives()[0] != z3.RealVal("2/3") * x * x + z3.RealVal("0.1"))
    assert check.check() == z3.unsat


def test_wide_objective_private_value_preserves_negative_optimum():
    text = ("Minimize\n cost:\n" + " + 0.125 x\n" * 65536
            + " - 1.25\nSubject To\n r: x >= -2\nBounds\n x free\nGeneral\n x\nEnd\n")
    translated, optimizer = load(text)
    x = z3.Int("x")
    value = z3.Real("__somt_lp_objective_value")
    expected = z3.And(x >= -2, value == 8192 * x - z3.RealVal("1.25"))
    equal_relation(optimizer, expected)
    check = z3.Solver()
    check.add(*optimizer.assertions(), optimizer.objectives()[0] != 8192 * x - z3.RealVal("1.25"))
    assert check.check() == z3.unsat
    assert optimizer.check() == z3.sat
    assert str(optimizer.model().eval(optimizer.objectives()[0])) == "-65541/4"
    assert translated.report.fidelity.preserves_optimum


def test_packing_keeps_numeric_lhs_variable_convention():
    text = ("Minimize\n cost: x\nSubject To\n row:\n" + " + 0 x\n" * 65536
            + " + 17 = 3\nBounds\n x free\nEnd\n")
    _, optimizer = load(text, {"lhs_numbers": "variables"})
    numeric_variable = z3.Real("17")
    equal_relation(optimizer, z3.And(numeric_variable == 3, numeric_variable >= 0))
    assert optimizer.check() == z3.sat
    _, constants = load(text, {"lhs_numbers": "constants"})
    assert constants.check() == z3.unsat


def test_packing_does_not_skip_invalid_later_row():
    text = ("Minimize\n cost: x\nSubject To\n row:\n" + " + x\n" * 65536
            + " <= 65536\n broken: x <= no_number\nEnd\n")
    translated = sp.translate(source=text, language="lp")
    assert not translated.ok
    assert any("not a number" in d.message for d in translated.diagnostic_items)
