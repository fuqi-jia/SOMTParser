"""Packed MPS rows preserve the source relation and exact objective in Z3."""
from fractions import Fraction

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def source(row_type="L", rhs="2", span=None, *, packed=True, exact_duplicate=False):
    rows = 65536 if packed else 1
    text = ["NAME compact", "OBJNAME objective", "ROWS", " N free", " N objective",
            f" {row_type} row"]
    text += [f" E padding{i}" for i in range(rows - 1)]
    text += ["COLUMNS", " x free 99", " x objective 1", " y objective 1.25",
             " s objective 1"]
    if exact_duplicate:
        text += [" x row 9007199254740993", " x row -9007199254740992"]
    else:
        text += [" x row 1", " y row 0.25", " s row 0"]
    text += ["RHS", " rhs objective 2.5"]
    if rhs is not None:
        text += [f" rhs row {rhs}"]
    if span is not None:
        text += ["RANGES", f" range row {span}"]
    text += ["BOUNDS", " FR bounds x", " BV bounds y", " LO bounds s 2",
             " SC bounds s 4", "ENDATA"]
    return "\n".join(text) + "\n"


def translate(text, packed):
    result = sp.translate(source=text, language="mps", dialect=sp.OmtDialect.Z3)
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream == packed
    assert result.has_parser != packed
    assert result.report.stats.num_constraints == (65536 if packed else 1) + 1
    assert result.report.stats.num_objectives == 1
    assert result.report.fidelity.sound and result.report.fidelity.complete
    assert result.report.fidelity.preserves_optimum
    target = result.to_smt2(sp.OmtDialect.Z3)
    opt = z3.Optimize()
    opt.from_string(target)  # independent parser, including exact Real/Int sorts
    return result, opt


def row_bounds(row_type, rhs, span):
    rhs = Fraction(rhs or "0")
    if span is None:
        return (None, rhs) if row_type == "L" else (rhs, None) if row_type == "G" else (rhs, rhs)
    width = Fraction(span)
    if row_type == "L":
        return rhs - abs(width), rhs
    if row_type == "G":
        return rhs, rhs + abs(width)
    return (rhs, rhs + width) if width >= 0 else (rhs + width, rhs)


@pytest.mark.parametrize("row_type,rhs,span", [
    ("L", "2", "-3"), ("G", "-2", "3"),
    ("E", "1", "2"), ("E", "1", "-2"),
    ("L", None, None), ("G", None, None), ("E", "1.25", None),
])
def test_packed_row_feasible_set_matches_source(row_type, rhs, span):
    x, s = z3.Reals("x s")
    y = z3.Int("y")
    lo, hi = row_bounds(row_type, rhs, span)
    lhs = x + z3.RealVal("0.25") * y
    expected = z3.And(y >= 0, y <= 1, z3.Or(s == 0, z3.And(s >= 2, s <= 4)),
                      True if lo is None else lhs >= z3.RealVal(str(lo)),
                      True if hi is None else lhs <= z3.RealVal(str(hi)))
    for packed in (False, True):
        result, opt = translate(source(row_type, rhs, span, packed=packed), packed)
        check = z3.Solver()
        check.add(z3.Xor(expected, z3.And(*opt.assertions())))
        assert check.check() == z3.unsat
        assert len(opt.objectives()) == 1
        check = z3.Solver()
        check.add(opt.objectives()[0] != x + z3.RealVal("1.25") * y + s - z3.RealVal("2.5"))
        assert check.check() == z3.unsat
        assert any(choice.strategy == "packed-linear-rows" for choice in result.report.choices) == packed
    # An explicit source-domain counterexample remains infeasible: s=1 lies
    # between the isolated zero and the semicontinuous interval [2,4].
    check = z3.Solver()
    check.add(*opt.assertions(), s == 1)
    assert check.check() == z3.unsat


def test_repeated_large_coefficients_are_summed_exactly():
    x, s = z3.Reals("x s")
    y = z3.Int("y")
    expected = z3.And(x == 1, y >= 0, y <= 1,
                      z3.Or(s == 0, z3.And(s >= 2, s <= 4)))
    _, opt = translate(source("E", "1", packed=True, exact_duplicate=True), True)
    check = z3.Solver()
    check.add(z3.Xor(expected, z3.And(*opt.assertions())))
    assert check.check() == z3.unsat
    check = z3.Solver()
    check.add(*opt.assertions(), x == 1, y == 0, s == 0)
    assert check.check() == z3.sat
    check.add(x == 2)
    assert check.check() == z3.unsat


def test_packed_semiinteger_maximum_and_quadratic_objective():
    # SI changes the column's domain as well as its zero-or-band constraint.
    # A diagonal QUADOBJ coefficient is halved; the off-diagonal is not.
    text = source("E", "1", packed=True)
    text = text.replace("NAME compact\n", "NAME compact\nOBJSENSE MAX\n")
    text = text.replace(" SC bounds s 4", " SI bounds s 4")
    text = text.replace("ENDATA\n", "QUADOBJ\n x x 0.2\n x y -2\nENDATA\n")
    x = z3.Real("x")
    y, s = z3.Ints("y s")
    _, opt = translate(text, True)
    expected = z3.And(x + z3.RealVal("0.25") * y == 1, y >= 0, y <= 1,
                      z3.Or(s == 0, z3.And(s >= 2, s <= 4)))
    check = z3.Solver()
    check.add(z3.Xor(expected, z3.And(*opt.assertions())))
    assert check.check() == z3.unsat
    cost = x + z3.RealVal("1.25") * y + s - z3.RealVal("2.5")
    cost += z3.RealVal("0.1") * x * x - 2 * x * y
    check = z3.Solver()
    # Z3 exposes maximize(cost) as a minimization of -cost.
    check.add(opt.objectives()[0] != -cost)
    assert check.check() == z3.unsat
    check = z3.Solver()
    check.add(*opt.assertions(), s == z3.RealVal("2.5"))
    assert check.check() == z3.unsat


def test_invalid_range_keeps_source_diagnostic_before_packing():
    text = source("E", "1", "2").replace(" range row 2", " range free 2")
    result = sp.translate(source=text, language="mps")
    assert not result.ok
    assert any("RANGES cannot be applied to free N row" in item.message and item.line > 65536
               for item in result.diagnostic_items)


def test_wide_matrix_packs_by_entries_and_preserves_exact_feasible_set():
    # Only two rows, but enough non-unit matrix entries to make ordinary
    # multiplication DAGs expensive. Repeated entries must remain additive.
    repeats = 16384
    text = ["NAME wide", "ROWS", " N cost", " L first", " G second", "COLUMNS",
            " x cost 0.3", " y cost -0.7"]
    text.extend([" x first 0.1 second 0.3", " y first -0.2 second 0.4"] * repeats)
    text.extend(["RHS", " rhs first 2.5 second -7.25", "RANGES", " span second -2.5",
                 "BOUNDS", " FR bounds x", " FR bounds y", "ENDATA"])
    result = sp.translate(source="\n".join(text) + "\n", language="mps",
                          dialect=sp.OmtDialect.Z3)
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream
    assert result.report.stats.num_constraints == 2
    assert result.report.fidelity.sound and result.report.fidelity.complete
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    x, y = z3.Reals("x y")
    first = repeats * (z3.RealVal("0.1") * x - z3.RealVal("0.2") * y)
    second = repeats * (z3.RealVal("0.3") * x + z3.RealVal("0.4") * y)
    expected = z3.And(first <= z3.RealVal("2.5"),
                      second >= z3.RealVal("-7.25"), second <= z3.RealVal("-4.75"))
    check = z3.Solver()
    check.add(z3.Xor(expected, z3.And(*target.assertions())))
    assert check.check() == z3.unsat
    assert len(target.objectives()) == 1
    check = z3.Solver()
    check.add(target.objectives()[0] != z3.RealVal("0.3") * x - z3.RealVal("0.7") * y)
    assert check.check() == z3.unsat
