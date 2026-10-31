"""Full feasible-set and signed-cost checks for LP's shared packed backend."""
from fractions import Fraction

import pytest
import somtparser as sp
import z3


def translated(text, *, packed=True, options=None):
    result = sp.translate(source=text, language="lp", dialect=sp.OmtDialect.Z3,
                          options=options or {})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.uses_packed_smt_stream == packed
    assert result.report.fidelity.sound and result.report.fidelity.complete
    assert result.report.fidelity.preserves_optimum
    target = z3.Optimize()
    target.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    return result, target


def unsat(*constraints):
    solver = z3.Solver()
    solver.add(*constraints)
    assert solver.check() == z3.unsat


def sat(*constraints):
    solver = z3.Solver()
    solver.add(*constraints)
    assert solver.check() == z3.sat


@pytest.mark.parametrize("relation,false_constant", [
    ("<=", False), (">=", False), ("=", False), ("range", False), ("range", True),
])
def test_wide_rows_exact_constants_domains_and_vacuous_rows(relation, false_constant):
    repeats = 16384
    group = " + 9007199254740993 x - 9007199254740992 x + .125e1 i + 0 s"
    expression = group * repeats + " + .1 + .2"
    row = ("-2.5 <= " + expression + " <= 7.25" if relation == "range"
           else expression + f" {relation} 7.25")
    text = ("Minimize\n cost: .1 x + b + s\nSubject To\n r: " + row
            + "\nconstant: .1 + .2 = " + (".4" if false_constant else ".3")
            + "\nempty: <= 0\nrange_constant: -.2 <= .1 + .2 <= .3\n"
              "Bounds\n x free\n -2 <= i <= 4\n b = 0\n 2 <= s <= 4\n"
              "Generals\n i s\nBinary\n b\nSemi-Continuous\n s\nEnd\n")
    result, target = translated(text)
    x = z3.Real("x")
    i, b, s = z3.Ints("i b s")
    lhs = repeats * (x + z3.RealVal("1.25") * i) + z3.RealVal(".3")
    row_expected = {
        "<=": lhs <= z3.RealVal("7.25"), ">=": lhs >= z3.RealVal("7.25"),
        "=": lhs == z3.RealVal("7.25"),
        "range": z3.And(lhs >= z3.RealVal("-2.5"), lhs <= z3.RealVal("7.25")),
    }[relation]
    expected = z3.And(i >= -2, i <= 4, b >= 0, b <= 1, b == 0,
                      z3.Or(s == 0, z3.And(s >= 2, s <= 4)),
                      row_expected, not false_constant)
    actual = z3.And(*target.assertions())
    unsat(z3.Xor(actual, expected))
    assert result.report.stats.num_objectives == 1
    cost = z3.RealVal(".1") * x + b + s
    # Do not use an inconsistent feasible set to prove a cost identity.
    unsat(target.objectives()[0] != cost)
    if not false_constant:
        witness = (z3.RealVal("7.25") - z3.RealVal(".3")) / repeats
        sat(actual, x == witness, i == 0, b == 0, s == 0)
        unsat(actual, s == 1)
        # Removing the source binary equality genuinely admits an extra point.
        sat(i == 0, b == 1, s == 0, x == witness, row_expected, z3.Not(expected))


@pytest.mark.parametrize("mode", ["constants", "variables"])
def test_packed_numeric_lhs_reader_modes_remain_distinct(mode):
    text = ("Minimize x\nSubject To\nr: " + " + 0 x" * 65536
            + " + x + 1 >= 2\nBounds\nx free\nEnd\n")
    _, target = translated(text, options={"lhs_numbers": mode})
    x, numeral = z3.Reals("x 1")
    expected = x >= 1 if mode == "constants" else z3.And(numeral >= 0, x + numeral >= 2)
    unsat(z3.Xor(z3.And(*target.assertions()), expected))
    unsat(target.objectives()[0] != x)


@pytest.mark.parametrize("maximize,offset,zeros", [
    (False, "-1.25", False), (True, "9007199254740993.125", False),
    (False, ".375", True),
])
def test_wide_cost_unique_private_extension_and_objective_name_collision(maximize, offset, zeros):
    # Two source columns and the objective label occupy the first three helper
    # spellings. None may be captured by the new private value coordinate.
    group = " + 0 x + 0 x + 0 i + 0 i" if zeros else " + .125 x - .125 x - .25 i + .3125 i"
    text = (("Maximize" if maximize else "Minimize") + "\n__somt_lp_objective_value2:"
            + group * 16384 + " + " + offset
            + "\nSubject To\na: x + i <= 3\nb: x - i >= -2\nBounds\n"
              "-2 <= x <= 4\n-2 <= i <= 4\n__somt_lp_objective_value free\n"
              "__somt_lp_objective_value1 free\nGenerals\ni\nEnd\n")
    result, target = translated(text)
    x = z3.Real("x")
    i = z3.Int("i")
    helper = z3.Real("__somt_lp_objective_value3")
    source_cost = z3.RealVal(str(Fraction(offset))) + (0 if zeros else 1024 * i)
    expected = z3.And(x >= -2, x <= 4, i >= -2, i <= 4, x + i <= 3, x - i >= -2)
    assertions = list(target.assertions())
    actual = z3.And(*assertions)
    assert result.report.stats.num_vars == 5
    assert len(target.objectives()) == 1
    # Full relation under the explicit unique extension, and necessity of that
    # extension under every target solution. No optimum-only comparison.
    unsat(z3.Xor(z3.substitute(actual, (helper, source_cost)), expected))
    unsat(actual, z3.Not(expected))
    unsat(actual, helper != source_cost)
    unsat(actual, target.objectives()[0] != (-source_cost if maximize else source_cost))
    sat(actual, x == 1, i == 1, z3.Real("__somt_lp_objective_value") == -7,
        z3.Real("__somt_lp_objective_value1") == 13)
    # Without the defining equality the target cost becomes unconstrained.
    without_definition = [a for a in assertions if "__somt_lp_objective_value3" not in a.sexpr()]
    assert len(without_definition) == len(assertions) - 1
    sat(*without_definition, x == 1, i == 1, helper != source_cost)
    sat(actual, x == 1, i == 1, target.objectives()[0] !=
        (-source_cost - 1 if maximize else source_cost + 1))


def test_packed_linear_rows_coexist_with_exact_quadratic_rows_and_cost():
    text = ("Minimize cost: [ x ^ 2 ] / 3 + .125 i\nSubject To\nlinear:"
            + " + x" * 65536 + " <= 65536\nquadratic: [ x ^ 2 ] / 3 <= 1\n"
              "Bounds\nx free\ni free\nGenerals\ni\nEnd\n")
    _, target = translated(text)
    x, i = z3.Real("x"), z3.Int("i")
    expected = z3.And(x <= 1, x * x / 3 <= 1)
    unsat(z3.Xor(z3.And(*target.assertions()), expected))
    unsat(target.objectives()[0] != x * x / 3 + z3.RealVal(".125") * i)
    sat(*target.assertions(), x == -1, i == 0)
    # The nonlinear row must not be lost merely because a matrix is packed.
    sat(x <= 1, z3.Not(expected), x == -2)


def test_many_short_rows_stream_the_whole_model():
    rows = "".join(f"r{n}: x <= 3\n" for n in range(65536))
    result, target = translated("Minimize x\nSubject To\n" + rows + "Bounds\nx free\nEnd\n")
    assert result.report.stats.num_constraints == 65536
    # Z3 may hash-cons duplicate ASTs, but the parser retains each assertion.
    assert len(target.assertions()) == 65536
    x = z3.Real("x")
    unsat(z3.Xor(z3.And(*target.assertions()), x <= 3))
    unsat(target.objectives()[0] != x)


def test_wide_quadratic_objective_retains_ordinary_fallback():
    text = ("Minimize cost:" + " + x" * 65536 + " + [ x ^ 2 ] / 3\n"
            "Subject To\nr: x <= 1\nBounds\nx free\nEnd\n")
    _, target = translated(text, packed=False)
    x = z3.Real("x")
    unsat(z3.Xor(z3.And(*target.assertions()), x <= 1))
    unsat(target.objectives()[0] != 65536 * x + x * x / 3)
