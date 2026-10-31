"""A packed objective is a definitional extension, with an unchanged source projection."""
from fractions import Fraction

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _source(*, maximize=False, offset="-1.25", integers=False, zeros=False, quadratic=False):
    text = ["NAME objective", "OBJSENSE", " MAX" if maximize else " MIN", "OBJNAME cost",
            "ROWS", " L before", " N free", " N cost", " G after", "COLUMNS"]
    if integers:
        text.append(" marker0 'MARKER' 'INTORG'")
    spellings = ["0", "0", "0", "0"] if zeros else ["0.125", "-0.25", "-0.125", "0.3125"]
    coefficients = [Fraction(0), Fraction(0)]
    for i in range(65536):
        column = i % 2
        coefficient = spellings[i % len(spellings)]
        coefficients[column] += Fraction(coefficient)
        text.append(f" {'x' if column == 0 else 'y'} cost {coefficient}")
    if integers:
        text.append(" marker1 'MARKER' 'INTEND'")
    text.extend([" x before 1", " y before 1", " x after 1", " y after -1",
                 " x free 999", " __somt_mps_objective_value cost 0",
                 " __somt_mps_objective_value1 cost 0", "RHS", f" rhs cost {offset}",
                 " rhs before 3", " rhs after -2", "BOUNDS", " LO bounds x -2",
                 " UP bounds x 4", " LO bounds y -2", " UP bounds y 4",
                 " FR bounds __somt_mps_objective_value", " FR bounds __somt_mps_objective_value1"])
    if quadratic:
        text.extend(["QUADOBJ", " x x 0.5", " x y -0.25"])
    text.append("ENDATA")
    return "\n".join(text) + "\n", coefficients


def _model(text):
    result = sp.translate(source=text, language="mps", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert len(target.objectives()) == 1
    return result, target


def _unsat(*constraints):
    solver = z3.Solver()
    solver.set(timeout=0)
    solver.add(*constraints)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("maximize,offset,integers,zeros", [
    (False, "-1.25", False, False),
    (True, "9007199254740993.125", True, False),
    (False, "0.375", True, True),
])
def test_wide_objective_has_unique_exact_extension_and_preserves_source_feasibility(
        maximize, offset, integers, zeros):
    text, coefficients = _source(maximize=maximize, offset=offset, integers=integers, zeros=zeros)
    result, target = _model(text)
    assert result.uses_packed_smt_stream
    variable = z3.Int if integers else z3.Real
    x, y = variable("x"), variable("y")
    helper = z3.Real("__somt_mps_objective_value2")
    expected = z3.And(x >= -2, x <= 4, y >= -2, y <= 4, x + y <= 3, x - y >= -2)
    cost = sum(z3.RealVal(str(c)) * v for c, v in zip(coefficients, (x, y))) - z3.RealVal(offset)
    assertions = list(target.assertions())
    actual = z3.And(*assertions)
    # Source assignments extend by helper=cost. Both directions of feasibility
    # are checked after that independent substitution, not merely SAT on a few points.
    _unsat(z3.Xor(z3.substitute(actual, (helper, cost)), expected))
    _unsat(actual, z3.Not(expected))
    _unsat(actual, helper != cost)
    _unsat(actual, target.objectives()[0] != (-cost if maximize else cost))
    solver = z3.Solver()
    solver.add(actual, x == 1, y == 1,
               z3.Real("__somt_mps_objective_value") == -7,
               z3.Real("__somt_mps_objective_value1") == 13)
    assert solver.check() == z3.sat
    # Reject a missing defining equality independently: the remaining source
    # constraints cannot determine the fresh target objective coordinate.
    without_definition = [a for a in assertions if "__somt_mps_objective_value2" not in a.sexpr()]
    solver = z3.Solver()
    solver.add(*without_definition, helper != cost, x == 1, y == 1)
    assert solver.check() == z3.sat


def test_empty_objective_keeps_its_exact_constant_without_an_auxiliary():
    text = "NAME empty\nROWS\n N cost\n L row\nCOLUMNS\n x row 1\nRHS\n rhs cost -0.75\n rhs row 3\nBOUNDS\n FR bounds x\nENDATA\n"
    result, target = _model(text)
    assert result.report.stats.num_vars == 1
    _unsat(target.objectives()[0] != z3.RealVal("0.75"))
    _unsat(z3.Xor(z3.And(*target.assertions()), z3.Real("x") <= 3))


def test_quadratic_wide_objective_keeps_the_existing_exact_encoding():
    text, coefficients = _source(quadratic=True)
    result, target = _model(text)
    assert not result.uses_packed_smt_stream
    assert result.report.stats.num_vars == 4
    x, y = z3.Reals("x y")
    cost = sum(z3.RealVal(str(c)) * v for c, v in zip(coefficients, (x, y)))
    cost += z3.RealVal("1.25") + z3.RealVal("0.25") * x*x - z3.RealVal("0.25") * x*y
    _unsat(target.objectives()[0] != cost)
