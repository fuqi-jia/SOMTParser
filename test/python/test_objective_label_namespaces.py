"""LP/MPS row labels may coincide with columns; target names must stay fresh."""
from fractions import Fraction

import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize("language", ["lp", "mps"])
@pytest.mark.parametrize("constant_only", [False, True])
def test_objective_label_collision_preserves_columns_feasibility_and_cost(language, constant_only):
    if language == "lp":
        term = "1" if constant_only else "2 obj + 3 obj__objective + 1"
        source = (
            f"Minimize\n obj: {term}\nSubject To\n"
            " row: obj + obj__objective <= 12\nBounds\n"
            " obj = 5\n obj__objective = 7\n obj__objective1 = 9\nEnd\n"
        )
    else:
        left, right = (0, 0) if constant_only else (2, 3)
        source = (
            "NAME COLLISION\nROWS\n N obj\n L row\nCOLUMNS\n"
            f"    obj obj {left} row 1\n"
            f"    obj__objective obj {right} row 1\n"
            "    obj__objective1 row 0\nRHS\n"
            "    rhs row 12 obj -1\nBOUNDS\n"
            " FX b obj 5\n FX b obj__objective 7\n FX b obj__objective1 9\nENDATA\n"
        )
    translation = sp.translate(source=source, language=language)
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    optimizer = z3.Optimize()
    optimizer.from_string(translation.to_smt2(dialect=sp.OmtDialect.Z3))
    assert optimizer.check() == z3.sat
    model = optimizer.model()
    expected_cost = 1 if constant_only else 32
    assert z3.is_true(z3.simplify(model.eval(optimizer.objectives()[0]) == expected_cost))
    for name, expected in [("obj", 5), ("obj__objective", 7), ("obj__objective1", 9)]:
        variable = z3.Real(name)
        assert model.eval(variable).as_fraction() == Fraction(expected)
        # Renaming a source column or losing its bound would admit this model.
        solver = z3.Solver()
        solver.add(*optimizer.assertions(), variable != expected)
        assert solver.check() == z3.unsat


def test_default_lp_objective_label_cannot_capture_a_column():
    translation = sp.translate(source="Minimize\n obj\nSubject To\n r: obj >= 3\nEnd\n", language="lp")
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    optimizer = z3.Optimize()
    optimizer.from_string(translation.to_smt2(dialect=sp.OmtDialect.Z3))
    assert optimizer.check() == z3.sat
    assert optimizer.model().eval(z3.Real("obj")).as_fraction() == 3
    assert optimizer.model().eval(optimizer.objectives()[0]).as_fraction() == 3
