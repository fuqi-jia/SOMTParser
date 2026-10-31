"""Releasing reader columns preserves packed objectives and source domains."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _source(mode, quadratic=False, collisions=2):
    lines = ["NAME columns", "OBJNAME obj", "ROWS", " N free", " G row", " N obj"]
    if mode == "rows":
        lines.extend(f" E padding{i}" for i in range(65535))
    lines.extend(["COLUMNS", " x free 99", " x obj 2", " x obj -0.5",
                  " x row 1", " x row -0.25", " obj__objective obj -3",
                  " obj__objective1 obj -1", " semi obj 1",
                  " MARK0 'MARKER' 'INTORG'", " obj obj -1", " obj row 2",
                  " MARK1 'MARKER' 'INTEND'"])
    if mode == "terms":
        # Few matrix rows with genuinely repeated, signed coefficients force
        # the term-count threshold. Every pair contributes exactly zero.
        lines.extend([" x row 1", " x row -1"] * 32768)
    extras = [f"obj__objective{i}" for i in range(2, collisions)]
    lines.extend(f" {name} obj 0" for name in extras)
    lines.extend(["RHS", " rhs obj -1.25", " rhs row -2", "BOUNDS",
                  " FR bounds x", " FR bounds obj__objective",
                  " BV bounds obj__objective1", " LO bounds semi 2", " SI bounds semi 4"])
    lines.extend(f" FR bounds {name}" for name in extras)
    if quadratic:
        lines.extend(["QUADOBJ", " x x 0.2", " x obj -2"])
    lines.append("ENDATA")
    return "\n".join(lines) + "\n"


def _check(source, packed, quadratic=False, columns=5):
    result = sp.translate(source=source, language="mps", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.uses_packed_smt_stream == packed
    assert result.report.stats.num_vars == columns
    script = result.to_smt2(sp.OmtDialect.Z3)
    assert script.count("(declare-fun ") + script.count("(declare-const ") == columns
    target = z3.Optimize()
    target.from_string(script)
    x, collision = z3.Reals("x obj__objective")
    marker, binary, semi = z3.Ints("obj obj__objective1 semi")
    expected = z3.And(z3.RealVal("3/4") * x + 2*marker >= -2,
                      marker >= 0, marker <= 1, binary >= 0, binary <= 1,
                      z3.Or(semi == 0, z3.And(semi >= 2, semi <= 4)))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat
    cost = z3.RealVal("3/2")*x - 3*collision - binary + semi - marker + z3.RealVal("5/4")
    if quadratic:
        cost += z3.RealVal("1/10")*x*x - 2*x*marker
    assert len(target.objectives()) == 1
    solver = z3.Solver()
    solver.add(target.objectives()[0] != cost)
    assert solver.check() == z3.unsat
    # Integer marker default and semiinteger domain both retain their sorts.
    solver = z3.Solver()
    solver.add(*target.assertions(), semi == z3.RealVal("5/2"))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("mode", ["ordinary", "rows", "terms"])
@pytest.mark.parametrize("quadratic", [False, True])
def test_column_release_preserves_offsets_duplicates_names_sorts_and_quadratic_fallback(mode, quadratic):
    _check(_source(mode, quadratic), mode != "ordinary", quadratic)


def test_many_objective_name_collisions_keep_distinct_source_columns():
    # The generated objective must get a fresh name after all these columns,
    # and finding it must not repeatedly scan all retained declarations.
    _check(_source("terms", collisions=2048), True, columns=2051)
