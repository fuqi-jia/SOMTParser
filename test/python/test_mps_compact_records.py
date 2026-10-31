"""Interned RHS/range payloads survive rehashing and input-index release."""
from fractions import Fraction

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("packed", [False, True])
def test_many_distinct_rhs_values_preserve_exact_intervals_and_objective(packed):
    count = 257
    rows = 65536 if packed else count
    names = [f"long_input_row_name_{i}" for i in range(count)]
    columns = [f"column_{i}" for i in range(count)]
    rhs = [10**20 + i for i in range(count)]
    spans = [Fraction(1, 8) if i % 2 else Fraction(-1, 4) for i in range(count)]
    source = ["NAME compact_records", "OBJNAME selected_objective", "ROWS",
              " N free_row", " N selected_objective"]
    source += [f" L {name}" for name in names]
    source += [f" E padding_{i}" for i in range(rows - count)]
    source += ["COLUMNS", f" {columns[0]} selected_objective 1"]
    source += [f" {name} {row} 1" for name, row in zip(columns, names)]
    source += ["RHS", " rhs selected_objective -0.75"]
    source += [f" rhs {row} {value}" for row, value in zip(names, rhs)]
    source += ["RANGES"]
    source += [f" span {row} {'0.125' if i % 2 else '-0.25'}" for i, row in enumerate(names)]
    source += ["ENDATA"]
    result = sp.translate(source="\n".join(source) + "\n", language="mps", dialect=sp.OmtDialect.Z3)
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    assert result.uses_packed_smt_stream == packed
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    xs = [z3.Real(name) for name in columns]
    expected = z3.And(*[z3.And(x <= upper, x >= z3.RealVal(str(Fraction(upper) - abs(width))))
                          for x, upper, width in zip(xs, rhs, spans)])
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(target.objectives()[0] != xs[0] + z3.RealVal("0.75"))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("section, records, diagnostic", [
    ("RHS", [" rhs long_row_name 1", " rhs long_row_name 2"], "duplicate RHS value for row 'long_row_name'"),
    ("RANGES", [" rng long_row_name 1", " rng long_row_name 2"], "duplicate RANGES value for row 'long_row_name'"),
    ("RANGES", [" rng objective 1"], "RANGES cannot be applied to free N row 'objective'"),
])
def test_input_diagnostics_keep_original_row_names(section, records, diagnostic):
    source = "\n".join(["NAME names", "ROWS", " N objective", " L long_row_name",
                          "COLUMNS", " x long_row_name 1", section, *records, "ENDATA"]) + "\n"
    result = sp.translate(source=source, language="mps")
    assert not result.ok
    assert any(diagnostic in item.message for item in result.diagnostic_items)


def test_nonobjective_quadratic_row_is_checked_before_row_index_release():
    result = sp.translate(language="mps", source="""NAME qconstraint
ROWS
 N objective
 L nonobjective_row
COLUMNS
 x objective 1 nonobjective_row 1
QSECTION nonobjective_row
 x x 2
ENDATA
""")
    assert not result.ok
    assert any("not the objective row" in item.message for item in result.diagnostic_items)
