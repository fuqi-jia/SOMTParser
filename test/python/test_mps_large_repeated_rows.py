"""Repeated entries in long matrix and objective rows retain their exact sum."""
from fractions import Fraction

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("packed", [False, True])
def test_long_rows_preserve_repeated_columns_and_exact_objective(packed):
    rows = ["NAME long_rows", "ROWS", " N objective", " L ceiling", " G floor"]
    if packed:
        rows.extend(f" E padding_{i}" for i in range(65534))
    rows.append("COLUMNS")
    names = ["x", "y", "z"]
    spellings = ["0.125", "-0.75", "2", "0.3125", "-1"]
    coefficients = {row: [Fraction(0)] * 3 for row in ("objective", "ceiling", "floor")}
    for index in range(4097):
        column = index % 3
        for offset, row in enumerate(coefficients):
            text = spellings[(index + offset) % len(spellings)]
            rows.append(f" {names[column]} {row} {text}")
            coefficients[row][column] += Fraction(text)
    rows.extend(["RHS", " rhs objective 1.25", " rhs ceiling 10", " rhs floor -5",
                 "BOUNDS", *[f" FR bounds {name}" for name in names], "ENDATA"])
    result = sp.translate(source="\n".join(rows) + "\n", language="mps")
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream == packed
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    variables = [z3.Real(name) for name in names]
    sums = {row: z3.Sum(*[z3.RealVal(str(value)) * variable
                          for value, variable in zip(values, variables)])
            for row, values in coefficients.items()}
    expected = z3.And(sums["ceiling"] <= 10, sums["floor"] >= -5)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat
    assert len(target.objectives()) == 1
    solver = z3.Solver()
    solver.add(target.objectives()[0] != sums["objective"] - z3.RealVal("1.25"))
    assert solver.check() == z3.unsat


def test_packed_batch_boundaries_keep_ranged_rows_and_skip_free_rows():
    # More than two batches of matrix rows, with free N rows interleaved at
    # the boundaries. Repeated entries make packing depend on term count.
    count = 8193
    source = ["NAME batches", "ROWS", " N objective"]
    for index in range(count):
        source.append(f" L row_{index}")
        if index in (4095, 8191):
            source.append(f" N unused_{index}")
    source.extend(["COLUMNS", " x objective 1", " x unused_4095 999", " x unused_8191 -999"])
    for index in range(count):
        variable = "y" if index == 4096 else "z" if index == 8192 else "x"
        source.extend([f" {variable} row_{index} 0.125"] * 9)
    source.extend(["RHS", *[f" rhs row_{index} 2" for index in range(count)],
                   "RANGES", " span row_4096 3", " span row_8192 5",
                   "BOUNDS", " FR bounds x", " FR bounds y", " FR bounds z", "ENDATA"])
    result = sp.translate(source="\n".join(source) + "\n", language="mps")
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    x, y, z = z3.Reals("x y z")
    coefficient = z3.RealVal("9/8")
    expected = z3.And(coefficient * x <= 2, coefficient * y <= 2,
                      coefficient * y >= -1, coefficient * z <= 2, coefficient * z >= -3)
    assert len(target.assertions()) == count
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat
    assert len(target.objectives()) == 1
    solver = z3.Solver()
    solver.add(target.objectives()[0] != x)
    assert solver.check() == z3.unsat
