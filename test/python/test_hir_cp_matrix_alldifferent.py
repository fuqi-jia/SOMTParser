"""Semantic regression for a whole shaped matrix in HIR all_different."""
import z3

from somtparser.hir import HirBuilder


def test_four_by_four_all_different_covers_all_sixteen_cells():
    builder = HirBuilder()
    builder.declare("square", "Int", shape=[4, 4], lower=1, upper=16)
    builder.constrain({"op": "all_different", "args": [{"var": "square"}]})

    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2()))
    square = z3.Array("square", z3.IntSort(),
                      z3.ArraySort(z3.IntSort(), z3.IntSort()))
    cells = [square[row][col] for row in range(4) for col in range(4)]
    expected = z3.And(z3.Distinct(*cells),
                      *[z3.And(cell >= 1, cell <= 16) for cell in cells])

    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat

    # Establish a concrete satisfying assignment and reject a duplicate in the
    # final row, so neither vacuity nor checking only the first row can pass.
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(actual, *[cell == i + 1 for i, cell in enumerate(cells)])
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(actual, *[cell == i + 1 for i, cell in enumerate(cells[:-1])],
               cells[-1] == 1)
    assert solver.check() == z3.unsat
