"""Check the compact suffix and consumed preamble against an independent formula."""
import os
from pathlib import Path
import subprocess

import pytest

z3 = pytest.importorskip("z3")


@pytest.fixture(scope="module")
def exports(tmp_path_factory):
    build = os.environ.get("SOMTPARSER_BUILD_DIR")
    root = Path(__file__).resolve().parents[2]
    builds = ([Path(build)] if build else []) + [root / "build-rel", root / "build"]
    binary = next((b / "test/test_packed_scalar_preamble_lifetime" for b in builds
                   if (b / "test/test_packed_scalar_preamble_lifetime").is_file()), None)
    if binary is None:
        pytest.skip("requires the C++ scalar-preamble lifetime helper")
    output = tmp_path_factory.mktemp("scalar-preamble-lifetime")
    subprocess.run([str(binary), str(output)], check=True, capture_output=True, timeout=90)
    return output


@pytest.mark.parametrize("case", range(4))
def test_relation_and_objective_survive_preamble_release(exports, case):
    actual = z3.Optimize()
    actual.from_file(str(exports / f"case-{case}.smt2"))
    x = z3.Int("x")
    cells = [z3.Int(f"cell[{i}]") for i in range(3)]
    reference = z3.And(x >= 0, x <= 7, x >= 1, cells[0] > 0,
                       z3.Or(x == 1, x == 2),
                       *[z3.And(c >= -2, c <= 5) for c in cells],
                       x + 1 <= cells[0], cells[1] + 1 <= cells[0])
    solver = z3.Solver()
    solver.add(reference)
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.add(*actual.assertions())
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*actual.assertions()), reference))
    assert solver.check() == z3.unsat
    assert len(actual.objectives()) == 1
    objective = x + cells[2]
    if case % 2:
        objective = -objective  # Z3 represents maximization as negated minimization.
    solver = z3.Solver()
    solver.add(actual.objectives()[0] != objective)
    assert solver.check() == z3.unsat
