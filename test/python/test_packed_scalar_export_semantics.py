"""Independent solver check of the C++ compact and expanded HIR exports."""
import os
from pathlib import Path
import subprocess

import pytest

z3 = pytest.importorskip("z3")


@pytest.fixture(scope="module")
def exports(tmp_path_factory):
    root = Path(__file__).resolve().parents[2]
    build = os.environ.get("SOMTPARSER_BUILD_DIR")
    candidates = ([Path(build)] if build else []) + [root / "build-rel", root / "build"]
    binary = next((p / "test" / "test_packed_scalar_export_contract" for p in candidates
                   if (p / "test" / "test_packed_scalar_export_contract").is_file()), None)
    if binary is None:
        pytest.skip("requires the C++ export-contract test built by CMake")
    output = tmp_path_factory.mktemp("packed-scalar-exports")
    subprocess.run([str(binary), str(output)], check=True, timeout=90, capture_output=True)
    return output


@pytest.mark.parametrize("case", range(8))
def test_compact_export_preserves_entire_relation_and_objective(exports, case):
    actual, expected = z3.Optimize(), z3.Optimize()
    actual.from_file(str(exports / f"case-{case}-packed.smt2"))
    expected.from_file(str(exports / f"case-{case}-expanded.smt2"))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*actual.assertions()), z3.And(*expected.assertions())))
    assert solver.check() == z3.unsat
    assert len(actual.objectives()) == len(expected.objectives()) == 1
    solver = z3.Solver()
    solver.add(actual.objectives()[0] != expected.objectives()[0])
    assert solver.check() == z3.unsat
    # The final coordinate is deliberately absent from calls/functions/objective.
    # It is still bounded and observable, rather than being pruned as unused.
    for outside in (-3, 6):
        solver = z3.Solver()
        solver.add(*actual.assertions(), z3.Int("pos[3][11]") == outside)
        assert solver.check() == z3.unsat
