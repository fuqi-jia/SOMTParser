"""Independent relation/objective checks for deferred numeric bounds."""
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
    binary = next((p / "test" / "test_packed_linear_streamed_bounds" for p in candidates
                   if (p / "test" / "test_packed_linear_streamed_bounds").is_file()), None)
    if binary is None:
        pytest.skip("requires the C++ streamed-bound test built by CMake")
    output = tmp_path_factory.mktemp("packed-linear-bounds")
    subprocess.run([str(binary), str(output)], check=True, timeout=90, capture_output=True)
    actual, expected = z3.Optimize(), z3.Optimize()
    actual.from_file(str(output / "packed.smt2"))
    expected.from_file(str(output / "expanded.smt2"))
    return actual, expected


def test_complete_relation_and_objective_match_ordinary_lowering(exports):
    actual, expected = exports
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*actual.assertions()), z3.And(*expected.assertions())))
    assert solver.check() == z3.unsat
    assert len(actual.objectives()) == len(expected.objectives()) == 1
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(actual.objectives()[0] != expected.objectives()[0])
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(*actual.assertions())
    assert solver.check() == z3.sat


@pytest.mark.parametrize("name,sort,value", [
    ("fractional", z3.Int, -2), ("fractional", z3.Int, 3),
    ("big", z3.Int, 900719925474099312344),
    ("big", z3.Int, 900719925474099312348),
    ("mixed", z3.Int, 0), ("mixed", z3.Int, 8),
    ("x y", z3.Real, "-1/2"), ("x y", z3.Real, "5/2"),
    ("rational_int", z3.Int, 0), ("rational_int", z3.Int, 3),
    ("unused", z3.Real, "-3.5"), ("unused", z3.Real, 7),
    ("empty", z3.Int, -9223372036854775809),
])
def test_outside_domain_assignment_stays_infeasible(exports, name, sort, value):
    actual, _ = exports
    solver = z3.Solver()
    solver.add(*actual.assertions(), sort(name) == z3.RealVal(str(value)))
    assert solver.check() == z3.unsat
