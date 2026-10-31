"""Independent SMT relation and objective checks for renamed HIR symbols."""
import itertools
import os
from pathlib import Path
import subprocess

import pytest

z3 = pytest.importorskip("z3")


@pytest.fixture(scope="module")
def symbol_exports(tmp_path_factory):
    root = Path(__file__).resolve().parents[2]
    build = os.environ.get("SOMTPARSER_BUILD_DIR")
    candidates = ([Path(build)] if build else []) + [root / "build-rel", root / "build"]
    binary = next((p / "test" / "test_reserved_symbol_names" for p in candidates
                   if (p / "test" / "test_reserved_symbol_names").is_file()), None)
    if binary is None:
        pytest.skip("requires the C++ reserved-symbol test built by CMake")
    output = tmp_path_factory.mktemp("hir-builtin-symbols")
    subprocess.run([str(binary), str(output)], check=True, timeout=90,
                   capture_output=True, cwd=root)
    records = [line.split("\t") for line in (output / "symbols.tsv").read_text().splitlines()]
    assert len(records) == 24
    return output, dict(records)


@pytest.mark.parametrize("index", range(24))
def test_ordinary_and_packed_exports_preserve_distinct_source_values(symbol_exports, index):
    directory, records = symbol_exports
    base = records[str(index)]
    x, y, z = (z3.Int(base + suffix) for suffix in ("!2", "!0", "!1"))
    expected = z3.And(x >= 0, x <= 1, y >= 2, y <= 3, z >= 4, z <= 5, x + y + z == 7)
    expected_objective = 100 * x + 10 * y + z
    for mode in ("ordinary", "packed"):
        optimizer = z3.Optimize()
        optimizer.from_file(str(directory / f"{index}-{mode}.smt2"))
        relation = z3.And(*optimizer.assertions())
        solver = z3.Solver()
        solver.set(timeout=5000)
        solver.add(z3.Xor(relation, expected))
        assert solver.check() == z3.unsat
        assert len(optimizer.objectives()) == 1
        solver = z3.Solver()
        solver.set(timeout=5000)
        solver.add(optimizer.objectives()[0] != expected_objective)
        assert solver.check() == z3.unsat
        # Source assignments have independently enumerated expected truth.
        # This also witnesses feasibility, so vacuous UNSAT cannot pass.
        solver = z3.Solver()
        solver.add(relation)
        for a, b, c in itertools.product(range(2), range(2, 4), range(4, 6)):
            solver.push()
            solver.add(x == a, y == b, z == c)
            assert solver.check() == (z3.sat if a + b + c == 7 else z3.unsat)
            solver.pop()


def test_free_names_and_bound_names_keep_separate_meanings(symbol_exports):
    directory, _ = symbol_exports
    x, y = z3.Ints("true!0 y")
    f = z3.Function("not!0", z3.IntSort(), z3.IntSort())
    expected = z3.And(x >= 0, x <= 1, y >= f(x), y <= 6)
    for mode in ("ordinary", "packed"):
        actual = z3.And(*z3.parse_smt2_file(str(directory / f"scope-{mode}.smt2")))
        solver = z3.Solver()
        solver.set(timeout=5000)
        solver.add(z3.Xor(actual, expected))
        assert solver.check() == z3.unsat
