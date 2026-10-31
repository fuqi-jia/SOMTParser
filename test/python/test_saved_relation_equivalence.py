"""Saved obligations retain both complete relations and their shared context."""
import json
from pathlib import Path
import subprocess
import sys

import pytest

z3 = pytest.importorskip("z3")
from tools.check_relation_equivalence import read_relations


@pytest.mark.parametrize("script", [
    "(assert true)",
    "(assert (xor true false))(assert false)",
    "(declare-const cost Int)(assert (xor true false))(minimize cost)",
])
def test_saved_query_requires_one_xor_and_no_objectives(script):
    with pytest.raises(ValueError):
        read_relations(script)


def test_saved_quantifiers_and_cost_relations_share_their_input_context():
    left, right = read_relations(
        "(declare-const cost Int)"
        "(assert (xor (exists ((hidden Int)) (and (> hidden 0) (= cost hidden)))"
        "             (> cost 0)))")
    assert left.ctx == right.ctx
    assert left.ctx != z3.main_ctx()
    assert z3.is_quantifier(left)
    solver = z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_cli_records_objective_difference_with_memory_and_source_provenance(tmp_path):
    source = tmp_path / "cost.smt2"
    source.write_text(
        "(declare-const x Int)(declare-const cost Int)"
        "(assert (xor (and (>= x 0) (= cost x))"
        "             (and (>= x 0) (= cost (+ x 1)))))")
    output = tmp_path / "result.json"
    root = Path(__file__).resolve().parents[2]
    result = subprocess.run(
        [sys.executable, str(root / "tools/check_relation_equivalence.py"),
         str(source), "--output", str(output), "--timeout-ms", "2000"],
        capture_output=True, text=True, timeout=15)
    assert result.returncode == 0, result.stderr
    row = json.loads(output.read_text())
    assert row["status"] == "counterexample"
    assert row["equivalent"] is False
    assert row["memory_bytes"] <= 2 * 1024 ** 3
    assert len(row["input_sha256"]) == len(row["checker_sha256"]) == 64
