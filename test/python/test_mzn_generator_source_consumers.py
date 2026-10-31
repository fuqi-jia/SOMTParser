"""MiniZinc generator-source behavior at measured Boolean consumers."""
import hashlib
import json
from pathlib import Path

import z3
import somtparser as sp


FIXTURE = Path(__file__).with_name("fixtures") / "r209-generator-consumers.json"


def test_r209_official_generator_source_consumer_matrix():
    cases = json.loads(FIXTURE.read_text(encoding="utf-8"))["cases"]
    assert len(cases) == 56
    for case in cases:
        model = case["model"]
        assert hashlib.sha256(model.encode()).hexdigest() == case["model_sha256"]
        translated = sp.translate(source=model, language="minizinc")
        assert translated.ok, (case["id"], [d.message for d in translated.diagnostic_items])
        solver = z3.Solver()
        solver.set(timeout=5000)
        assertions = z3.parse_smt2_string(translated.to_smt2())
        solver.add(*assertions)
        actual = solver.check()
        assert actual in (z3.sat, z3.unsat), (case["id"], solver.reason_unknown())
        expected = z3.sat if case["expected"] == "sat" else z3.unsat
        assert actual == expected, (case["id"], actual, expected)

        if case["expected"] == "sat":
            # Every frozen source fixes its two declared cells to 1 and 2.
            # Their -2..2 bounds are then redundant; all other SMT array
            # coordinates must remain unconstrained by these successful cases.
            a = z3.Array("a", z3.IntSort(), z3.IntSort())
            relation = z3.And(z3.Select(a, 1) == 1, z3.Select(a, 2) == 2)
            equivalence = z3.Solver()
            equivalence.set(timeout=5000)
            equivalence.add(z3.Xor(z3.And(*assertions), relation))
            assert equivalence.check() == z3.unsat, case["id"]
