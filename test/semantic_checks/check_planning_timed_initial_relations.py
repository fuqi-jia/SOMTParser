"""Independent full symbolic relations for mandatory events and PDDL makespan."""
from pathlib import Path
import json
import sys
import z3

root = Path(sys.argv[1])
a0, a1, g0, g1, g2 = z3.Bools("a0 a1 g0 g1 g2")
t0, t1, last, makespan = z3.Reals("t0 t1 last makespan")
expected = {
    "mandatory": z3.And(a0, a1, t0 == 2, t1 == 5),
    "duplicate": z3.And(a0, z3.Not(a1), t0 == 2),
    "conflict": z3.BoolVal(False),
    "read_conflict": z3.BoolVal(False),
    "read_separate": z3.And(a0, t0 == 2),
    "stable": z3.And(a0, a1, t0 == 2, t1 == 5, g2,
        z3.Or(last == 0, last == 2, last == 5),
        makespan == z3.If(last == 5, 5, z3.If(last == 2, z3.If(g1, 2, 5),
                            z3.If(z3.And(g0, g1), 0, z3.If(g1, 2, 5))))),
    "empty": z3.And(g0, last == 0, makespan == 0),
}
rows = []
for name, oracle in expected.items():
    actual = z3.And(*z3.parse_smt2_file(str(root / (name + ".smt2"))))
    solver = z3.Solver(); solver.add(z3.Xor(actual, oracle)); answer = solver.check()
    row = dict(case=name, full_relation=str(answer))
    if answer != z3.unsat:
        row["counterexample"] = str(solver.model()) if answer == z3.sat else solver.reason_unknown()
    rows.append(row); assert answer == z3.unsat, row
(root / "timed-initial-full-relations.json").write_text(json.dumps(
    dict(passed=True, cases=rows, full_relation_cases=len(rows), limits=None), indent=2) + "\n")
print(json.dumps(rows))
