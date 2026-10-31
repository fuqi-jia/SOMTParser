"""Interned source records must preserve variable identity and product cost."""
from itertools import product
import operator
import re

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("top", [None, 0, 4, 7, 20])
def test_compact_wbo_records_preserve_each_source_assignment(top):
    # x01 and x1 are distinct source spellings. Repeated/coefficient-one terms,
    # complements and nonlinear products must not be merged by the ID table.
    soft = [
        (3, "+1 x01 ~x1 >= 1", lambda a, b, c: a * (1 - b) >= 1),
        (4, "+01 x1 +01 x1 -1 ~x2 != 0", lambda a, b, c: 2 * b - (1 - c) != 0),
        (2, "+0 x01 ~x2 +2 ~x1 x2 = 2", lambda a, b, c: 2 * (1 - b) * c == 2),
        (1, "+1 x01 x1 x2 < 1", lambda a, b, c: a * b * c < 1),
    ]
    source = "soft: " + ("" if top is None else str(top)) + " ;\n"
    source += "+1 x01 +1 x1 +1 x2 >= 1 ;\n"
    source += "\n".join(f"[{cost}] {expr} ;" for cost, expr, _ in soft)
    result = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(sp.OmtDialect.Z3)
    for assignment in product((0, 1), repeat=3):
        expected = sum(cost for cost, _, predicate in soft if not predicate(*assignment))
        feasible = sum(assignment) >= 1 and (top is None or expected < top)
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(*(z3.Int(name) == value for name, value in zip(("x01", "x1", "x2"), assignment)))
        assert opt.check() == (z3.sat if feasible else z3.unsat)
        if feasible:
            assert opt.model().eval(opt.objectives()[0]).as_long() == expected


@pytest.mark.parametrize("direction", ["min", "max"])
def test_compact_opb_records_keep_signed_big_coefficients_and_unused_zero_vars(direction):
    weight = 10**80 + 1
    source = f"{direction}: +{weight} x01 ~x1 -{weight} ~x01 x1 +0 x2 ;\n"
    source += "+1 x01 +1 x1 <= 2 ;\n"
    result = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(sp.OmtDialect.Z3)
    assert re.search(r"\(declare-(?:fun\s+\|?x2\|?\s+\(\)|const\s+\|?x2\|?)\s+Int\s*\)", script)
    for a, b, c in product((0, 1), repeat=3):
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(z3.Int("x01") == a, z3.Int("x1") == b, z3.Int("x2") == c)
        assert opt.check() == z3.sat
        objective = opt.model().eval(opt.objectives()[0]).as_long()
        expected = weight * (a * (1 - b) - (1 - a) * b)
        assert objective == (expected if direction == "min" else -expected)
    for outside_domain in (-1, 2):
        opt = z3.Optimize()
        opt.from_string(script)
        opt.add(z3.Int("x01") == 0, z3.Int("x1") == 0,
                z3.Int("x2") == outside_domain)
        assert opt.check() == z3.unsat


@pytest.mark.parametrize("relation,predicate", [
    (">=", operator.ge), (">", operator.gt), ("<=", operator.le),
    ("<", operator.lt), ("=", operator.eq), ("!=", operator.ne),
])
def test_compact_hard_records_preserve_all_six_relations(relation, predicate):
    source = f"+2 x01 ~x1 -1 x2 {relation} 1 ;\n"
    result = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(sp.OmtDialect.Z3)
    for a, b, c in product((0, 1), repeat=3):
        expected = predicate(2 * a * (1 - b) - c, 1)
        solver = z3.Solver()
        solver.from_string(script)
        solver.add(z3.Int("x01") == a, z3.Int("x1") == b, z3.Int("x2") == c)
        assert solver.check() == (z3.sat if expected else z3.unsat), (a, b, c)
