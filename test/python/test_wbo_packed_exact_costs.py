"""Every source valuation determines the cost, independently of optimization."""
from itertools import product

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.fixture(scope="module")
def padding():
    return "[1] " + "+0 xpad " * 65536 + "= 0;\n"


def translated(source, require_strategy=True):
    result = sp.translate(source=source, language="opb", dialect=sp.OmtDialect.Z3)
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream
    if require_strategy:
        assert any(c.strategy == "packed-exact-weighted-violations" for c in result.report.choices)
    opt = z3.Optimize()
    opt.from_string(result.to_smt2(sp.OmtDialect.Z3))
    return opt


@pytest.mark.parametrize("relation", [">=", "<=", "="])
@pytest.mark.parametrize("finite_top", [False, True])
def test_signed_complemented_duplicate_terms_bigints_and_nonoptimal_cost(padding, relation, finite_top):
    coefficient, weight = 10**65 + 7, 10**80 + 3
    top = weight + 4 if finite_top else None
    # Unweighted padding activates the previous hard-packed implementation too,
    # so a baseline failure measures incorrect nonoptimal cost, not a new flag.
    source = "soft: " + (str(top) if top is not None else "") + ";\n" + padding.removeprefix("[1] ")
    source += f"[{weight}] -{coefficient} x1 +{coefficient+1} ~x2 +1 x1 {relation} 1;\n"
    source += "[3] +1 x2 <= 0;\n[5] +1 x1 = 1;\n+1 x1 +1 x2 >= 0;\n"
    opt = translated(source, require_strategy=False)
    objective = opt.objectives()[0]
    for x1, x2 in product((0, 1), repeat=2):
        value = -coefficient*x1 + (coefficient+1)*(1-x2) + x1
        holds = {">=": value >= 1, "<=": value <= 1, "=": value == 1}[relation]
        expected = weight*(not holds) + 3*x2 + 5*(x1 != 1)
        feasible = top is None or expected < top
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Int("x1") == x1,
                   z3.Int("x2") == x2, z3.Int("xpad") == 0)
        assert solver.check() == (z3.sat if feasible else z3.unsat)
        if feasible:
            # A plain Solver, not an Optimize result: even a nonoptimal source
            # assignment cannot inflate a satisfied row's violation indicator.
            solver.add(objective != expected)
            assert solver.check() == z3.unsat


@pytest.mark.parametrize("relation", [">=", "<=", "="])
@pytest.mark.parametrize("rhs", [-100, 100])
def test_reification_outside_attainable_bounds_is_total(padding, relation, rhs):
    opt = translated("soft: ;\n" + padding + f"[9] -3 x1 +2 ~x2 {relation} {rhs};\n")
    for x1, x2 in product((0, 1), repeat=2):
        value = -3*x1+2*(1-x2)
        holds = {">=": value >= rhs, "<=": value <= rhs, "=": value == rhs}[relation]
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Int("x1") == x1, z3.Int("x2") == x2)
        assert solver.check() == z3.sat
        solver.add(opt.objectives()[0] != (0 if holds else 9))
        assert solver.check() == z3.unsat


def test_cost_prefixes_are_unique_unbounded_ints_across_multiple_batches(padding):
    source = "soft: ;\n" + padding + "[7] +1 x1 >= 1;\n" * 513
    opt = translated(source)
    for x1 in (0, 1):
        expected = 513*7*(1-x1)
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Int("x1") == x1)
        assert solver.check() == z3.sat
        solver.add(opt.objectives()[0] != expected)
        assert solver.check() == z3.unsat


def test_source_identifiers_cannot_alias_internal_violation_or_cost_coordinates(padding):
    source = "soft: ;\n" + padding + "[7] +1 !wbo_v0 +1 !wbo_cost0 = 1;\n"
    opt = translated(source)
    for first, second in product((0, 1), repeat=2):
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Int("!wbo_v0") == first, z3.Int("!wbo_cost0") == second)
        assert solver.check() == z3.sat
        solver.add(opt.objectives()[0] != (0 if first+second == 1 else 7))
        assert solver.check() == z3.unsat
