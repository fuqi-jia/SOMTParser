"""Large cumulative lowering must share exact loads without changing polarity."""
import pytest
import z3
import somtparser as sp
from somtparser import _somtparser as native
from somtparser.hir import build_hir


def model(expression, names):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=[dict(name=name, sort="Int") for name in names],
                functions=[], constraints=[dict(expr=expression, span=[0, 1])],
                objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])


@pytest.mark.parametrize("negated", [False, True])
def test_shared_load_matches_independent_integer_time_grid(negated):
    # Two groups of 64 tasks force the shared path while keeping the oracle
    # independent of the lowering's event enumeration and helper definitions.
    names = ["s0", "s1", "d0", "d1", "r0", "r1", "b"]
    context = z3.Context()
    terms = {name: z3.Int(name, ctx=context) for name in names}
    expr = {"cp": "cumulative", "starts": [{"var": f"s{i % 2}"} for i in range(128)],
            "durations": [{"var": f"d{i % 2}"} for i in range(128)],
            "demands": [{"var": f"r{i % 2}"} for i in range(128)], "capacity": {"var": "b"}}
    if negated:
        expr = {"op": "not", "args": [expr]}
    translated = build_hir(model(expr, names), "x").translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    assert "cumulative-start-events-shared-load" in translated.report.to_json()
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2(sp.OmtDialect.Z3), ctx=context))
    expected = z3.And(terms["b"] >= 0, *[terms[n] >= 0 for n in names[2:6]], *[
        64 * z3.Sum(*[z3.If(z3.And(terms[f"s{i}"] <= t,
                                  t < terms[f"s{i}"] + terms[f"d{i}"]), terms[f"r{i}"], 0)
                     for i in range(2)]) <= terms["b"] for t in range(-2, 6)])
    solver = z3.Solver(ctx=context)
    solver.set(timeout=15000)
    for name, term in terms.items():
        solver.add(term >= (-2 if name.startswith("s") else -1))
        solver.add(term <= (2 if name.startswith("s") else 256 if name == "b" else 3))
    solver.add(z3.Xor(actual, z3.Not(expected) if negated else expected))
    assert solver.check() == z3.unsat


def test_large_ground_export_does_not_expand_every_task_pair():
    names = [f"s{i}" for i in range(256)]
    expr = {"cp": "cumulative", "starts": [{"var": name} for name in names],
            "durations": [1] * 256, "demands": [1] * 256, "capacity": {"literal": 1, "sort": "Int"}}
    result = build_hir(model(expr, names), "x").translate()
    assert result.ok, [item.message for item in result.diagnostic_items]
    target = result.to_smt2(sp.OmtDialect.Z3)
    # A complete 256-task formula used to allocate 65,536 load terms; retain
    # its exact definition instead. Verify an actual conflicting assignment.
    assert len(target) < 256 * 1000
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(target, ctx=context))
    solver.add(*[z3.Int(name, ctx=context) == 0 for name in names])
    assert solver.check() == z3.unsat


def test_shared_function_name_cannot_capture_source_variable():
    name = "!cumulative_load0"
    # Native HIR allows this SMT symbol; the JSON model API deliberately
    # restricts source identifiers and cannot express the collision.
    raw = native.HirModel()
    integer = native.HirSort.integer()
    start = raw.declare(name, integer)
    one = native._hir_literal(integer, "1")
    capacity = native._hir_literal(integer, "127")
    raw.constrain(native._hir_global("cumulative", [capacity] + [start, one, one] * 128))
    result = raw.translate()
    assert result.ok, [item.message for item in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=context))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("capacity, expected", [(63, z3.unsat), (64, z3.sat)])
def test_lexically_bound_start_stays_in_its_scope(capacity, expected):
    relation = {"cp": "cumulative", "starts": [{"var": "start"}] * 64,
                "durations": [1] * 64, "demands": [1] * 64, "capacity": {"literal": capacity, "sort": "Int"}}
    expression = {"quantifier": "exists", "binders": [{"name": "start", "sort": "Int"}],
                  "body": relation}
    result = build_hir(model(expression, []), "x").translate()
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert "cumulative-start-events-shared-load" not in result.report.to_json()
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=context))
    assert solver.check() == expected


@pytest.mark.parametrize("capacity, expected", [(127, z3.unsat), (128, z3.sat)])
def test_minizinc_shared_helper_composes_with_frontend_contract(capacity, expected):
    # Direct HIR has no preceding frontend contract. Exercise the real
    # MiniZinc -> relational core -> defined helpers -> SMT composition too.
    source = (
        "array[1..128] of var 0..1: s;\n"
        "constraint forall(i in 1..128)(s[i] = 0);\n"
        "constraint cumulative(s, [1 | i in 1..128], [1 | i in 1..128], "
        f"{capacity});\nsolve satisfy;\n"
    )
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert "cumulative-start-events-shared-load" in result.report.to_json()
    assert "typed-relational-core-defined-helper-extension-v1" in result.report.to_json()
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=15000)
    solver.add(z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3), ctx=context))
    # Every unit-duration, unit-demand task starts at zero: peak load is 128.
    assert solver.check() == expected
