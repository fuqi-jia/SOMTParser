"""Exact HIR semantics for all_different_except_0 over mathematical Ints."""
import itertools

import pytest
import z3

from somtparser._nl_model import ModelError
from somtparser.hir import HirBuilder
from somtparser.hir_cp import build_cp_hir


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def _relation(builder):
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(translated.to_smt2()))


def _equivalent(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def _expected_except_zero(values):
    return z3.And(*[
        z3.Implies(z3.And(left != 0, right != 0), left != right)
        for left, right in itertools.combinations(values, 2)
    ])


def test_unbounded_int_list_matches_pairwise_relation_and_negation():
    builder = HirBuilder()
    for name in ("x", "y", "z", "w"):
        builder.declare(name, "Int")
    values = [z3.Int(name) for name in ("x", "y", "z", "w")]
    expression = op("all_different_except_0", *(var(name) for name in
                                                   ("x", "y", "z", "w")))
    builder.constrain(expression)
    actual = _relation(builder)
    expected = _expected_except_zero(values)
    _equivalent(actual, expected)

    negated = HirBuilder()
    for name in ("x", "y", "z", "w"):
        negated.declare(name, "Int")
    negated.constrain(op("not", expression))
    _equivalent(_relation(negated), z3.Not(expected))

    solver = z3.Solver()
    solver.add(actual, values[0] == 0, values[1] == 0,
               values[2] == -7, values[3] == 9)
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.add(actual, values[0] == -7, values[1] == -7,
               values[2] == 0, values[3] == 0)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("arity", [0, 1, 2, 3, 6])
def test_list_cardinality_edges_and_output_growth(arity):
    builder = HirBuilder()
    names = [f"x{i}" for i in range(arity)]
    for name in names:
        builder.declare(name, "Int")
    builder.constrain(op("all_different_except_0", *(var(n) for n in names)))
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    smt = translated.to_smt2()
    if arity < 2:
        assert "(assert true)" in smt
    else:
        assert smt.count("(distinct ") == 1



def test_list_encoding_size_is_linear_in_arity():
    def serialized_size(arity):
        builder = HirBuilder()
        names = [f"x{i}" for i in range(arity)]
        for name in names:
            builder.declare(name, "Int")
        builder.constrain(op("all_different_except_0", *(var(n) for n in names)))
        translated = builder.translate()
        assert translated.ok, [d.message for d in translated.diagnostic_items]
        smt = translated.to_smt2()
        assert smt.count("(distinct ") == 1
        return len(smt)

    size8 = serialized_size(8)
    size16 = serialized_size(16)
    assert size16 > size8
    assert size16 < size8 * 2.5


def test_indexed_half_open_range_matches_exact_relation():
    builder = HirBuilder()
    builder.declare("a", {"Array": ["Int", "Int"]})
    builder.constrain(op("all_different_except_0", var("a"), lit(2), lit(5)))
    actual = _relation(builder)
    array = z3.Array("a", z3.IntSort(), z3.IntSort())
    expected = _expected_except_zero([array[i] for i in range(2, 5)])
    _equivalent(actual, expected)

    outside_only = z3.Solver()
    outside_only.add(actual, array[1] == 4, array[5] == 4,
                     array[2] == 0, array[3] == 0, array[4] == 0)
    assert outside_only.check() == z3.sat


def test_finite_shaped_array_expands_all_cells():
    builder = HirBuilder()
    builder.declare("grid", "Int", shape=[2, 2])
    builder.constrain(op("all_different_except_0", var("grid")))
    actual = _relation(builder)
    grid = z3.Array("grid", z3.IntSort(),
                    z3.ArraySort(z3.IntSort(), z3.IntSort()))
    cells = [grid[i][j] for i in range(2) for j in range(2)]
    _equivalent(actual, _expected_except_zero(cells))


def test_cp_constructor_builds_same_global_and_checks_types():
    source = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability", "declarations": [
            {"name": name, "sort": "Int"} for name in ("x", "y", "z")
        ], "functions": [], "constraints": [{"expr": {
            "cp": "all_different_except_0",
            "items": [var("x"), var("y"), var("z")],
        }, "span": [0, 1]}], "objectives": [], "objective_order": "single",
        "goal": None, "assumptions": [], "unresolved": [],
    }
    builder = build_cp_hir(source, "cp-catalog-test")
    actual = _relation(builder)
    values = [z3.Int(name) for name in ("x", "y", "z")]
    _equivalent(actual, _expected_except_zero(values))

    bad = HirBuilder()
    bad.declare("flag", "Bool")
    with pytest.raises(ModelError, match="exact Int"):
        bad.expr(op("all_different_except_0", var("flag")))
    bad_real = HirBuilder()
    bad_real.declare("real_value", "Real")
    with pytest.raises(ModelError, match="exact Int"):
        bad_real.expr(op("all_different_except_0", var("real_value")))
    bad_array = HirBuilder()
    bad_array.declare("flags", "Bool", shape=[2])
    with pytest.raises(ModelError, match="exact Int elements"):
        bad_array.expr(op("all_different_except_0", var("flags")))

    bad_bounds = HirBuilder()
    bad_bounds.declare("a", {"Array": ["Int", "Int"]})
    bad_bounds.constrain(op("all_different_except_0", var("a"),
                            {"literal": True, "sort": "Bool"}, lit(2)))
    translated = bad_bounds.translate()
    assert not translated.ok
    assert any("lower index bound must be Int" in d.message
               for d in translated.diagnostic_items)
