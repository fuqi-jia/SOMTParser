"""Exact CP extrema and bounded construction/serialization of shared operands."""
import json
import time

import pytest
import z3

from somtparser.hir import HirBuilder, ModelError
from somtparser.hir_cp import expand_cp_expression


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def extreme(kind, *items):
    return {"cp": kind, "items": list(items)}


def formula(builder):
    result = builder.translate()
    assert result.ok, [item.message for item in result.diagnostic_items]
    text = result.to_smt2()
    return z3.And(*z3.parse_smt2_string(text)), text


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
@pytest.mark.parametrize("negative", [False, True])
def test_symbolic_extrema_equal_independent_order_characterization(kind, negative):
    builder = HirBuilder()
    for name in ("x", "y", "z", "r"):
        builder.declare(name, "Int")
    builder.declare("flag", "Bool")
    items = [var("x"), op("sub", var("y"), lit(2)),
             op("ite", var("flag"), var("z"), lit(-3)), var("x"),
             extreme("maximum", var("y"), lit(-1))]
    relation = op("eq", var("r"), extreme(kind, *items))
    builder.constrain(op("not", relation) if negative else relation)
    actual, _ = formula(builder)
    x, y, z, r = z3.Ints("x y z r")
    vals = [x, y-2, z3.If(z3.Bool("flag"), z, -3), x, z3.If(y >= -1, y, -1)]
    expected = z3.And(z3.Or(*[r == value for value in vals]),
                      *[r <= value if kind == "minimum" else r >= value for value in vals])
    if negative:
        expected = z3.Not(expected)
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_singleton_and_explicit_json_expansion_remain_exact(kind):
    builder = HirBuilder(); builder.declare("x", "Int")
    builder.constrain(op("ne", extreme(kind, var("x")), var("x")))
    actual, _ = formula(builder)
    solver = z3.Solver(); solver.add(actual)
    assert solver.check() == z3.unsat
    direct = extreme(kind, lit(-2), lit(3), lit(-2), lit(0))
    expanded = expand_cp_expression(direct)
    builder = HirBuilder(); builder.constrain(op("ne", direct, expanded))
    actual, _ = formula(builder)
    solver = z3.Solver(); solver.add(actual)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_fold_scopes_and_bound_array_prefixes_do_not_share_values(kind):
    builder = HirBuilder()
    builder.declare("grid", "Int", shape=[2, 3])
    builder.declare("out", "Int", shape=[2])
    body = op("eq", {"at": "out", "indices": [var("i")]},
              {"cp": kind, "items": {"array": "grid", "length": 3, "prefix": [var("i")]}})
    builder.constrain({"fold": "forall", "var": "i", "range": [0, 2], "body": body})
    actual, _ = formula(builder)
    grid = z3.Array("grid", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    out = z3.Array("out", z3.IntSort(), z3.IntSort())
    expected = z3.And(*[z3.And(z3.Or(*[out[i] == grid[i][j] for j in range(3)]),
                            *[out[i] <= grid[i][j] if kind == "minimum" else out[i] >= grid[i][j]
                              for j in range(3)]) for i in range(2)])
    solver = z3.Solver(); solver.set(timeout=5000); solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_nested_binders_and_shadowed_global_array_preserve_scope(kind):
    builder = HirBuilder()
    builder.declare("a", "Int", shape=[1])
    array_sort = {"Array": ["Int", "Int"]}
    bound_extreme = {"cp": kind, "items": {"array": "a", "length": 3}}
    relation = op("le" if kind == "minimum" else "ge", bound_extreme,
                  {"at": "a", "indices": [lit(1)]})
    builder.constrain({"quantifier": "forall", "binders": [{"name": "a", "sort": array_sort}],
                       "body": {"quantifier": "exists", "binders": [{"name": "i", "sort": "Int"}],
                                "body": op("and", relation,
                                           op("eq", extreme(kind, var("i"), op("add", var("i"), lit(1))),
                                              var("i") if kind == "minimum" else op("add", var("i"), lit(1))))}})
    actual, _ = formula(builder)
    solver = z3.Solver(); solver.set(timeout=5000); solver.add(z3.Not(actual))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
@pytest.mark.parametrize("item", [lit(True, "Bool"), lit("1/2", "Real")])
def test_exact_int_contract_including_singletons(kind, item):
    for items in ([item], [lit(0), item]):
        with pytest.raises(ModelError, match="exact sort Int"):
            HirBuilder().expr({"cp": kind, "items": items})


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_empty_unknown_fields_and_vector_limits_rejected(kind):
    for expression, error in [
        (extreme(kind), "empty vector"),
        ({"cp": kind, "items": [lit(1)], "extra": 1}, "unknown"),
        ({"cp": kind, "items": [lit(1)] * 1001}, "1000 elements"),
    ]:
        with pytest.raises(ModelError, match=error):
            HirBuilder().expr(expression)
    builder = HirBuilder(); builder.declare("a", "Int", shape=[2, 3])
    with pytest.raises(ModelError, match="fixed prefix"):
        builder.expr({"cp": kind, "items": {"array": "a", "length": 6}})


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_invalid_or_unguarded_partial_items_are_not_hidden(kind):
    item = {"at": "a", "indices": [var("i")]}
    expression = op("not", op("eq", extreme(kind, lit(0), item), lit(0)))
    formulas = []
    for node in (expression, expand_cp_expression(expression)):
        builder = HirBuilder(); builder.declare("a", "Int", shape=[2]); builder.declare("i", "Int")
        builder.constrain(node); formulas.append(formula(builder)[0])
    solver = z3.Solver(); solver.set(timeout=5000); solver.add(z3.Xor(*formulas))
    assert solver.check() == z3.unsat
    builder = HirBuilder(); builder.declare("d", "Int")
    with pytest.raises(ModelError, match="nonzero"):
        builder.expr(extreme(kind, lit(0), op("div_euclid", lit(2), var("d"))))
    builder = HirBuilder(); builder.declare("d", "Int")
    builder.constrain(op("implies", op("ne", var("d"), lit(0)),
                         op("eq", extreme(kind, op("div_euclid", lit(2), var("d"))),
                            op("div_euclid", lit(2), var("d")))))
    actual, _ = formula(builder)
    solver = z3.Solver(); solver.add(z3.Not(actual)); assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_construct_and_complete_smt_scale_linearly(kind):
    sizes = []
    for count in (40, 1000):
        builder = HirBuilder(); builder.declare("a", "Int", shape=[count]); builder.declare("r", "Int")
        started = time.monotonic()
        builder.constrain(op("eq", var("r"), {"cp": kind, "items": {"array": "a", "length": count}}))
        built = time.monotonic()
        result = builder.translate(); assert result.ok, [item.message for item in result.diagnostic_items]
        text = result.to_smt2(); serialized = time.monotonic()
        parsed = z3.Optimize(); parsed.from_string(text); completed = time.monotonic()
        assert builder.nodes < 8 * count + 10
        assert len(text.encode()) < 1000 * count
        assert "(let " in text
        sizes.append(len(text.encode()))
        print(json.dumps(dict(kind=kind, count=count, construction_nodes=builder.nodes,
                              smt_bytes=sizes[-1], construct_seconds=built-started,
                              translate_serialize_seconds=serialized-built, parse_seconds=completed-serialized)))
    assert sizes[1] < sizes[0] * 40


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_defined_function_compiles_extrema_in_its_parameter_scope(kind):
    builder = HirBuilder(); builder.declare("x", "Int")
    builder.declare_function("f", ["Int"], "Int")
    body = extreme(kind, var("x"), op("sub", var("x"), lit(2)))
    builder.define_function("f", [{"name": "x", "sort": "Int"}], body)
    builder.constrain(op("ne", {"apply": "f", "args": [lit(7)]}, lit(5 if kind == "minimum" else 7)))
    actual, _ = formula(builder)
    solver = z3.Solver(); solver.add(actual); assert solver.check() == z3.unsat
