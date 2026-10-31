"""Finite-array all_different against an independent SMT relation."""
from _public_relation import public_relation
import pytest
import z3

from somtparser.hir import HirBuilder, ModelError, hir_api


def var(name):
    return {"var": name}


def lit(value):
    return {"literal": value, "sort": "Int"}


def op(name, *args):
    return {"op": name, "args": list(args)}


def relation(builder):
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return public_relation(result)


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("negated", [False, True])
def test_matrix_cells_and_scalar_form_one_global_relation(negated):
    builder = HirBuilder()
    builder.declare("matrix", "Int", shape=[2, 3])
    builder.declare("scalar", "Int")
    constraint = op("all_different", var("matrix"), var("scalar"))
    builder.constrain(op("not", constraint) if negated else constraint)
    matrix = z3.Array("matrix", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    expected = z3.Distinct(*[matrix[i][j] for i in range(2) for j in range(3)],
                           z3.Int("scalar"))
    equivalent(relation(builder), z3.Not(expected) if negated else expected)


def test_array_outside_the_explicit_extent_remains_unconstrained():
    builder = HirBuilder()
    builder.declare("items", "Int", shape=[2])
    builder.constrain(op("all_different", var("items")))
    items = z3.Array("items", z3.IntSort(), z3.IntSort())
    equivalent(relation(builder), items[0] != items[1])
    solver = z3.Solver()
    solver.add(relation(builder), items[99] == items[0])
    assert solver.check() == z3.sat


def test_repeating_an_array_does_not_deduplicate_its_cells():
    builder = HirBuilder()
    builder.declare("items", "Int", shape=[2])
    builder.constrain(op("all_different", var("items"), var("items")))
    equivalent(relation(builder), z3.BoolVal(False))


def test_local_scalar_shadow_does_not_use_global_array_shape():
    builder = HirBuilder()
    builder.declare("x", "Int", shape=[2])
    builder.constrain(op("eq", {"at": "x", "indices": [lit(0)]},
                         {"at": "x", "indices": [lit(1)]}))
    builder.constrain({"quantifier": "exists", "binders": [{"name": "x", "sort": "Int"}],
                       "body": op("all_different", var("x"), lit(0))})
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    equivalent(relation(builder), x[0] == x[1])


def test_local_array_shadow_and_total_arrays_have_no_inferred_extent():
    builder = HirBuilder()
    builder.declare("x", "Int", shape=[2])
    with pytest.raises(ModelError, match="scalar Int"):
        builder.expr({"quantifier": "exists", "binders": [
            {"name": "x", "sort": {"Array": ["Int", "Int"]}}],
            "body": op("all_different", var("x"))})
    builder.declare("open", {"Array": ["Int", "Int"]})
    with pytest.raises(ModelError, match="scalar Int"):
        builder.expr(op("all_different", var("open")))


def test_empty_extent_is_vacuous_without_materializing_other_dimensions():
    builder = HirBuilder()
    builder.declare("empty", "Int", shape=[0, 10**30])
    builder.constrain(op("all_different", var("empty")))
    equivalent(relation(builder), z3.BoolVal(True))


@pytest.mark.parametrize("sort", ["Bool", "Real", {"Array": ["Int", "Int"]}])
def test_empty_extent_still_checks_the_declared_element_sort(sort):
    builder = HirBuilder()
    builder.declare("items", sort, shape=[0])
    with pytest.raises(ModelError, match="exact Int"):
        builder.expr(op("all_different", var("items")))


def test_expansion_budget_counts_cells_across_all_arguments():
    builder = HirBuilder()
    builder.declare("a", "Int", shape=[6000])
    builder.declare("b", "Int", shape=[6000])
    with pytest.raises(ModelError, match="expansion exceeds 10000"):
        builder.expr(op("all_different", var("a"), var("b")))
    assert "explicit shape" in hir_api()["semantics"]["all_different"]


def test_nested_quantifiers_can_shadow_with_a_different_sort():
    builder = HirBuilder()
    builder.declare("x", "Int")
    builder.constrain(op("eq", var("x"), lit(7)))
    inner = {"quantifier": "exists", "binders": [{"name": "x", "sort": "Bool"}],
             "body": var("x")}
    builder.constrain({"quantifier": "forall", "binders": [{"name": "x", "sort": "Int"}],
                       "body": op("implies", op("eq", var("x"), lit(0)),
                                  op("and", inner, op("eq", var("x"), lit(0))))})
    equivalent(relation(builder), z3.Int("x") == 7)


def test_later_declaration_cannot_capture_an_existing_quantifier():
    builder = HirBuilder()
    builder.constrain({"quantifier": "exists", "binders": [{"name": "x", "sort": "Bool"}],
                       "body": var("x")})
    builder.declare("x", "Int")
    builder.constrain(op("eq", var("x"), lit(7)))
    equivalent(relation(builder), z3.Int("x") == 7)
