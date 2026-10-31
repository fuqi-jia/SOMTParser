"""Reject ill-typed generated models before any target translation is attempted."""
import copy

import pytest

from somtparser import _somtparser as native
from somtparser.hir import HirBuilder, ModelError, build_hir, hir_schema


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def candidate(expr, declarations=None):
    return dict(schema="somt-hir-model-v1", language="hir",
                decision="satisfiability", declarations=declarations or [],
                functions=[], constraints=[dict(expr=expr, span=[0, 1])],
                objectives=[], objective_order="single", goal=None,
                assumptions=[], unresolved=[])


@pytest.mark.parametrize("expr,declarations,path,detail", [
    (op("eq", {"var": "groups"}, lit(0)),
     [{"name": "groups", "sort": "Int", "shape": [4]}],
     "constraints[0].expr.args[1]", "compares"),
    (op("eq", op("mul", lit(7), {"var": "selected"}), lit(0)),
     [{"name": "selected", "sort": "Bool"}],
     "constraints[0].expr.args[0].args[1]", "numeric operands"),
    (lit(3), [], "constraints[0].expr", "Bool"),
    (op("bvult", lit("#b00", {"BitVec": 2}), lit("#b000", {"BitVec": 3})),
     [], "constraints[0].expr", "width"),
])
def test_observed_and_native_only_type_errors_fail_at_build(expr, declarations, path, detail):
    model = candidate(expr, declarations)
    before = copy.deepcopy(model)
    with pytest.raises(ModelError) as error:
        build_hir(model, "x")
    assert error.value.path == path
    assert detail in error.value.message
    assert model == before


@pytest.mark.parametrize("field", ["goal", "objective"])
def test_nonboolean_goal_and_nonnumeric_objective_keep_root_paths(field):
    model = candidate(lit(True, "Bool"))
    if field == "goal":
        model.update(decision="validity", goal=dict(expr=lit(1), span=[0, 1]))
        path = "goal.expr"
    else:
        model.update(decision="optimization", objectives=[
            dict(expr=lit(True, "Bool"), span=[0, 1], sense="minimize")])
        path = "objectives[0].expr"
    with pytest.raises(ModelError) as error:
        build_hir(model, "x")
    assert error.value.path == path


def test_native_function_body_error_has_json_path():
    model = candidate(lit(True, "Bool"))
    model["functions"] = [dict(
        name="bad", arguments=[], result="Bool", binders=[], span=[0, 1],
        body=op("bvult", lit("#b00", {"BitVec": 2}), lit("#b000", {"BitVec": 3})))]
    with pytest.raises(ModelError) as error:
        build_hir(model, "x")
    assert error.value.path == "functions[0].body"


def test_synthesized_sum_helper_retains_original_fold_body_path():
    fold = {"fold": "sum", "var": "i", "range": [0, 9],
            "body": op("ite", lit(True, "Bool"), lit(1), lit(False, "Bool"))}
    model = candidate(op("eq", fold, lit(0)))
    with pytest.raises(ModelError) as error:
        build_hir(model, "x")
    assert error.value.path == "constraints[0].expr.args[0].body.args[2]"
    # The precise diagnostic points to the ill-sorted Bool branch in the
    # original JSON, rather than a synthesized helper or its enclosing fold.
    offending = model["constraints"][0]["expr"]["args"][0]["body"]["args"][2]
    assert offending == lit(False, "Bool")
    assert "branches" in error.value.message


@pytest.mark.parametrize("options", [
    dict(lower=0, upper=1, shape=[-1]), dict(lower=0, upper=True),
])
def test_rejected_declaration_does_not_consume_expression_budget(options):
    builder = HirBuilder()
    before = builder.nodes
    with pytest.raises(ModelError):
        builder.declare("x", "Int", **options)
    assert builder.nodes == before
    assert "x" not in builder.symbols
    builder.declare("x", "Int", lower=0, upper=1, shape=[2])
    assert builder.validate() == []
    assert builder.translate().ok


@pytest.mark.parametrize("sort,bound,field", [
    ("Bool", 0, "lower"), ("Bool", 1, "upper"),
    ("Int", True, "lower"), ("Int", 1.5, "upper"),
    ("Real", 1.5, "lower"), ("Real", "1/0", "upper"),
    ({"Array": ["Int", "Int"]}, 0, "lower"),
])
def test_invalid_bounds_have_paths_and_do_not_reserve_a_name(sort, bound, field):
    builder = HirBuilder()
    with pytest.raises(ModelError) as error:
        builder.declare("x", sort, **{field: bound})
    assert error.value.path == "declaration." + field
    assert "x" not in builder.symbols
    builder.declare("x", "Int", lower=0, upper=2)
    assert builder.validate() == []
    assert builder.translate().ok
    model = candidate(lit(True, "Bool"), [dict(name="x", sort=sort, **{field: bound})])
    with pytest.raises(ModelError) as error:
        build_hir(model, "x")
    assert error.value.path == "declarations[0]." + field


@pytest.mark.parametrize("declaration,valid", [
    (dict(name="b", sort="Bool", lower=0, upper=1), False),
    (dict(name="b", sort="Bool", shape=[4]), True),
    (dict(name="b", sort="Bool", lower=None), True),
    (dict(name="i", sort="Int", lower=True), False),
    (dict(name="i", sort="Int", lower=0, upper=3), True),
    (dict(name="r", sort="Real", lower=1.5), False),
    (dict(name="r", sort="Real", lower="1/2", upper="3.25"), True),
    (dict(name="r", sort="Real", lower="1/0"), False),
])
def test_public_schema_rejects_invalid_numeric_bounds(declaration, valid):
    jsonschema = pytest.importorskip("jsonschema")
    schema = hir_schema()
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)
    assert validator.is_valid(candidate(lit(True, "Bool"), [declaration])) == valid


def test_valid_unsat_bounds_and_boolean_count_build_without_translation(monkeypatch):
    def unexpected(*args, **kwargs):
        raise AssertionError("validation must not translate")
    monkeypatch.setattr(HirBuilder, "translate", unexpected)
    model = candidate(op("eq", op("count", {"var": "chosen"}), lit(1)), [
        dict(name="chosen", sort="Bool"), dict(name="x", sort="Int", lower=5, upper=2)])
    assert build_hir(model, "x").validate() == []
    # The check only establishes well-typed HIR, not feasibility or a solver's
    # support for quantified finite sets.
    sets = candidate({"quantifier": "forall", "binders": [{"name": "s", "sort": {"Set": "Int"}}],
                      "body": op("eq", {"var": "s"}, {"var": "s"})})
    assert build_hir(sets, "x").validate() == []


def test_native_validation_returns_diagnostics_without_mutation():
    model = native.HirModel()
    integer = native._hir_literal(native.HirSort.integer(), "1")
    model.constrain(integer, source_path="constraints[7].expr")
    for _ in range(2):
        diagnostics = model.validate()
        assert diagnostics
        assert diagnostics[0].severity == native.Severity.ERROR
        assert diagnostics[0].file == "constraints[7].expr"
        assert "Bool" in diagnostics[0].message
