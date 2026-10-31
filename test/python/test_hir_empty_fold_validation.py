"""Empty folds preserve scope and typing without asserting their source bodies."""
from copy import deepcopy
import pytest
import z3
import somtparser as sp
from somtparser import _somtparser as native
from somtparser.hir import HirBuilder, ModelError, build_hir
from somtparser.hir_cp import CpProvider, expand_cp_model


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def fold(kind, body, name="i", interval=(3, 3)):
    return {"fold": kind, "var": name, "range": list(interval), "body": body}


def model(expression):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=[], functions=[], constraints=[dict(expr=expression, span=[0, 1])],
                objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])


def translated(raw, route="direct"):
    previous = deepcopy(raw)
    try:
        if route == "provider":
            proposal = sp.propose_nl("x", language="hir", provider=CpProvider(lambda _: deepcopy(raw)))
            if not proposal.valid:
                raise ModelError(str(proposal.diagnostics))
            result = sp.compile_candidate(proposal, accept_digest=proposal.digest)
        else:
            result = build_hir(expand_cp_model(raw) if route == "expanded" else raw, "x").translate()
        if not result.ok:
            raise ModelError(str([d.message for d in result.diagnostic_items]))
        return result.to_smt2()
    finally:
        assert raw == previous


def same_relation(script, expected):
    actual = z3.And(*z3.parse_smt2_string(script))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("route", ["direct", "expanded", "provider"])
@pytest.mark.parametrize("kind,body", [
    ("sum", var("missing")), ("forall", var("missing")), ("exists", var("missing")),
    ("sum", lit(True, "Bool")), ("forall", lit(1)), ("exists", lit("1/2", "Real")),
])
def test_erased_body_still_has_a_scope_and_required_type(route, kind, body):
    expression = fold(kind, body)
    if kind == "sum":
        expression = op("eq", expression, lit(0))
    with pytest.raises(ModelError):
        translated(model(expression), route)


@pytest.mark.parametrize("route", ["direct", "expanded", "provider"])
@pytest.mark.parametrize("kind,body,expected", [
    ("sum", lit(37), lit(0)),
    ("sum", lit("37/2", "Real"), lit("0", "Real")),
    ("forall", lit(False, "Bool"), lit(True, "Bool")),
    ("exists", lit(True, "Bool"), lit(False, "Bool")),
])
def test_all_four_typed_identities_keep_the_full_relation(route, kind, body, expected):
    raw = model(op("and", op("eq", fold(kind, body), expected), op("ge", var("x"), lit(-2))))
    raw["declarations"] = [dict(name="x", sort="Int")]
    same_relation(translated(raw, route), z3.Int("x") >= -2)
    builder = HirBuilder()
    assert repr(builder.expr(fold(kind, body)).sort) == expected["sort"]
    builder.validate()


@pytest.mark.parametrize("route", ["direct", "expanded", "provider"])
def test_real_empty_sum_is_usable_at_an_exact_real_function_parameter(route):
    raw = model(op("eq", {"apply": "f", "args": [fold("sum", lit("1/2", "Real"))]}, lit(7)))
    raw["functions"] = [dict(name="f", arguments=["Real"], result="Int")]
    same_relation(translated(raw, route), z3.Function("f", z3.RealSort(), z3.IntSort())(0) == 7)


@pytest.mark.parametrize("kind", ["selector", "tester", "constructor"])
def test_deep_native_datatype_error_is_retained_even_when_fold_disappears(kind):
    raw = model(lit(True, "Bool"))
    raw["datatypes"] = [{"name": "Box", "constructors": [
        {"name": "box", "fields": [{"name": "value", "sort": "Int"}]}]}]
    raw["declarations"] = [dict(name="x", sort={"Datatype": "Box"})]
    if kind == "selector":
        body = {"dt_selector": "value", "sort": "Real", "value": var("x")}
        expression = op("eq", fold("sum", body), lit("0", "Real"))
    elif kind == "tester":
        body = {"dt_tester": "box", "value": lit(1)}
        expression = fold("forall", body)
    else:
        body = {"dt_tester": "box", "value": {
            "dt_constructor": "box", "sort": {"Datatype": "Box"}, "args": [lit(True, "Bool")]}}
        expression = fold("forall", body)
    raw["constraints"][0]["expr"] = expression
    with pytest.raises(ModelError) as error:
        build_hir(raw, "x")
    assert error.value.path == "constraints[0].expr" + (".args[0]" if kind == "selector" else "") + ".body"


@pytest.mark.parametrize("body", [
    {"op_indexed": {"op": "divisible", "indices": [3], "args": [lit(True, "Bool")]}},
    op("bvult", {"op_indexed": {"op": "int2bv", "indices": [4],
                                "args": [lit("1/2", "Real")]}}, lit("#b0001", {"BitVec": 4})),
])
def test_deep_indexed_operator_type_error_survives_an_empty_boolean_fold(body):
    with pytest.raises(ModelError) as error:
        build_hir(model(fold("forall", body)), "x")
    assert error.value.path == "constraints[0].expr.body"


def test_outer_quantifier_and_fold_shadowing_close_actual_native_binders():
    raw = model({"quantifier": "forall", "binders": [dict(name="a", sort={"Array": ["Bool", "Int"]}),
                                                               dict(name="flag", sort="Bool")],
                 "body": op("eq", fold("sum", op("select", var("a"), var("flag")), name="a"), lit(0))})
    # The fold shadows a with Int; its body must not silently select the outer array.
    with pytest.raises((ModelError, ValueError)):
        translated(raw)
    raw["constraints"][0]["expr"]["body"]["args"][0]["var"] = "i"
    same_relation(translated(raw), z3.BoolVal(True))
    raw = model(op("eq", fold("sum", op("add", var("i"),
        fold("sum", var("i"), name="i")), name="i", interval=(0, 3)), lit(3)))
    same_relation(translated(raw), z3.BoolVal(True))


def test_source_only_nested_sum_has_no_helper_signature_or_target_side_effect():
    body = fold("sum", op("add", var("x"), var("j")), name="j", interval=(0, 12))
    builder = HirBuilder()
    builder.declare("x", "Int")
    builder.constrain(op("and", fold("forall", op("gt", body, lit(1000000))), op("ge", var("x"), lit(0))))
    builder.validate()
    checked = builder.translate()
    assert checked.ok
    ordinary = HirBuilder()
    ordinary.declare("x", "Int")
    ordinary.constrain(op("and", lit(True, "Bool"), op("ge", var("x"), lit(0))))
    plain = ordinary.translate()
    assert plain.ok
    assert checked.to_smt2() == plain.to_smt2()
    assert builder.functions == {} and builder._sum_template_cache == {}
    same_relation(checked.to_smt2(), z3.Int("x") >= 0)
    bad = fold("sum", {"dt_tester": "absent", "value": lit(0)}, name="j", interval=(0, 12))
    with pytest.raises(ModelError):
        HirBuilder().expr(fold("sum", bad))


def test_native_source_terms_never_assert_values_and_require_real_lexical_bindings():
    integer = native.HirSort.integer()
    boolean = native.HirSort.boolean()
    raw = native.HirModel()
    false = native._hir_literal(boolean, "false")
    term = native._hir_source_term(false, [], "source.false")
    assert raw.validate([term]) == []
    base = raw.translate()
    checked = raw.translate(source_terms=[term])
    assert checked.ok and checked.to_smt2() == base.to_smt2()
    bound = native._hir_ident("scope@bound", integer, True)
    closed = native._hir_source_term(bound, [bound, bound], "source.bound")
    assert raw.translate(source_terms=[closed]).ok
    unbound = native._hir_source_term(bound, [], "source.unbound")
    assert not raw.translate(source_terms=[closed, unbound]).ok
    wrong = native._hir_ident("scope@bound", boolean, True)
    with pytest.raises(ValueError, match="binder sort"):
        native._hir_source_term(bound, [bound, wrong], "source.conflict")
    # A free identifier is never converted to a binder merely because an env
    # contains its spelling. Model declaration checking still rejects it.
    free = native._hir_ident("unbound_global", integer, False)
    term = native._hir_source_term(free, [free], "source.free")
    assert not raw.translate(source_terms=[term]).ok


_ERASURES = ["distinct", "all_different", "all_different_except_0", "cp_all_different",
             "among", "gcc_open", "gcc_closed", "regular_no_transitions", "regular_no_finals"]


def erased(expression, kind):
    if kind in {"distinct", "all_different", "all_different_except_0"}:
        return op(kind, expression)
    if kind == "cp_all_different":
        return {"cp": "all_different", "items": [expression]}
    if kind == "among":
        return op("eq", {"cp": "among", "items": [expression], "values": []}, lit(0))
    if kind.startswith("gcc_"):
        return {"cp": "global_cardinality", "items": [expression], "values": [],
                "counts": [], "closed": kind == "gcc_closed"}
    return {"cp": "regular", "items": [expression], "start": 0,
            "finals": [] if kind == "regular_no_finals" else [0],
            "transitions": [] if kind == "regular_no_transitions" else [[0, 0, 0]]}


def model_with_box(expression):
    raw = model(expression)
    raw["datatypes"] = [{"name": "BoolBox", "constructors": [
        {"name": "boolBox", "fields": [{"name": "flag", "sort": "Bool"}]}]}]
    raw["declarations"] = [dict(name="boxValue", sort={"Datatype": "BoolBox"})]
    return raw


@pytest.mark.parametrize("route", ["direct", "expanded", "provider"])
@pytest.mark.parametrize("kind", _ERASURES)
def test_degenerate_constructor_cannot_erase_nested_native_type_errors(route, kind):
    wrong_selector = {"dt_selector": "flag", "sort": "Int", "value": var("boxValue")}
    wrong_indexed = op("ite", {"op_indexed": {"op": "divisible", "indices": [3],
                                             "args": [lit(True, "Bool")]}}, lit(1), lit(0))
    for bad_term in [wrong_selector, wrong_indexed]:
        relation = erased(bad_term, kind)
        # Test both a directly used relation and erasure inside a second,
        # empty fold: retaining only that fold's final Bool root is insufficient.
        for context in [relation, fold("forall", relation)]:
            with pytest.raises((ModelError, ValueError)):
                translated(model_with_box(context), route)


@pytest.mark.parametrize("kind", _ERASURES)
def test_legal_degenerate_constructors_remain_identities_with_bound_operands(kind):
    expected = kind not in {"gcc_closed", "regular_no_transitions", "regular_no_finals"}
    # The operand contains both a source free variable and a true lexical
    # binding. A validation-only copy must bind just the latter.
    relation = {"quantifier": "forall", "binders": [dict(name="q", sort="Int")],
                "body": erased(op("add", var("q"), var("x")), kind)}
    raw = model(op("and", op("eq", relation, lit(expected, "Bool")), op("ge", var("x"), lit(-2))))
    raw["declarations"] = [dict(name="x", sort="Int")]
    for route in ["direct", "expanded", "provider"]:
        same_relation(translated(raw, route), z3.Int("x") >= -2)



def test_retention_reuses_compiled_children_without_rebuilding_them(monkeypatch):
    original = native._hir_dt_selector
    calls = []

    def selector(*args):
        calls.append(args[0])
        return original(*args)

    monkeypatch.setattr(native, "_hir_dt_selector", selector)
    for kind in _ERASURES:
        b = HirBuilder()
        b.declare_datatype({"name": "IntBox", "constructors": [
            {"name": "intBox", "fields": [{"name": "number", "sort": "Int"}]}]})
        b.declare("boxed", {"Datatype": "IntBox"})
        before = len(calls)
        item = {"dt_selector": "number", "sort": "Int", "value": var("boxed")}
        b.constrain(fold("forall", erased(item, kind)))
        b.validate()
        assert len(calls) - before == 1, kind
