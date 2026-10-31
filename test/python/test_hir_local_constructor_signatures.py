"""Local signatures remain enforced when outer constructors erase a term."""
from copy import deepcopy
import pytest
import z3
import somtparser as sp
from somtparser.hir import HirBuilder, ModelError, build_hir
from somtparser.hir_cp import CpProvider, expand_cp_model


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def raw_model(expression):
    return dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
                declarations=[dict(name="a",sort={"Array":["Int","Int"]})],
                functions=[dict(name="f",arguments=["Int"],result="Int")],
                constraints=[dict(expr=expression,span=[0,1])], objectives=[],
                objective_order="single",goal=None,assumptions=[],unresolved=[])


def invalid_term(kind):
    if kind == "application":
        return {"apply":"f","args":[lit(True,"Bool")]}
    if kind == "select":
        return {"at":"a","indices":[lit(True,"Bool")]}
    if kind == "store":
        return op("select",op("store",{"var":"a"},lit(0),lit(True,"Bool")),lit(0))
    if kind == "ite":
        return op("ite",lit(True,"Bool"),lit(1),lit(False,"Bool"))
    raise AssertionError(kind)


def erased_relation(kind, value):
    if kind == "distinct":
        return op("distinct",value)
    if kind == "all_different":
        return {"cp":"all_different","items":[value]}
    if kind == "among":
        return op("eq",{"cp":"among","items":[value],"values":[]},lit(0))
    if kind == "gcc":
        return {"cp":"global_cardinality","items":[value],"values":[],"counts":[],"closed":False}
    if kind == "regular":
        return {"cp":"regular","items":[value],"start":0,"finals":[0],"transitions":[]}
    raise AssertionError(kind)


def translate(model, route):
    before=deepcopy(model)
    try:
        if route == "provider":
            proposal=sp.propose_nl("x",language="hir",provider=CpProvider(lambda _:deepcopy(model)))
            if not proposal.valid:
                raise ModelError(str(proposal.diagnostics))
            result=sp.compile_candidate(proposal,accept_digest=proposal.digest)
        else:
            result=build_hir(expand_cp_model(model) if route=="expanded" else model,"x").translate()
        if not result.ok:
            raise ModelError(str([d.message for d in result.diagnostic_items]))
        return result
    finally:
        assert model==before


@pytest.mark.parametrize("route",["direct","expanded","provider"])
@pytest.mark.parametrize("erasure",["distinct","all_different","among","gcc","regular"])
@pytest.mark.parametrize("kind",["application","select","store","ite"])
def test_vacuous_context_cannot_hide_an_ill_sorted_local_constructor(route,erasure,kind):
    with pytest.raises((ModelError,ValueError)):
        translate(raw_model(erased_relation(erasure,invalid_term(kind))),route)


@pytest.mark.parametrize("kind",["application","select","store","ite"])
def test_signature_rejected_at_construction_without_a_model_pass_or_solver(kind):
    b=HirBuilder()
    b.declare("a",{"Array":["Int","Int"]})
    b.declare_function("f",["Int"],"Int")
    with pytest.raises(ModelError):
        b.expr(invalid_term(kind))


def test_exact_ite_is_not_confused_with_mixed_numeric_arithmetic():
    b=HirBuilder()
    with pytest.raises(ModelError):
        b.expr(op("ite",lit(True,"Bool"),lit(1),lit("1/2","Real")))
    assert repr(b.expr(op("add",lit(1),lit("1/2","Real"))).sort)=="Real"
    b.constrain(op("eq",op("add",lit(1),lit("1/2","Real")),lit("3/2","Real")))
    result=b.translate();assert result.ok
    check=z3.Solver();check.add(z3.Not(z3.And(*z3.parse_smt2_string(result.to_smt2()))))
    assert check.check()==z3.unsat


@pytest.mark.parametrize("route",["direct","expanded","provider"])
def test_valid_nested_sorts_and_lexical_array_shadowing_keep_the_full_relation(route):
    model=raw_model(op("and",
        op("eq",{"apply":"f","args":[lit(2)]},lit(3)),
        {"quantifier":"forall","binders":[{"name":"a","sort":{"Array":["Bool","Int"]}}],
         "body":op("eq",op("select",op("store",{"var":"a"},lit(True,"Bool"),lit(7)),lit(True,"Bool")),lit(7))},
        op("eq",op("ite",lit(True,"Bool"),lit(2),lit(5)),lit(2))))
    result=translate(model,route);actual=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    f=z3.Function("f",z3.IntSort(),z3.IntSort());expected=f(2)==3
    check=z3.Solver();check.add(z3.Xor(actual,expected));assert check.check()==z3.unsat
    check=z3.Solver();check.add(actual);assert check.check()==z3.sat


@pytest.mark.parametrize("erasure",["distinct","all_different","among","gcc","regular"])
def test_well_typed_vacuous_contexts_keep_their_mathematical_identity(erasure):
    result=translate(raw_model(erased_relation(erasure,{"apply":"f","args":[lit(1)]})),"direct")
    actual=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected=z3.BoolVal(erasure!="regular")
    check=z3.Solver();check.add(z3.Xor(actual,expected));assert check.check()==z3.unsat
