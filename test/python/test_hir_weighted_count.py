"""Explicit Bool-weight selection: relation, exact cost and partiality contracts."""
from copy import deepcopy
from fractions import Fraction
from itertools import product

import jsonschema
import pytest
import z3
import somtparser as sp
from somtparser._nl_model import ModelError
from somtparser.hir import hir_schema
from somtparser.hir_canonical import canonicalize_hir
from somtparser.hir_cp import build_cp_hir, cp_api, expand_cp_model


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def weighted(items, weights, sort="Int"):
    return {"cp": "weighted_count", "items": items, "weights": weights, "sort": sort}


def model(expr, declarations=(), *, objective=False):
    return dict(schema="somt-hir-model-v1", language="hir",
                decision="optimization" if objective else "satisfiability",
                declarations=list(declarations), functions=[],
                constraints=[] if objective else [dict(expr=expr, span=[0, 1])],
                objectives=[dict(expr=expr, sense="minimize", span=[0, 1])] if objective else [],
                objective_order="single", goal=None, assumptions=[], unresolved=[])


def target(value, expanded=False):
    if expanded:
        value = expand_cp_model(value)
    result = build_cp_hir(value, "x").translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2(sp.OmtDialect.Z3)
    parsed = z3.Optimize()
    parsed.from_string(text)
    return z3.And(*parsed.assertions()), list(parsed.objectives())


def unsat(expr):
    solver = z3.Solver()
    solver.add(expr)
    assert solver.check() == z3.unsat


def sat(expr):
    solver = z3.Solver()
    solver.add(expr)
    assert solver.check() == z3.sat


@pytest.mark.parametrize("expanded", [False, True])
@pytest.mark.parametrize("sort", ["Int", "Real"])
def test_full_relation_and_cost_exact_point_oracle(sort, expanded):
    # Repeated f0 must retain both weights; all assignments and both signs are
    # enumerated independently in Python, including zero and rational weights.
    names = ["f0", "f1", "f2"]
    flags = [var("f0"), var("f1"), var("f0"), var("f2")]
    weights = [var("w"), lit(-3 if sort == "Int" else "-3/2", sort),
               lit(2 if sort == "Int" else "2/3", sort),
               lit(0 if sort == "Int" else "0", sort)]
    decl = [dict(name=n, sort="Bool") for n in names] + [dict(name="w", sort=sort)]
    expr = weighted(flags, weights, sort)
    cost_relation, objectives = target(model(expr, decl, objective=True), expanded)
    assert len(objectives) == 1 and str(objectives[0].sort()) == sort
    cost = objectives[0]
    f0, f1, f2 = z3.Bools("f0 f1 f2")
    w = z3.Int("w") if sort == "Int" else z3.Real("w")
    q = z3.Int("q") if sort == "Int" else z3.Real("q")
    values = [-4, 0, 5] if sort == "Int" else [Fraction(-4, 3), Fraction(0), Fraction(5, 7)]
    rows = []
    for bits, weight in product(product([False, True], repeat=3), values):
        terms = [weight, -3 if sort == "Int" else Fraction(-3, 2),
                 2 if sort == "Int" else Fraction(2, 3), 0]
        expected = sum(v for enabled, v in zip([bits[0], bits[1], bits[0], bits[2]], terms)
                       if enabled)
        assign = z3.And(f0 == bits[0], f1 == bits[1], f2 == bits[2], w == str(weight))
        sat(z3.And(cost_relation, assign))
        unsat(z3.And(cost_relation, assign, cost != str(expected)))
        rows.append(z3.And(assign, q == str(expected)))
    relation, _ = target(model(op("eq", var("q"), expr),
                              decl + [dict(name="q", sort=sort)]), expanded)
    domain = z3.Or(*[w == str(v) for v in values])
    unsat(z3.And(domain, z3.Xor(relation, z3.Or(*rows))))
    # Independent mutants: dropping the repeated position, unconditional sum,
    # and changing the sign of a negative weight must all be distinguishable.
    second = z3.RealVal("-3/2") if sort == "Real" else z3.IntVal(-3)
    repeat = z3.RealVal("2/3") if sort == "Real" else z3.IntVal(2)
    for mutant in [z3.If(f0, w, 0) + z3.If(f1, second, 0),
                   w + second + repeat,
                   z3.If(f0, w + repeat, 0) + z3.If(f1, -second, 0)]:
        sat(z3.And(domain, cost_relation, cost != mutant))


@pytest.mark.parametrize("sort", ["Int", "Real"])
@pytest.mark.parametrize("expanded", [False, True])
def test_empty_and_singleton_preserve_declared_sort(sort, expanded):
    zero = lit(0 if sort == "Int" else "0", sort)
    raw = model(weighted([], [], sort), objective=True)
    assert expand_cp_model(raw)["objectives"][0]["expr"] == zero
    _, objectives = target(raw, expanded)
    assert len(objectives) == 1 and str(objectives[0].sort()) == sort
    unsat(objectives[0] != 0)
    _, objectives = target(model(weighted([lit(True, "Bool")],
                                         [lit(7 if sort == "Int" else "7/3", sort)], sort),
                                   objective=True), expanded)
    assert str(objectives[0].sort()) == sort
    unsat(objectives[0] != (7 if sort == "Int" else z3.RealVal("7/3")))


@pytest.mark.parametrize("expanded", [False, True])
def test_guarded_weights_retain_zero_denominator_branch_and_locality(expanded):
    guard = op("ne", var("d"), lit(0))
    weight = op("div_euclid", lit(10), var("d"))
    expr = weighted([guard], [weight])
    decl = [dict(name="d", sort="Int"), dict(name="q", sort="Int")]
    relation, _ = target(model(op("eq", var("q"), expr), decl), expanded)
    d, q = z3.Ints("d q")
    expected = z3.If(d != 0, 10 / d, 0)
    unsat(z3.Xor(relation, q == expected))
    sat(z3.And(relation, d == 0, q == 0))
    # One flag's fact cannot justify another weight, nor escape a binder.
    unsafe = weighted([guard, lit(True, "Bool")], [weight, weight])
    shadow = {"quantifier": "forall", "binders": [dict(name="d", sort="Int")],
              "body": op("eq", expr, weight)}
    for invalid in [op("eq", unsafe, lit(0)), op("implies", guard, shadow)]:
        with pytest.raises(ModelError, match="nonzero"):
            target(model(invalid, decl), expanded)


@pytest.mark.parametrize("expanded", [False, True])
def test_real_division_weight_uses_exact_guarded_branch(expanded):
    expr = weighted([op("ne", var("d"), lit(0))],
                    [op("div", lit(10), var("d"))], "Real")
    relation, _ = target(model(op("eq", var("q"), expr),
                              [dict(name="d", sort="Int"), dict(name="q", sort="Real")]), expanded)
    d, q = z3.Int("d"), z3.Real("q")
    unsat(z3.Xor(relation, q == z3.If(d != 0, z3.RealVal(10) / z3.ToReal(d), 0)))


@pytest.mark.parametrize("expanded", [False, True])
def test_array_descriptors_prefixes_and_quantifier_shadowing(expanded):
    expr = weighted({"array": "flags", "length": 3, "prefix": [lit(1)]},
                    {"array": "costs", "length": 3, "prefix": [lit(0)]})
    declarations = [dict(name="flags", sort="Bool", shape=[2, 3]),
                    dict(name="costs", sort="Int", shape=[2, 3]), dict(name="q", sort="Int")]
    relation, _ = target(model(op("eq", var("q"), expr), declarations), expanded)
    flags = z3.Array("flags", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    costs = z3.Array("costs", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    unsat(z3.Xor(relation, z3.Int("q") == z3.Sum([z3.If(flags[1][i], costs[0][i], 0)
                                                                for i in range(3)])))
    # Global array spellings may be shadowed by scalar quantified binders.
    inner = weighted([var("flags")], [var("costs")])
    body = op("eq", inner, op("ite", var("flags"), var("costs"), lit(0)))
    shadow = dict(quantifier="forall", binders=[dict(name="flags", sort="Bool"),
                                               dict(name="costs", sort="Int")], body=body)
    relation, _ = target(model(shadow, declarations), expanded)
    unsat(z3.Not(relation))


def test_provider_prefixes_and_explicit_aliases_have_replayable_ledger():
    expr = weighted({"array": "flags", "length": 2, "prefix": [1]},
                    {"array": "costs", "length": 2, "prefix": [0]})
    raw = model(op("eq", expr, lit(4)), [dict(name="flags", sort="Bool", shape=[2, 2]),
                                        dict(name="costs", sort="Int", shape=[2, 2])])
    original = deepcopy(raw)
    fixed, ledger = canonicalize_hir(raw)
    assert raw == original
    assert {entry["path"] for entry in ledger} == {
        "/constraints/0/expr/args/0/items/prefix/0", "/constraints/0/expr/args/0/weights/prefix/0"}
    assert canonicalize_hir(fixed) == (fixed, [])
    candidate = sp.propose_nl("x", language="hir", provider=lambda _: deepcopy(raw))
    assert candidate.valid, candidate.diagnostics
    assert candidate.normalization_ledger
    assert sp.compile_candidate(candidate, accept_digest=candidate.digest).ok
    alias = deepcopy(expr)
    alias["op"] = alias.pop("cp")
    alias["items"]["prefix"] = [lit(1)]
    alias["weights"]["prefix"] = [lit(0)]
    left, _ = target(fixed)
    right, _ = target(model(op("eq", alias, lit(4)), raw["declarations"]))
    unsat(z3.Xor(left, right))


@pytest.mark.parametrize("expanded", [False, True])
@pytest.mark.parametrize("sort,weight", [("Int", lit("1/2", "Real")),
                                         ("Real", lit(1)), ("Int", lit(True, "Bool"))])
def test_all_weights_match_sort_even_in_false_branch(sort, weight, expanded):
    with pytest.raises(ModelError):
        target(model(weighted([lit(False, "Bool")], [weight], sort), objective=True), expanded)


@pytest.mark.parametrize("expanded", [False, True])
@pytest.mark.parametrize("flag", [lit(0), lit(1), lit("0", "Real")])
def test_numeric_flags_never_coerce_to_bool(flag, expanded):
    with pytest.raises(ModelError, match="Bool"):
        target(model(weighted([flag], [lit(3)]), objective=True), expanded)


def test_native_ite_mixed_branches_and_old_bool_multiplication_remain_rejected():
    for expr in [op("ite", lit(False, "Bool"), lit(1), lit("0", "Real")),
                 op("mul", lit(True, "Bool"), lit(7))]:
        with pytest.raises(ModelError):
            target(model(expr, objective=True))


@pytest.mark.parametrize("change", ["missing-sort", "bad-sort", "missing-weights", "unknown",
                                    "length", "float-weight", "raw-int-weight", "bad-vector"])
def test_shape_field_and_exact_literal_errors(change):
    expr = weighted([lit(True, "Bool")], [lit(3)])
    if change.startswith("missing-"):
        del expr[change.removeprefix("missing-")]
    elif change == "bad-sort":
        expr["sort"] = "Bool"
    elif change == "unknown":
        expr["default"] = lit(0)
    elif change == "length":
        expr["weights"] = []
    elif change == "float-weight":
        expr["weights"] = [lit(0.5, "Real")]
        expr["sort"] = "Real"
    elif change == "raw-int-weight":
        expr["weights"] = [3]
    else:
        expr["items"] = "flags"
    with pytest.raises(ModelError):
        target(model(expr, objective=True))


@pytest.mark.parametrize("field", ["items", "weights"])
def test_descriptor_does_not_flatten_or_accept_invalid_prefix(field):
    for descriptor in [{"array": "a", "length": 1},
                       {"array": "a", "length": 4, "prefix": [lit(0)]}]:
        expr = weighted([lit(True, "Bool")], [lit(3)])
        expr[field] = descriptor
        with pytest.raises(ModelError, match="prefix|final-axis"):
            target(model(expr, [dict(name="a", sort="Bool" if field == "items" else "Int",
                                     shape=[2, 3])], objective=True))


def test_schema_and_catalog_require_complete_explicit_signature():
    api = cp_api()["constructors"]["weighted_count"]
    assert set(api) == {"cp", "items", "weights", "sort"}
    validator = jsonschema.Draft202012Validator(hir_schema())
    for tag in ["cp", "op"]:
        expr = weighted([lit(True, "Bool")], [lit(3)])
        if tag == "op":
            expr["op"] = expr.pop("cp")
        assert validator.is_valid(model(expr, objective=True))
        for field in ["items", "weights", "sort"]:
            broken = deepcopy(expr)
            del broken[field]
            assert not validator.is_valid(model(broken, objective=True))
        expr["sort"] = "Bool"
        assert not validator.is_valid(model(expr, objective=True))


def test_expansion_work_and_output_are_linear_at_public_vector_limit():
    def nodes(expr):
        stack, count = [expr], 0
        while stack:
            value = stack.pop()
            count += 1
            if isinstance(value, dict):
                stack.extend(value.values())
            elif isinstance(value, list):
                stack.extend(value)
        return count
    sizes = []
    for n in [1, 10, 100, 1000]:
        raw = model(weighted([var("flag")] * n, [var("weight")] * n), objective=True)
        expanded = expand_cp_model(raw)["objectives"][0]["expr"]
        sizes.append(nodes(expanded))
        assert len(expanded["args"]) == n
        assert all(term["op"] == "ite" for term in expanded["args"])
    assert sizes[3] - sizes[2] == 10 * (sizes[2] - sizes[1])
    assert sizes[2] - sizes[1] == 10 * (sizes[1] - sizes[0])
