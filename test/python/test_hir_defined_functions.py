"""Exact HIR defined-function candidate semantics; qualification runs remotely."""
from copy import deepcopy

import pytest
import z3
import somtparser as sp
from somtparser.hir import ModelError, build_hir, hir_schema


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def apply(name, *args):
    return {"apply": name, "args": list(args)}


def model(source, *, declarations=(), functions=(), constraints=()):
    functions = [
        dict(function, span=function.get("span", [0, len(source)]))
        if "body" in function and "binders" in function else dict(function)
        for function in functions
    ]
    return {
        "schema": hir_schema()["properties"]["schema"]["const"],
        "language": "hir",
        "decision": "satisfiability",
        "declarations": list(declarations),
        "functions": list(functions),
        "constraints": [
            {"expr": expr, "span": [0, len(source)]} for expr in constraints
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


def actual(candidate):
    compiled = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert compiled.ok, compiled.diagnostics
    return z3.And(*z3.parse_smt2_string(compiled.to_smt2()))


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_defined_function_is_normalized_immutable_and_exact_under_reuse():
    source = "f(x) is x plus x"
    raw = model(
        source,
        declarations=[{"name": "x", "sort": "Int"}],
        functions=[{
            "name": "twice",
            "arguments": [{"sort": "Int"}],
            "result": {"sort": "Int"},
            "binders": [{"name": "x", "sort": {"sort": "Int"}}],
            "body": op("add", var("x"), var("x")),
        }],
        constraints=[
            op("eq", apply("twice", lit(3)), lit(6)),
            op("eq", apply("twice", lit(3)), lit(6)),
            op("eq", var("x"), lit(3)),
        ],
    )
    before = deepcopy(raw)
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert candidate.valid, candidate.diagnostics
    assert raw == before
    assert candidate.model["functions"][0]["binders"][0]["sort"] == "Int"
    assert candidate.model["functions"][0]["span"] == [0, len(source)]
    assert candidate.model["constraints"][0]["span"] == [0, len(source)]
    equivalent(actual(candidate), z3.Int("x") == 3)


def test_forward_defined_dependencies_are_resolved_exactly():
    source = "f calls g"
    raw = model(
        source,
        functions=[
            {"name": "f", "arguments": ["Int"], "result": "Int",
             "binders": [{"name": "a", "sort": "Int"}], "body": apply("g", var("a"))},
            {"name": "g", "arguments": ["Int"], "result": "Int",
             "binders": [{"name": "b", "sort": "Int"}],
             "body": op("add", var("b"), lit(1))},
        ],
        constraints=[op("eq", apply("f", lit(2)), lit(3))],
    )
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert candidate.valid, candidate.diagnostics
    equivalent(actual(candidate), z3.BoolVal(True))


def test_nullary_definition_and_bv_width_preserve_smt_semantics():
    source = "zero is five"
    nullary = model(
        source,
        functions=[{"name": "zero", "arguments": [], "result": "Int",
                    "binders": [], "body": lit(5)}],
        constraints=[op("eq", apply("zero"), lit(5))],
    )
    c0 = sp.propose_nl(source, language="hir", provider=lambda _request: nullary)
    assert c0.valid, c0.diagnostics
    equivalent(actual(c0), z3.BoolVal(True))

    bv4 = {"BitVec": 4}
    one = {"literal": "#b0001", "sort": bv4}
    raw = model(
        "f maps four bits",
        declarations=[{"name": "x", "sort": bv4}],
        functions=[{"name": "inc", "arguments": [bv4], "result": bv4,
                    "binders": [{"name": "v", "sort": bv4}],
                    "body": {"op": "bvadd", "args": [var("v"), one]}}],
        constraints=[op("eq", apply("inc", var("x")),
                        {"op": "bvadd", "args": [var("x"), one]}),
                     op("eq", apply("inc", {"literal": "#b0000", "sort": bv4},),
                        {"literal": "#b0001", "sort": bv4}),
                     op("eq", var("x"), {"literal": "#b0000", "sort": bv4})],
    )
    c1 = sp.propose_nl("f maps four bits", language="hir", provider=lambda _request: raw)
    assert c1.valid, c1.diagnostics
    equivalent(actual(c1), z3.BitVec("x", 4) == 0)


def test_function_binder_is_lexical_and_shadows_global_name():
    source = "the function parameter is local"
    raw = model(
        source,
        declarations=[{"name": "x", "sort": "Int"}],
        functions=[{"name": "succ", "arguments": ["Int"], "result": "Int",
                    "binders": [{"name": "x", "sort": "Int"}],
                    "body": op("add", var("x"), lit(1))}],
        constraints=[op("eq", var("x"), lit(99)),
                     op("eq", apply("succ", lit(2)), lit(3))],
    )
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert candidate.valid, candidate.diagnostics
    equivalent(actual(candidate), z3.Int("x") == 99)


def test_quantifier_inside_definition_shadows_formal_only_in_its_body():
    source = "the nested variable is local"
    raw = model(
        source,
        functions=[{"name": "is_three", "arguments": ["Int"], "result": "Bool",
                    "binders": [{"name": "x", "sort": "Int"}],
                    "body": op("and",
                               {"quantifier": "exists",
                                "binders": [{"name": "x", "sort": "Int"}],
                                "body": op("eq", var("x"), lit(7))},
                               op("eq", var("x"), lit(3)))}],
        constraints=[apply("is_three", lit(3)),
                     op("not", apply("is_three", lit(4)))],
    )
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert candidate.valid, candidate.diagnostics
    equivalent(actual(candidate), z3.BoolVal(True))


@pytest.mark.parametrize(
    "function,diagnostic",
    [
        ({"name": "f", "arguments": ["Int"], "result": "Int", "body": lit(0)}, "binders"),
        ({"name": "f", "arguments": ["Int"], "result": "Int",
          "binders": [{"name": "x", "sort": "Int"}]}, "body"),
        ({"name": "f", "arguments": ["Int"], "result": "Int",
          "binders": [], "body": lit(0)}, "binder count"),
        ({"name": "f", "arguments": ["Int", "Int"], "result": "Int",
          "binders": [{"name": "x", "sort": "Int"},
                      {"name": "x", "sort": "Int"}], "body": lit(0)}, "duplicate"),
        ({"name": "f", "arguments": ["Int"], "result": "Int",
          "binders": [{"name": "x", "sort": "Bool"}], "body": var("x")}, "sort"),
        ({"name": "f", "arguments": ["Int"], "result": "Bool",
          "binders": [{"name": "x", "sort": "Int"}], "body": var("x")}, "result"),
        ({"name": "f", "arguments": ["Int"], "result": "Int",
          "binders": [{"name": "x", "sort": "Int"}], "body": var("free")}, "functions[0].body"),
    ],
)
def test_malformed_definition_is_rejected_with_local_diagnostic(function, diagnostic):
    source = "bad definition"
    raw = model(source, functions=[function])
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert not candidate.valid
    assert any(diagnostic in message for message in candidate.diagnostics)


def test_recursive_definition_is_rejected_by_native_typecheck():
    source = "f calls itself"
    raw = model(
        source,
        functions=[{"name": "f", "arguments": ["Int"], "result": "Int",
                    "binders": [{"name": "x", "sort": "Int"}],
                    "body": apply("f", var("x"))}],
        constraints=[op("eq", apply("f", lit(0)), lit(0))],
    )
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert not candidate.valid


def test_mutually_recursive_definitions_are_rejected():
    source = "f and g call each other"
    raw = model(source, functions=[
        {"name": "f", "arguments": ["Int"], "result": "Int",
         "binders": [{"name": "x", "sort": "Int"}], "body": apply("g", var("x"))},
        {"name": "g", "arguments": ["Int"], "result": "Int",
         "binders": [{"name": "y", "sort": "Int"}], "body": apply("f", var("y"))},
    ], constraints=[op("eq", apply("f", lit(0)), lit(0))])
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert not candidate.valid


@pytest.mark.parametrize(
    "argument_sort,binder_sort",
    [
        ({"BitVec": 4}, {"BitVec": 8}),
        ({"Array": ["Int", {"BitVec": 4}]},
         {"Array": ["Int", {"BitVec": 8}]}),
    ],
)
def test_native_same_sort_rejects_width_and_array_component_mismatches(
    argument_sort, binder_sort
):
    source = "bad binder signature"
    raw = model(source, functions=[{
        "name": "f", "arguments": [argument_sort], "result": "Int",
        "binders": [{"name": "x", "sort": binder_sort}], "body": lit(0),
    }])
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert not candidate.valid
    assert any("binder sort" in message for message in candidate.diagnostics)


def test_direct_builder_failed_definition_can_be_retried():
    from somtparser.hir import HirBuilder

    builder = HirBuilder()
    builder.declare_function("identity", ["Int"], "Int")
    binder = [{"name": "x", "sort": "Int"}]
    with pytest.raises(ModelError, match="body sort"):
        builder.define_function("identity", binder, lit(True, "Bool"), path="functions[0]")
    builder.define_function("identity", binder, var("x"), path="functions[0]")
    builder.constrain(op("eq", apply("identity", lit(4)), lit(4)))
    translation = builder.translate()
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(translation.to_smt2()))
    assert solver.check() == z3.sat


@pytest.mark.parametrize(
    "argument_sort,binder_sort",
    [
        ({"BitVec": 4}, {"BitVec": 8}),
        ({"Array": ["Int", {"BitVec": 4}]},
         {"Array": ["Int", {"BitVec": 8}]}),
    ],
)
def test_direct_builder_checks_native_sort_identity(argument_sort, binder_sort):
    from somtparser.hir import HirBuilder

    builder = HirBuilder()
    builder.declare_function("f", [argument_sort], "Int")
    with pytest.raises(ModelError, match="binder sort"):
        builder.define_function(
            "f", [{"name": "x", "sort": binder_sort}], lit(0)
        )


def test_definition_span_is_required_and_checked_exactly():
    source = "defined f"
    raw = model(source, functions=[{
        "name": "f", "arguments": [], "result": "Int", "binders": [],
        "body": lit(1),
    }])
    del raw["functions"][0]["span"]
    missing = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert not missing.valid
    assert any("binders, body, and span" in message for message in missing.diagnostics)

    for span in ([0, 0], [0, len(source) + 1], [False, 2], ["0", 2], [0, 1, 2]):
        malformed = model(source, functions=[{
            "name": "f", "arguments": [], "result": "Int", "binders": [],
            "body": lit(1), "span": span,
        }])
        candidate = sp.propose_nl(source, language="hir", provider=lambda _request: malformed)
        assert not candidate.valid
        assert any("functions[0].span" in message for message in candidate.diagnostics)


def test_uninterpreted_declaration_compatibility_and_strict_unknown_fields():
    source = "p accepts x"
    legacy = model(source, declarations=[{"name": "x", "sort": "Int"}],
                   functions=[{"name": "p", "arguments": ["Int"], "result": "Bool"}],
                   constraints=[apply("p", var("x"))])
    builder = build_hir(legacy, source)
    assert builder.translate().ok
    invalid = deepcopy(legacy)
    invalid["functions"][0]["definition"] = lit(True, "Bool")
    with pytest.raises(ModelError):
        build_hir(invalid, source)


def transitive_hierarchy(depth):
    source = "Each function sums its predecessor at the next two integers."
    functions = [{"name": "f0", "arguments": ["Int"], "result": "Int",
                  "binders": [{"name": "a", "sort": "Int"}],
                  "body": op("add", var("a"), lit(1))}]
    for i in range(1, depth + 1):
        functions.append({"name": f"f{i}", "arguments": ["Int"], "result": "Int",
                          "binders": [{"name": "a", "sort": "Int"}],
                          "body": op("add",
                                     apply(f"f{i-1}", op("add", var("a"), lit(1))),
                                     apply(f"f{i-1}", op("add", var("a"), lit(2))))})
    raw = model(source, declarations=[{"name": "x", "sort": "Int"},
                                      {"name": "y", "sort": "Int"}],
                functions=functions,
                constraints=[op("eq", apply(f"f{depth}", var("x")), var("y"))])
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: raw)
    assert candidate.valid, candidate.diagnostics
    compiled = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert compiled.ok, compiled.diagnostics
    return compiled.to_smt2()


def test_deep_non_auxiliary_function_hierarchy_retains_parser_sharing():
    text = transitive_hierarchy(18)
    assert "(define-fun-rec " in text
    context = z3.Context()
    assert len(z3.parse_smt2_string(text, ctx=context)) > 0


def test_retained_transitive_hierarchy_preserves_its_exact_equation():
    text = transitive_hierarchy(9)
    context = z3.Context()
    formula = z3.And(*z3.parse_smt2_string(text, ctx=context))
    x, y = z3.Ints("x y", ctx=context)
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    # f_n(x) = 2**n*x + 2**n + 3*n*2**(n-1), by the source recurrence.
    solver.add(z3.Xor(formula, y == 512 * x + 7424))
    assert solver.check() == z3.unsat
