"""Public HIR schema and native builder agree on constructor structure."""
import pytest
from somtparser.hir import ModelError, build_hir, hir_schema

jsonschema = pytest.importorskip("jsonschema")


def schema_validity(models):
    schema = hir_schema()
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)
    return [validator.is_valid(model) for model in models]


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def model(expressions, *, declarations=None, functions=None, data=None):
    source = "declaration and expression constructor validation"
    result = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability", "declarations": declarations or [],
        "functions": functions or [],
        "constraints": [{"expr": expr, "span": [0, len(source)]}
                        for expr in expressions],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    if data is not None:
        result["data"] = data
    return result, source


def test_rejects_observed_invalid_call_and_select_constructor_shapes():
    bad_call, source = model(
        [{"call": "f", "args": [lit(1)]}],
        functions=[{"name": "f", "arguments": ["Int"], "result": "Int"}],
    )
    assert schema_validity([bad_call]) == [False]
    try:
        build_hir(bad_call, source)
    except ModelError as exc:
        assert "unknown HIR constructor" in str(exc)
    else:
        raise AssertionError("unknown call constructor unexpectedly built")

    bad_select, source = model(
        [op("select", {"var": "a"}, lit(0), lit(1))],
        declarations=[{"name": "a", "sort": "Int", "shape": [2, 2]}],
    )
    assert schema_validity([bad_select]) == [False]
    try:
        build_hir(bad_select, source)
    except ModelError as exc:
        assert "invalid arity: select" in str(exc)
    else:
        raise AssertionError("three-argument select unexpectedly built")


def test_builds_recursive_array_application_quantifier_and_lookup_forms():
    source = "define inc(n) = n+1; check array and table"
    candidate = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "x", "sort": "Int"},
                         {"name": "a", "sort": "Int", "shape": [3]}],
        "functions": [{
            "name": "inc", "arguments": ["Int"], "result": "Int",
            "binders": [{"name": "n", "sort": "Int"}],
            "body": op("add", {"var": "n"}, lit(1)), "span": [0, 19],
        }],
        "constraints": [
            {"expr": op("eq", {"at": "a", "indices": [lit(0)]},
                        {"apply": "inc", "args": [op("add", {"var": "x"}, lit(1))]}),
             "span": [0, len(source)]},
            {"expr": {"quantifier": "forall",
                      "binders": [{"name": "i", "sort": "Int"}],
                      "body": op("implies", op("ge", {"var": "i"}, lit(0)),
                                 op("eq", {"var": "i"}, {"var": "i"}))},
             "span": [0, len(source)]},
            {"expr": op("eq", {"var": "x"},
                        {"data": "table", "indices": [lit(0)], "default": lit(-1)}),
             "span": [0, len(source)]},
        ],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [], "data": {"table": [3, 4]},
    }
    assert schema_validity([candidate]) == [True]
    build_hir(candidate, source)


def test_builds_each_public_cp_constructor_family():
    expressions = [
        op("eq", {"cp": "sum", "items": [lit(1), lit(2)]}, lit(3)),
        op("eq", {"cp": "minimum", "items": [lit(1)]}, lit(1)),
        op("eq", {"cp": "maximum", "items": [lit(1)]}, lit(1)),
        {"cp": "all_different", "items": []},
        op("eq", {"cp": "count_true", "items": []}, lit(0)),
        {"cp": "at_most_one", "items": []},
        op("eq", {"cp": "abs", "value": lit(-1)}, lit(1)),
        op("eq", {"cp": "among", "items": [], "values": [-1]}, lit(0)),
        {"cp": "global_cardinality", "items": [], "values": [],
         "counts": [], "closed": True},
        op("eq", {"cp": "element", "items": [], "index": lit(2),
                  "default": lit(-1)}, lit(-1)),
        {"cp": "table", "items": [], "tuples": [[]], "positive": True},
        {"cp": "lex", "left": [], "right": [], "strict": False},
        {"cp": "cumulative", "starts": [], "durations": [], "demands": [],
         "capacity": lit(0)},
        {"cp": "diffn", "dimensions": 2, "positions": [], "sizes": [],
         "nonstrict": False},
        {"cp": "no_overlap", "starts": [], "durations": []},
        {"cp": "circuit", "successors": [lit(0)]},
        {"cp": "regular", "items": [], "start": 0, "finals": [0],
         "transitions": []},
    ]
    candidate, source = model(expressions)
    assert schema_validity([candidate]) == [True]
    build_hir(candidate, source)


def test_builds_cp_vector_descriptor_and_datatype_expression():
    source = "typed array and datatype construction"
    candidate = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "datatypes": [{"name": "MaybeInt", "constructors": [
            {"name": "none", "fields": []},
            {"name": "some", "fields": [{"name": "value", "sort": "Int"}]},
        ]}],
        "declarations": [
            {"name": "a", "sort": "Int", "shape": [2]},
            {"name": "m", "sort": {"Datatype": "MaybeInt"}},
        ],
        "functions": [],
        "constraints": [
            {"expr": op("eq", {"cp": "sum", "items": {
                "array": "a", "length": 2}}, lit(3)), "span": [0, len(source)]},
            {"expr": op("eq", {"var": "m"},
                {"dt_constructor": "some", "sort": {"Datatype": "MaybeInt"},
                 "args": [lit(1)]}), "span": [0, len(source)]},
            {"expr": {"dt_tester": "some", "value": {"var": "m"}},
             "span": [0, len(source)]},
        ],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    build_hir(candidate, source)


def test_schema_and_public_builder_agree_on_recursive_fold_typed_literal_and_diffn():
    source = "nested folds, typed literals, and two-dimensional diffn"
    folded = {
        "fold": "sum", "var": "i", "range": [0, 2],
        "body": {
            "fold": "sum", "var": "j", "range": [0, 2],
            "body": op("add", {"var": "i"}, {"var": "j"}),
        },
    }
    expressions = [
        op("eq", folded, lit(4)),
        op("eq", lit(1, "Int"), lit(1)),
        {"cp": "diffn", "dimensions": 2,
         "positions": [[lit(0), lit(0)],
                       [{"at": "xs", "indices": [lit(0)]}, lit(3)]],
         "sizes": [[lit(2), lit(2)], [lit(2), lit(1)]],
         "nonstrict": False},
    ]
    candidate, source = model(expressions,
                              declarations=[{"name": "xs", "sort": "Int", "shape": [1]}])
    assert schema_validity([candidate]) == [True]
    build_hir(candidate, source)


def test_cumulative_symbolic_durations_do_not_inherit_no_overlap_field_schema():
    candidate, source = model([{
        "cp": "cumulative", "starts": [lit(0)],
        "durations": [{"var": "duration"}], "demands": [lit(1)],
        "capacity": lit(2),
    }], declarations=[{"name": "duration", "sort": "Int", "lower": 0}])
    assert schema_validity([candidate]) == [True]
    build_hir(candidate, source)
    candidate["constraints"][0]["expr"] = {
        "cp": "no_overlap", "starts": [lit(0)],
        "durations": [{"var": "duration"}],
    }
    assert schema_validity([candidate]) == [False]
    with pytest.raises(ModelError):
        build_hir(candidate, source)
