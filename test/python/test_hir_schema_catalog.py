"""Structural HIR schema validation across the public constructor catalog."""
import pytest
from somtparser import hir

jsonschema = pytest.importorskip("jsonschema")


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def model(expr, *, source="schema constructor test", declarations=None,
          functions=None, data=None, datatypes=None):
    return {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability", "declarations": declarations or [],
        "functions": functions or [],
        "constraints": [{"expr": expr, "span": [0, len(source)]}],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
        **({"data": data} if data is not None else {}),
        **({"datatypes": datatypes} if datatypes is not None else {}),
    }


def validator():
    schema = hir.hir_schema()
    jsonschema.Draft202012Validator.check_schema(schema)
    return jsonschema.Draft202012Validator(schema)


def test_observed_unknown_call_and_bad_select_arity_are_rejected_by_schema():
    check = validator()
    bad_call = model({"call": "f", "args": [lit(1)]},
                     functions=[{"name": "f", "arguments": ["Int"], "result": "Int"}])
    assert not check.is_valid(bad_call)
    bad_select = model(op("select", {"var": "a"}, lit(0), lit(1)),
                       declarations=[{"name": "a", "sort": "Int", "shape": [2, 2]}])
    assert not check.is_valid(bad_select)


def test_recursive_expression_array_function_quantifier_and_data_lookup_are_valid():
    source = "define inc(n) = n+1; check array and table"
    expr = op("eq",
        {"at": "a", "indices": [lit(0)]},
        {"apply": "inc", "args": [op("add", {"var": "x"}, lit(1))]},
    )
    declarations = [
        {"name": "x", "sort": "Int"},
        {"name": "a", "sort": "Int", "shape": [3]},
    ]
    functions = [{
        "name": "inc", "arguments": ["Int"], "result": "Int",
        "binders": [{"name": "n", "sort": "Int"}],
        "body": op("add", {"var": "n"}, lit(1)), "span": [0, 19],
    }]
    candidate = model(expr, source=source, declarations=declarations,
                      functions=functions, data={"table": [3, 4]})
    candidate["constraints"].append({
        "expr": {"quantifier": "forall", "binders": [{"name": "i", "sort": "Int"}],
                 "body": op("implies", op("ge", {"var": "i"}, lit(0)),
                            op("eq", {"var": "i"}, {"var": "i"}))},
        "span": [0, len(source)],
    })
    candidate["constraints"].append({
        "expr": op("eq", {"var": "x"},
                   {"data": "table", "indices": [lit(0)], "default": lit(-1)}),
        "span": [0, len(source)],
    })
    assert validator().is_valid(candidate)


def test_fold_marker_is_not_misclassified_as_a_variable_and_literals_are_typed():
    check = validator()
    folded = {"fold": "sum", "var": "i", "range": [0, 3],
              "body": {"var": "i"}}
    assert check.is_valid(model(op("eq", folded, lit(3))))
    assert not check.is_valid(model({"literal": 1}))
    assert check.is_valid(model({"literal": 1, "sort": "Int"}))
    assert not check.is_valid(model({"literal": 1, "sort": "RoundingMode"}))


def test_nonempty_diffn_uses_box_rows_of_coordinate_vectors():
    check = validator()
    positions = [[lit(0), lit(0)], [{"at": "xs", "indices": [lit(0)]}, lit(3)]]
    sizes = [[lit(2), lit(2)], [lit(2), lit(1)]]
    declarations = [{"name": "xs", "sort": "Int", "shape": [1]}]
    expr = {"cp": "diffn", "dimensions": 2, "positions": positions,
            "sizes": sizes, "nonstrict": False}
    assert check.is_valid(model(expr, declarations=declarations))
    # A coordinate row with an extra nesting level is not a vector.
    malformed = {"cp": "diffn", "dimensions": 2,
                 "positions": [[[lit(0), lit(0)]], [lit(3), lit(3)]],
                 "sizes": sizes, "nonstrict": False}
    assert not check.is_valid(model(malformed, declarations=declarations))


def test_every_catalog_operator_and_indexed_operator_has_a_schema_branch():
    check = validator()
    api = hir.hir_api()
    rm = {"rm": "RNE"}
    base = lit(1)
    for name, (minimum, _maximum) in api["operations"].items():
        args = [base] * minimum
        if name.startswith("fp.") and name in {"fp.add", "fp.sub", "fp.mul", "fp.div"}:
            args = [rm, base, base]
        candidate = model(op(name, *args))
        assert check.is_valid(candidate), name

    for name, (index_count, arg_count) in api["indexed_operations"].items():
        if name == "tuple.project":
            args = [{"tuple": [base]}]
        elif name in {"fp.to_sbv", "fp.to_ubv"}:
            args = [base, base]
        elif name in {"to_fp", "to_fp_unsigned"}:
            args = [base, base]
        elif name == "ieee_bv_to_fp":
            args = [base]
        else:
            args = [base] * arg_count
        indices = [0] * (index_count or 0)
        if name == "extract":
            indices = [0, 0]
        elif name in {"to_fp", "to_fp_unsigned", "ieee_bv_to_fp"}:
            indices = [8, 24]
        candidate = model({"op_indexed": {"op": name, "indices": indices, "args": args}})
        assert check.is_valid(candidate), name


def test_cp_variants_are_structurally_accepted_and_representative_cp_builds():
    check = validator()
    samples = [
        {"cp": "sum", "items": [lit(1), lit(2)]},
        {"cp": "minimum", "items": [lit(1)]},
        {"cp": "maximum", "items": [lit(1)]},
        {"cp": "all_different", "items": []},
        {"cp": "all_different_except_0", "items": []},
        {"cp": "count_true", "items": []},
        {"cp": "at_most_one", "items": []},
        {"cp": "abs", "value": lit(-1)},
        {"cp": "among", "items": [], "values": [-1, 2]},
        {"cp": "global_cardinality", "items": [], "values": [],
         "counts": [], "closed": True},
        {"cp": "element", "items": [], "index": lit(2), "default": lit(-1)},
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
    bool_cp = {"all_different", "all_different_except_0", "at_most_one", "table", "lex", "cumulative", "diffn",
               "no_overlap", "circuit", "regular"}
    for expr in samples:
        # Every catalogued CP form must have a structural schema branch.
        expression = expr if expr["cp"] in bool_cp else op("eq", expr, lit(0))
        assert check.is_valid(model(expression)), expr


def test_schema_keeps_native_symbol_checks_authoritative():
    missing_symbol = model({"var": "not_declared"})
    assert validator().is_valid(missing_symbol)
    assert "build_hir remains authoritative" in hir.hir_schema()["$comment"]
