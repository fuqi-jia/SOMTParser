"""Public request schemas retain strict arities for every named constructor."""
import pytest

from somtparser.hir import hir_api, hir_schema

jsonschema = pytest.importorskip("jsonschema")


@pytest.fixture(scope="module")
def expression_validator():
    schema = hir_schema()
    jsonschema.Draft202012Validator.check_schema(schema)
    # Resolve all recursive references against the published document, while
    # checking a single expression instead of manufacturing a whole model.
    root = {"$defs": schema["$defs"], "$ref": "#/$defs/expression"}
    return jsonschema.Draft202012Validator(root)


def literal():
    return {"literal": 1, "sort": "Int"}


def test_named_operator_and_alias_argument_boundaries(expression_validator):
    api = hir_api()
    arities = dict(api["operations"])
    arities.update({alias: arities[canonical]
                    for alias, canonical in api["operator_aliases"].items()})
    for name, (minimum, maximum) in arities.items():
        candidate = {"op": name, "args": [literal()] * minimum}
        assert expression_validator.is_valid(candidate), name
        if minimum:
            candidate["args"] = [literal()] * (minimum - 1)
            assert not expression_validator.is_valid(candidate), name
        # All fixed-arity operators get an above-maximum witness. Large
        # variadic bounds are exercised once below, without repeating 10k
        # recursive checks for every spelling of the same variadic contract.
        if maximum <= 4:
            candidate["args"] = [literal()] * (maximum + 1)
            assert not expression_validator.is_valid(candidate), name


def test_variadic_arguments_keep_the_published_size_boundary(expression_validator):
    candidate = {"op": "and", "args": [literal()] * 10000}
    assert expression_validator.is_valid(candidate)
    candidate["args"].append(literal())
    assert not expression_validator.is_valid(candidate)


def test_indexed_constructor_argument_and_index_counts(expression_validator):
    for name, (index_count, arg_count) in hir_api()["indexed_operations"].items():
        value = {"op": name, "indices": [0] * (index_count or 0),
                 "args": [literal()] * arg_count}
        candidate = {"op_indexed": value}
        assert expression_validator.is_valid(candidate), name
        value["args"].append(literal())
        assert not expression_validator.is_valid(candidate), name
        value["args"].pop()
        if index_count is not None:
            value["indices"].append(0)
            assert not expression_validator.is_valid(candidate), name
            value["indices"].pop()
            if index_count:
                value["indices"].pop()
                assert not expression_validator.is_valid(candidate), name


@pytest.mark.parametrize("field,value", [
    ("array", 7), ("length", -1), ("length", 1001),
    ("prefix", "not an expression list"), ("unexpected", True),
])
def test_cp_vector_descriptors_keep_closed_fields_and_types(
        expression_validator, field, value):
    descriptor = {"array": "schedule", "length": 3, "prefix": [literal()]}
    candidate = {"cp": "all_different", "items": descriptor}
    assert expression_validator.is_valid(candidate)
    descriptor[field] = value
    assert not expression_validator.is_valid(candidate)
