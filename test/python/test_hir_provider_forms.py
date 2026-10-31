"""Focused tests for the standalone, audited HIR provider-form adapter."""
from copy import deepcopy
import hashlib
import json

import pytest
import z3

from somtparser.hir import (
    INDEXED_OPERATIONS, OPERATOR_ALIASES, OPERATIONS, HirBuilder, build_hir,
)
from somtparser.hir_cp import cp_api
from somtparser.hir_provider_forms import adapt_provider_forms
from somtparser.natural_language import ModelError


def model(expr):
    return {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [],
        "functions": [],
        "constraints": [{"expr": expr, "span": [0, 12]}],
        "objectives": [],
        "assumptions": [],
        "unresolved": [],
        "goal": None,
        "objective_order": "single",
        "context": {"and": ["opaque context value"]},
    }


def relation(expr):
    builder = HirBuilder()
    builder.declare("x", "Int")
    builder.constrain(expr)
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(translated.to_smt2()))


def assert_same(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_named_and_tagged_array_access_preserve_indices_and_ledger():
    for wrapper in (
        {"array_access": {"at": "x", "indices": [{"add": [
            {"literal": 1, "sort": "Int"}, {"literal": 1, "sort": "Int"}]}]}},
        {"op": "array_access", "at": "x", "indices": [{"add": [
            {"literal": 1, "sort": "Int"}, {"literal": 1, "sort": "Int"}]}]},
    ):
        raw = model({"op": "eq", "args": [wrapper, {"literal": 7, "sort": "Int"}]})
        before = deepcopy(raw)
        adapted, ledger = adapt_provider_forms(raw)
        assert raw == before
        assert replay_ledger(raw, ledger) == adapted
        assert len(ledger) == 2
        assert adapt_provider_forms(adapted) == (adapted, [])
        builder = HirBuilder()
        builder.declare("x", {"Array": ["Int", "Int"]})
        builder.constrain(adapted["constraints"][0]["expr"])
        result = builder.translate()
        assert result.ok
        actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
        x = z3.Array("x", z3.IntSort(), z3.IntSort())
        assert_same(actual, x[2] == 7)


def test_context_goal_observable_is_distinct_from_validity_goal_and_unique():
    source = "Bonnie performs in talent shows."
    model = {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "somt_goal", "sort": "Bool"}],
        "functions": [],
        "constraints": [{
            "expr": {"op": "eq", "args": [
                {"var": "somt_goal"}, {"literal": True, "sort": "Bool"}
            ]},
            "span": [0, len(source)],
        }],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }
    assert build_hir(model, source) is not None

    duplicate = deepcopy(model)
    duplicate["declarations"].append({"name": "somt_goal", "sort": "Int"})
    with pytest.raises(ModelError, match="duplicate declaration: somt_goal"):
        build_hir(duplicate, source)

    misplaced_validity_goal = deepcopy(model)
    misplaced_validity_goal["goal"] = {
        "expr": {"literal": True, "sort": "Bool"},
        "span": [0, len(source)],
    }
    with pytest.raises(ModelError, match="decision/objective/goal mismatch"):
        build_hir(misplaced_validity_goal, source)


def test_array_access_adapter_does_not_repair_ambiguous_or_malformed_forms():
    for wrapper in (
        {"array_access": {"at": "x", "indices": []}},
        {"array_access": {"at": "x", "indices": [0], "default": 0}},
        {"array_access": {"at": "x", "indices": [0]}, "sort": "Int"},
        {"op": "other", "at": "x", "indices": [0]},
        {"op": "array_access", "at": "x", "indices": [0], "args": []},
    ):
        raw = model(wrapper)
        assert adapt_provider_forms(raw) == (raw, [])


def test_named_cp_wrapper_preserves_cardinality_relation_and_audit_ledger():
    raw = model({"cp": {
        "cp": "global_cardinality", "items": [{"var": "x"}, 0],
        "values": [0, 1], "counts": [1, 1], "closed": True,
    }})
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert raw == original
    assert ledger[0]["rule"] == "named-cp-constructor"
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])
    assert_same(relation(adapted["constraints"][0]["expr"]), z3.Int("x") == 1)


@pytest.mark.parametrize("wrapper", [
    {"cp": {"cp": "table", "items": [0], "tuples": [[0]]}},
    {"cp": {"cp": "all_different", "items": [0], "extra": True}},
    {"cp": {"cp": "invented", "items": [0]}},
    {"cp": {"cp": "all_different", "items": [0]}, "sort": "Bool"},
    {"cp": {"cp": {"cp": "all_different", "items": [0]}}},
    {"literal": {"var": "x"}, "sort": "Int"},
])
def test_cp_wrapper_adapter_does_not_fill_fields_or_infer_literal_meaning(wrapper):
    raw = model(wrapper)
    assert adapt_provider_forms(raw) == (raw, [])


def replay_ledger(raw, ledger):
    """Apply each patch in order and verify its declared preimage."""
    result = deepcopy(raw)
    for entry in ledger:
        assert set(entry) == {"path", "rule", "before", "after"}
        parts = [part.replace("~1", "/").replace("~0", "~") for part in entry["path"].split("/")[1:]]
        parent = result
        for part in parts[:-1]:
            parent = parent[int(part)] if isinstance(parent, list) else parent[part]
        key = parts[-1]
        current = parent[int(key)] if isinstance(parent, list) else parent[key]
        assert current == entry["before"], json.dumps(entry, sort_keys=True)
        if isinstance(parent, list):
            parent[int(key)] = deepcopy(entry["after"])
        else:
            parent[key] = deepcopy(entry["after"])
    return result


def test_rewrites_exact_whitelisted_forms_and_preserves_relation_and_spans():
    source_expr = {
        "and": [
            {"ge": [{"var": "x"}, {"literal": 0, "sort": "Int"}]},
            {
                "eq": [
                    {"mod_euclid": [{"var": "x"}, {"literal": 3, "sort": "Int"}]},
                    {"literal": 1, "sort": "Int"},
                ]
            },
        ]
    }
    original = model(source_expr)
    untouched = deepcopy(original)
    adapted, ledger = adapt_provider_forms(original)
    expected = {
        "op": "and",
        "args": [
            {
                "op": "ge",
                "args": [{"var": "x"}, {"literal": 0, "sort": "Int"}],
            },
            {
                "op": "eq",
                "args": [
                    {
                        "op": "mod_euclid",
                        "args": [{"var": "x"}, {"literal": 3, "sort": "Int"}],
                    },
                    {"literal": 1, "sort": "Int"},
                ],
            },
        ],
    }
    assert original == untouched
    assert adapted["constraints"][0]["expr"] == expected
    assert adapted["constraints"][0]["span"] == [0, 12]
    assert adapted["context"] == original["context"]
    assert len(ledger) == 4
    assert ledger[0]["path"] == "/constraints/0/expr"
    assert ledger[0]["after"] == {
        "op": "and",
        "args": [
            {"ge": [{"var": "x"}, {"literal": 0, "sort": "Int"}]},
            {
                "eq": [
                    {"mod_euclid": [{"var": "x"}, {"literal": 3, "sort": "Int"}]},
                    {"literal": 1, "sort": "Int"},
                ]
            },
        ],
    }
    assert replay_ledger(original, ledger) == adapted

    # The expected relation is constructed independently from the canonical
    # tagged form, so a syntax rewrite cannot silently alter the model.
    assert_same(relation(adapted["constraints"][0]["expr"]), z3.And(z3.Int("x") >= 0, z3.Int("x") % 3 == 1))
    again, second_ledger = adapt_provider_forms(adapted)
    assert again == adapted
    assert second_ledger == []


def test_bound_variables_and_source_spans_survive_nested_rewrite():
    raw = model(
        {
            "quantifier": "forall",
            "binders": [{"name": "i", "sort": "Int"}],
            "body": {
                "implies": [
                    {"ge": [{"var": "i"}, {"literal": 0, "sort": "Int"}]},
                    {"le": [{"var": "i"}, {"literal": 2, "sort": "Int"}]},
                ]
            },
        }
    )
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted["constraints"][0]["span"] == raw["constraints"][0]["span"]
    assert adapted["constraints"][0]["expr"]["binders"] == raw["constraints"][0]["expr"]["binders"]
    assert adapted["constraints"][0]["expr"]["body"] == {
        "op": "implies",
        "args": [
            {"op": "ge", "args": [{"var": "i"}, {"literal": 0, "sort": "Int"}]},
            {"op": "le", "args": [{"var": "i"}, {"literal": 2, "sort": "Int"}]},
        ],
    }
    assert len(ledger) == 3


def test_unknown_dynamic_malformed_and_unsupported_forms_are_unchanged():
    malformed = [
        {"mystery_op": [{"and": [{"var": "x"}, {"var": "x"}]}]},
        {"sub": [{"var": "x"}]},  # known name, invalid arity
        {"eq": {"left": {"var": "x"}, "right": {"var": "x"}}},
        {"op": "provider_defined", "args": [{"and": [{"var": "x"}]}]},
        {"data_lookup": {"data": "cost", "indices": []}},  # no explicit default
        {"quantifier": "forall", "binders": "malformed", "body": {"and": []}},
    ]
    for expr in malformed:
        raw = model(expr)
        adapted, ledger = adapt_provider_forms(raw)
        assert adapted == raw
        assert ledger == []


def test_operator_whitelist_tracks_documented_hir_operator_catalog():
    raw = model({"op_not_in_catalog": [{"var": "x"}]})
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted == raw and not ledger
    assert "mod_euclid" in OPERATIONS
    assert adapt_provider_forms(model({"mod_euclid": [{"var": "x"}, {"literal": 2, "sort": "Int"}]}))[1]


def test_dedicated_op_indexed_singleton_dispatches_before_operator_forms():
    raw = model(
        {
            "op_indexed": {
                "op": "extract",
                "indices": [3, 0],
                "args": [
                    {
                        "bvand": [
                            {"var": "v"},
                            {"var": "w"},
                        ]
                    }
                ],
            }
        }
    )
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted["constraints"][0]["expr"] == {
        "op_indexed": {
            "op": "extract",
            "indices": [3, 0],
            "args": [
                {"op": "bvand", "args": [{"var": "v"}, {"var": "w"}]}
            ],
        }
    }
    assert len(ledger) == 1
    assert replay_ledger(raw, ledger) == adapted


def test_finite_fold_singleton_wrapper_is_exact_bounded_and_replayable():
    cases = [
        (
            "sum",
            [0, 3],
            {"var": "x"},
            z3.Sum([z3.IntVal(i) for i in range(0, 3)]) == 3,
            {"op": "eq", "args": [
                {"fold": "sum", "var": "x", "range": [0, 3], "body": {"var": "x"}},
                {"literal": 3, "sort": "Int"},
            ]},
        ),
        (
            "forall",
            [0, 3],
            {"ge": [{"var": "x"}, {"literal": 0, "sort": "Int"}]},
            z3.And([z3.IntVal(i) >= 0 for i in range(0, 3)]),
            {"op": "forall", "args": [
                {"fold": "forall", "var": "x", "range": [0, 3],
                 "body": {"op": "ge", "args": [
                     {"var": "x"}, {"literal": 0, "sort": "Int"}
                 ]}},
            ]},
        ),
        (
            "exists",
            [0, 3],
            {"eq": [{"var": "x"}, {"literal": 2, "sort": "Int"}]},
            z3.Or([z3.IntVal(i) == 2 for i in range(0, 3)]),
            {"op": "exists", "args": [
                {"fold": "exists", "var": "x", "range": [0, 3],
                 "body": {"op": "eq", "args": [
                     {"var": "x"}, {"literal": 2, "sort": "Int"}
                 ]}},
            ]},
        ),
    ]
    for fold, bounds, body, expected, canonical in cases:
        wrapper = {"finite_fold": {
            "fold": fold, "var": "x", "range": bounds, "body": body,
        }}
        raw = model({"eq": [wrapper, {"literal": 3 if fold == "sum" else True,
                                      "sort": "Int" if fold == "sum" else "Bool"}]})
        original = deepcopy(raw)
        adapted, ledger = adapt_provider_forms(raw)
        assert raw == original
        assert adapted["constraints"][0]["expr"]["args"][0] == canonical["args"][0]
        assert ledger[0]["path"] == "/constraints/0/expr"
        assert ledger[0]["rule"] == "singleton-operator-object"
        assert ledger[1]["path"] == "/constraints/0/expr/args/0"
        assert ledger[1]["rule"] == "finite-fold-singleton-constructor"
        assert replay_ledger(raw, ledger) == adapted
        assert_same(relation(adapted["constraints"][0]["expr"]), expected)
        again, second_ledger = adapt_provider_forms(adapted)
        assert again == adapted and second_ledger == []

    # Empty half-open ranges retain the HIR identities: sum=0, forall=true,
    # and exists=false. The bound name still shadows the outer declaration.
    empty_cases = [
        ("sum", {"var": "x"}, {"literal": 0, "sort": "Int"}, z3.IntVal(0) == 0),
        ("forall", {"literal": False, "sort": "Bool"},
         {"literal": True, "sort": "Bool"}, z3.BoolVal(True)),
        ("exists", {"literal": True, "sort": "Bool"},
         {"literal": False, "sort": "Bool"}, z3.BoolVal(True)),
    ]
    for fold, body, expected_literal, expected in empty_cases:
        expr = {"eq": [
            {"finite_fold": {"fold": fold, "var": "x", "range": [5, 5], "body": body}},
            expected_literal,
        ]}
        adapted, ledger = adapt_provider_forms(model(expr))
        assert ledger[1]["path"] == "/constraints/0/expr/args/0"
        assert_same(relation(adapted["constraints"][0]["expr"]), expected)


def test_malformed_finite_fold_wrappers_are_not_repaired():
    valid_inner = {
        "fold": "sum", "var": "i", "range": [0, 2],
        "body": {"var": "i"},
    }
    malformed = [
        {"finite_fold": dict(valid_inner, extra=True)},
        {"finite_fold": {k: v for k, v in valid_inner.items() if k != "range"}},
        {"finite_fold": dict(valid_inner, fold="product")},
        {"finite_fold": dict(valid_inner, fold=[])},
        {"finite_fold": dict(valid_inner, var="")},
        {"finite_fold": dict(valid_inner, var="and")},
        {"finite_fold": dict(valid_inner, range=[False, 2])},
        {"finite_fold": dict(valid_inner, range=[0, 1.5])},
        {"finite_fold": dict(valid_inner, range=[2, 1])},
        {"finite_fold": dict(valid_inner, range=[0, 10001])},
        {"finite_fold": dict(valid_inner, body=[])},
        {"finite_fold": []},
    ]
    for expr in malformed:
        raw = model(expr)
        adapted, ledger = adapt_provider_forms(raw)
        assert adapted == raw
        assert ledger == []


def test_nl_proposal_accepts_exact_forms_and_declared_data_without_guessing():
    import somtparser as sp
    from somtparser.natural_language import Candidate
    source = "Cost is ten."
    raw = model({"eq": [
        {"data_lookup": {"data": "cost", "indices": [{"var": "x"}],
                         "default": {"literal": "0", "sort": "Int"}}},
        {"literal": "10", "sort": "Int"},
    ]})
    raw.pop("context")
    raw["data"] = {"cost": [7, 10]}
    raw["declarations"] = [{"name": "x", "sort": "Int"}]
    original = deepcopy(raw)
    candidate = sp.propose_nl(source, language="hir", provider=lambda _: raw)
    assert candidate.valid, candidate.diagnostics
    assert raw == original
    assert replay_ledger(dict(raw, context={}), candidate.normalization_ledger) == candidate.model
    loaded = Candidate.from_json(candidate.to_json())
    assert loaded.digest == candidate.digest
    from somtparser.hir import build_hir
    target = build_hir(loaded.model, source).translate()
    assert target.ok
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(target.to_smt2()))
    assert solver.check() == z3.sat
    solver.add(z3.Int("x") != 1)
    assert solver.check() == z3.unsat
    # The wrapper is unambiguous but an absent cost table remains a real error.
    raw["data"] = {}
    missing = sp.propose_nl(source, language="hir", provider=lambda _: raw)
    assert not missing.valid
    assert any("unknown data table" in text for text in missing.diagnostics)


def test_provider_prompts_preserve_source_visible_relation_and_domains():
    import somtparser as sp

    source = "Color the countries and minimize the number of colors."
    requests = {}

    class StopAfterCapture(Exception):
        pass

    def hir_provider(request):
        requests["hir"] = request
        raise StopAfterCapture

    try:
        sp.propose_nl(source, language="hir", provider=hir_provider)
    except StopAfterCapture:
        pass
    else:
        raise AssertionError("HIR provider sentinel did not propagate")

    def typed_provider(request):
        requests["typed"] = request
        raise StopAfterCapture

    try:
        sp.propose_nl(source, provider=typed_provider)
    except StopAfterCapture:
        pass
    else:
        raise AssertionError("typed provider sentinel did not propagate")
    for request in requests.values():
        instruction = request["instruction"]
        assert "full feasible relation over source-visible assignments" in instruction
        assert "Do not add symmetry-breaking or canonical-label constraints" in instruction
        assert "source or context explicitly requests canonical solutions" in instruction
        assert "logically entails the domain bound" in instruction


def test_nested_cp_expression_slots_normalize_and_replay_without_changing_data():
    from somtparser.hir import build_hir
    from somtparser.hir_canonical import canonicalize_hir
    raw = model({"cp": "global_cardinality",
                 "items": [{"add": [{"var": "x"}, {"literal": "1", "sort": "Int"}]}],
                 "values": [2],
                 "counts": [{"add": [{"literal": "0", "sort": "Int"},
                                      {"literal": "1", "sort": "Int"}]}],
                 "closed": True})
    raw["declarations"] = [{"name": "x", "sort": "Int"}]
    adapted, ledger = canonicalize_hir(raw)
    assert replay_ledger(raw, ledger) == adapted
    assert adapted["constraints"][0]["expr"]["values"] == [2]
    target = build_hir(adapted, "Cost is ten.").translate()
    assert target.ok
    relation = z3.And(*z3.parse_smt2_string(target.to_smt2()))
    assert_same(relation, z3.Int("x") == 1)
    assert canonicalize_hir(adapted) == (adapted, [])


@pytest.mark.parametrize("singleton", [False, True])
@pytest.mark.parametrize("symbol,expected", [
    ("=", lambda x: x == 3), ("!=", lambda x: x != 3),
    ("<=", lambda x: x <= 3), ("<", lambda x: x < 3),
    (">=", lambda x: x >= 3), (">", lambda x: x > 3),
    ("+", lambda x: x + 3 == 5), ("-", lambda x: x - 3 == 5),
    ("*", lambda x: x * 3 == 5),
    ("=>", lambda x: z3.Implies(x < 0, x > 3)),
])
def test_symbolic_operator_spelling_preserves_relation_and_replay(symbol, expected, singleton):
    args = [{"var": "x"}, 3]
    if symbol == "=>":
        args = [{"<": [{"var": "x"}, 0]}, {">": [{"var": "x"}, 3]}]
    expr = {symbol: args} if singleton else {"op": symbol, "args": args}
    if symbol in {"+", "-", "*"}:
        expr = {"op": "eq", "args": [expr, 5]}
    raw = model(expr)
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert raw == original
    assert any(entry["rule"] == "symbolic-operator-spelling" for entry in ledger)
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])
    assert_same(relation(adapted["constraints"][0]["expr"]), expected(z3.Int("x")))


def test_symbolic_chains_keep_every_operand_and_order():
    raw = model({"<=": [0, {"+": [{"var": "x"}, 2, 3]}, 9]})
    adapted, ledger = adapt_provider_forms(raw)
    assert replay_ledger(raw, ledger) == adapted
    x = z3.Int("x")
    assert_same(relation(adapted["constraints"][0]["expr"]), z3.And(0 <= x + 5, x + 5 <= 9))


@pytest.mark.parametrize("expr", [
    {"op": "-", "args": [1]}, {"-": [1, 2, 3]}, {"=": [1]},
    {"!=": [1, 2, 3]}, {"=>": [True]}, {"*": [1]},
    {"op": "/", "args": [1, 2]}, {"%": [1, 2]},
    {"op": "+", "args": [1, 2], "sort": "Int"}, {"+": 1},
    {"unknown": {"+": [1, 2]}}, {"literal": {"+": [1, 2]}, "sort": "Int"},
])
def test_symbolic_operator_adapter_keeps_ambiguous_or_malformed_nodes(expr):
    raw = model(expr)
    assert adapt_provider_forms(raw) == (raw, [])


def test_symbolic_operator_does_not_coerce_boolean_to_integer():
    raw = model({"<=": [True, 1]})
    adapted, ledger = adapt_provider_forms(raw)
    assert replay_ledger(raw, ledger) == adapted
    builder = HirBuilder()
    with pytest.raises((ModelError, ValueError), match="sort|numeric|arithmetic|type|Bool"):
        builder.constrain(adapted["constraints"][0]["expr"])


@pytest.mark.parametrize("operator,singleton", [
    ("all_different", False), ("all_different", True), ("allDifferent", False),
])
@pytest.mark.parametrize("items", [[], [{"var": "x"}],
    [{"var": "x"}, 1, 2], [{"var": "x"}, {"var": "x"}],
    [{"+": [{"var": "x"}, 1]}, 2],
])
def test_all_different_explicit_vector_preserves_every_position(operator, singleton, items):
    expr = {operator: [items]} if singleton else {"op": operator, "args": [items]}
    raw = model(expr)
    before = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert raw == before
    assert ledger[0]["rule"] == "all-different-explicit-vector"
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])
    x = z3.Int("x")
    terms = [z3.IntVal(item) if type(item) is int else
             x + 1 if "+" in item else x for item in items]
    expected = z3.And(*[terms[i] != terms[j] for i in range(len(terms))
                        for j in range(i + 1, len(terms))])
    assert_same(relation(adapted["constraints"][0]["expr"]), expected)


@pytest.mark.parametrize("expr", [
    {"op": "all_different", "args": [[[{"var": "x"}]]]},
    {"op": "all_different", "args": [["x", "y"]]},
    {"op": "all_different", "args": [[1.0, 2.0]]},
    {"op": "all_different", "args": [[1, 2], [3, 4]]},
    {"op": "all_different", "args": [[1, 2]], "sort": "Bool"},
    {"op": "add", "args": [[1, 2]]},
    {"literal": {"all_different": [[1, 2]]}, "sort": "Int"},
])
def test_vector_adapter_keeps_ambiguous_and_non_expression_lists(expr):
    raw = model(expr)
    assert adapt_provider_forms(raw) == (raw, [])


def _declared_function_model(expr, *, source, functions, declarations=None):
    candidate = model(expr)
    candidate["functions"] = deepcopy(functions)
    candidate["declarations"] = deepcopy(declarations or [])
    candidate["constraints"][0]["span"] = [0, len(source)]
    return candidate


def _model_relation(candidate, source):
    built = build_hir(candidate, source)
    translated = built.translate()
    assert translated.ok, [diagnostic.message for diagnostic in translated.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(translated.to_smt2()))


def test_declared_function_op_tag_preserves_argument_order_and_audit_path():
    source = "The ordered predicate holds."
    expression = {
        "op": "ordered_pair",
        "args": [{"literal": 9, "sort": "Int"}, {"var": "x"}],
    }
    raw = _declared_function_model(
        expression,
        source=source,
        functions=[{"name": "ordered_pair", "arguments": ["Int", "Int"],
                    "result": "Bool"}],
        declarations=[{"name": "x", "sort": "Int"}],
    )
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    expected_expr = {"apply": "ordered_pair", "args": deepcopy(expression["args"])}
    assert raw == original
    assert adapted["constraints"][0]["expr"] == expected_expr
    assert ledger[0] == {
        "path": "/constraints/0/expr",
        "rule": "declared-function-op-tag",
        "before": expression,
        "after": expected_expr,
    }
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])

    actual = _model_relation(adapted, source)
    ordered_pair = z3.Function(
        "ordered_pair", z3.IntSort(), z3.IntSort(), z3.BoolSort()
    )
    expected = ordered_pair(z3.IntVal(9), z3.Int("x"))
    assert_same(actual, expected)


def test_defined_function_body_nested_call_and_quantified_call_keep_relation():
    source = "For every integer, the nested functions preserve its successor."
    expression = {
        "quantifier": "forall",
        "binders": [{"name": "x", "sort": "Int"}],
        "body": {"op": "eq", "args": [
            {"op": "shifted", "args": [{"var": "x"}]},
            {"op": "add", "args": [{"var": "x"}, {"literal": 1, "sort": "Int"}]},
        ]},
    }
    functions = [
        {
            "name": "plus_one", "arguments": ["Int"], "result": "Int",
            "binders": [{"name": "n", "sort": "Int"}],
            "body": {"op": "add", "args": [
                {"var": "n"}, {"literal": 1, "sort": "Int"}
            ]},
            "span": [0, len(source)],
        },
        {
            "name": "shifted", "arguments": ["Int"], "result": "Int",
            "binders": [{"name": "m", "sort": "Int"}],
            "body": {"op": "plus_one", "args": [{"var": "m"}]},
            "span": [0, len(source)],
        },
    ]
    raw = _declared_function_model(expression, source=source, functions=functions)
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert raw == original
    assert adapted["functions"][1]["body"] == {
        "apply": "plus_one", "args": [{"var": "m"}]
    }
    assert adapted["constraints"][0]["expr"]["body"]["args"][0] == {
        "apply": "shifted", "args": [{"var": "x"}]
    }
    assert [entry["path"] for entry in ledger] == [
        "/functions/1/body", "/constraints/0/expr/body/args/0"
    ]
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])
    assert_same(_model_relation(adapted, source), z3.BoolVal(True))


def test_zero_argument_defined_function_application_is_exact():
    source = "The explicitly defined answer is seven."
    expression = {"op": "eq", "args": [
        {"op": "answer", "args": []},
        {"literal": 7, "sort": "Int"},
    ]}
    raw = _declared_function_model(
        expression,
        source=source,
        functions=[{
            "name": "answer", "arguments": [], "result": "Int",
            "binders": [], "body": {"literal": 7, "sort": "Int"},
            "span": [0, len(source)],
        }],
    )
    adapted, ledger = adapt_provider_forms(raw)
    expected = {"op": "eq", "args": [
        {"apply": "answer", "args": []},
        {"literal": 7, "sort": "Int"},
    ]}
    assert adapted["constraints"][0]["expr"] == expected
    assert ledger == [{
        "path": "/constraints/0/expr/args/0",
        "rule": "declared-function-op-tag",
        "before": {"op": "answer", "args": []},
        "after": {"apply": "answer", "args": []},
    }]
    assert_same(_model_relation(adapted, source), z3.BoolVal(True))


def test_builtin_alias_indexed_and_cp_names_never_become_function_calls():
    reserved = (
        set(OPERATIONS) | set(OPERATOR_ALIASES) | set(INDEXED_OPERATIONS)
        | set(cp_api()["constructors"])
        | {"sum", "min", "max", "minimum", "maximum", "allDifferent"}
    )
    for name in reserved:
        raw = _declared_function_model(
            {"op": name, "args": []},
            source="builtin collision",
            functions=[{"name": name, "arguments": [], "result": "Int"}],
        )
        adapted, ledger = adapt_provider_forms(raw)
        assert not any(entry["rule"] == "declared-function-op-tag" for entry in ledger), name
        assert adapted["constraints"][0]["expr"].get("apply") != name


@pytest.mark.parametrize("problem", [
    "undeclared", "wrong_arity", "duplicate_function", "constant_conflict",
    "duplicate_defined_function", "extra_expression_field", "extra_function_field",
    "datatype_selector_conflict", "malformed_function_name",
])
def test_ambiguous_or_malformed_function_forms_are_not_repaired(problem):
    source = "Do not infer ambiguous function calls."
    expr = {"op": "f", "args": [{"literal": 1, "sort": "Int"}]}
    functions = [{"name": "f", "arguments": ["Int"], "result": "Int"}]
    declarations = []
    datatypes = []
    if problem == "undeclared":
        functions = []
    elif problem == "wrong_arity":
        expr["args"] = []
    elif problem == "duplicate_function":
        functions.append(deepcopy(functions[0]))
    elif problem == "duplicate_defined_function":
        definition = {
            "name": "f", "arguments": ["Int"], "result": "Int",
            "binders": [{"name": "n", "sort": "Int"}],
            "body": {"op": "g", "args": []},
            "span": [0, len(source)],
        }
        functions = [deepcopy(definition), deepcopy(definition),
                     {"name": "g", "arguments": [], "result": "Int"}]
    elif problem == "constant_conflict":
        declarations = [{"name": "f", "sort": "Int"}]
    elif problem == "extra_expression_field":
        expr["metadata"] = "opaque"
    elif problem == "extra_function_field":
        functions[0]["metadata"] = "opaque"
    elif problem == "datatype_selector_conflict":
        datatypes = [{"name": "Record", "constructors": [{
            "name": "make_record", "fields": [{"name": "f", "sort": "Int"}]
        }]}]
    elif problem == "malformed_function_name":
        expr = {"literal": 0, "sort": "Int"}
        functions = [
            {
                "name": [], "arguments": [], "result": "Int", "binders": [],
                "body": {"op": "g", "args": []}, "span": [0, len(source)],
            },
            {"name": "g", "arguments": [], "result": "Int"},
        ]
    raw = _declared_function_model(
        expr, source=source, functions=functions, declarations=declarations
    )
    if datatypes:
        raw["datatypes"] = datatypes
    before = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert raw == before
    assert adapted == raw
    assert ledger == []


def test_nonexpression_data_and_context_are_opaque_to_function_adaptation():
    source = "Only explicit expression slots are visited."
    marker = {"op": "f", "args": [{"var": "x"}]}
    raw = _declared_function_model(
        marker, source=source,
        functions=[{"name": "f", "arguments": ["Int"], "result": "Int"}],
        declarations=[{"name": "x", "sort": "Int"}],
    )
    raw["data"] = {"opaque": deepcopy(marker)}
    raw["context"] = {"opaque": [deepcopy(marker)]}
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted["data"] == raw["data"]
    assert adapted["context"] == raw["context"]
    assert adapted["constraints"][0]["expr"] == {
        "apply": "f", "args": [{"var": "x"}]
    }
    assert ledger[0]["path"] == "/constraints/0/expr"


def test_invalid_declared_individual_identifier_is_consistently_alpha_renamed():
    raw = model({"op": "eq", "args": [
        {"var": "2sum"}, {"var": "4sum"}
    ]})
    raw["declarations"] = [
        {"name": "2sum", "sort": {"Uninterpreted": "Entity"}},
        {"name": "4sum", "sort": {"Uninterpreted": "Entity"}},
        {"name": "other", "sort": {"Uninterpreted": "Entity"}},
    ]
    raw["constraints"].append({
        "expr": {"var": "2sum"}, "span": [12, 15]
    })
    raw["constraints"].append({
        "expr": {"var": "other"}, "span": [16, 21]
    })
    original = deepcopy(raw)

    adapted, ledger = adapt_provider_forms(raw)

    encoded = adapted["declarations"][0]["name"]
    assert encoded.startswith("_somt_source_")
    assert encoded.isidentifier() and len(encoded) <= 128
    encoded_four = adapted["declarations"][1]["name"]
    assert encoded_four.startswith("_somt_source_")
    assert encoded_four.isidentifier() and len(encoded_four) <= 128
    assert encoded_four != encoded
    assert adapted["declarations"][2]["name"] == "other"
    assert adapted["constraints"][0]["expr"]["args"][0] == {"var": encoded}
    assert adapted["constraints"][0]["expr"]["args"][1] == {"var": encoded_four}
    assert adapted["constraints"][1]["expr"] == {"var": encoded}
    assert adapted["constraints"][2]["expr"] == {"var": "other"}
    assert raw == original
    assert replay_ledger(raw, ledger) == adapted
    assert {entry["path"] for entry in ledger} == {
        "/declarations/0/name",
        "/declarations/1/name",
        "/constraints/0/expr/args/0/var",
        "/constraints/0/expr/args/1/var",
        "/constraints/1/expr/var",
    }
    assert adapt_provider_forms(adapted) == (adapted, [])


def test_identifier_alpha_renaming_leaves_malformed_declaration_names_opaque():
    raw = model({"var": "2sum"})
    raw["declarations"] = [{"name": ["malformed"], "sort": "Int"}]
    before = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted == before
    assert ledger == []


def test_empty_whitespace_and_unencodable_names_are_left_untouched():
    raw = model({"var": "2sum"})
    raw["declarations"] = [
        {"name": "", "sort": {"Uninterpreted": "Entity"}},
        {"name": " \t", "sort": {"Uninterpreted": "Entity"}},
        {"name": "\ud800", "sort": {"Uninterpreted": "Entity"}},
    ]
    before = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted == before
    assert ledger == []


def test_identifier_alpha_renaming_respects_same_spelled_quantifier_binder():
    raw = model({"quantifier": "forall", "binders": [
        {"name": "2sum", "sort": {"Uninterpreted": "Entity"}}
    ], "body": {"op": "eq", "args": [
        {"var": "2sum"}, {"var": "2sum"}
    ]}})
    raw["declarations"] = [{
        "name": "2sum", "sort": {"Uninterpreted": "Entity"}
    }]
    raw["constraints"].append({"expr": {"var": "2sum"}, "span": [12, 15]})

    adapted, ledger = adapt_provider_forms(raw)

    encoded = adapted["declarations"][0]["name"]
    assert adapted["constraints"][0]["expr"]["binders"][0]["name"] == "2sum"
    assert adapted["constraints"][0]["expr"]["body"]["args"] == [
        {"var": "2sum"}, {"var": "2sum"}
    ]
    assert adapted["constraints"][1]["expr"] == {"var": encoded}
    assert ledger[-1]["path"] == "/constraints/1/expr/var"


def test_entity_individual_alpha_renaming_is_z3_equivalent_and_collision_safe():
    source = "2Sum and 4Sum are recommended; 2Sum is the conclusion."
    collision_name = "_somt_source_" + hashlib.sha256(b"2sum").hexdigest()
    raw = {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [
            {"name": "2sum", "sort": {"Uninterpreted": "Entity"}},
            {"name": "4sum", "sort": {"Uninterpreted": "Entity"}},
            {"name": collision_name, "sort": {"Uninterpreted": "Entity"}},
            {"name": "猫", "sort": {"Uninterpreted": "Entity"}},
            {"name": "somt_goal", "sort": "Bool"},
        ],
        "functions": [{
            "name": "recommended", "arguments": [{"Uninterpreted": "Entity"}],
            "result": "Bool",
        }],
        "constraints": [
            {"expr": {"apply": "recommended", "args": [{"var": "2sum"}]},
             "span": [0, len(source)]},
            {"expr": {"apply": "recommended", "args": [{"var": "4sum"}]},
             "span": [0, len(source)]},
            {"expr": {"op": "eq", "args": [
                {"var": "somt_goal"},
                {"apply": "recommended", "args": [{"var": "2sum"}]},
            ]}, "span": [0, len(source)]},
        ],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    encoded_two = adapted["declarations"][0]["name"]
    encoded_four = adapted["declarations"][1]["name"]
    assert encoded_two == collision_name + "_1"
    assert adapted["declarations"][3]["name"] == "猫"
    assert raw == original
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])

    translated = build_hir(adapted, source).translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2()))

    def find_constant(expression, name):
        if z3.is_const(expression) and str(expression.decl().name()) == name:
            return expression
        for child in expression.children():
            found = find_constant(child, name)
            if found is not None:
                return found
        return None

    entity_sort = find_constant(actual, encoded_two).sort()
    two_sum = z3.Const("2sum", entity_sort)
    four_sum = z3.Const("4sum", entity_sort)
    goal = find_constant(actual, "somt_goal")
    recommended = z3.Function("recommended", entity_sort, z3.BoolSort())
    relabeled = z3.substitute(
        actual,
        (find_constant(actual, encoded_two), two_sum),
        (find_constant(actual, encoded_four), four_sum),
    )
    expected = z3.And(
        recommended(two_sum), recommended(four_sum),
        goal == recommended(two_sum),
    )
    solver = z3.Solver()
    solver.add(z3.Xor(relabeled, expected))
    assert solver.check() == z3.unsat


def test_invalid_identifier_mapping_handles_long_names_and_only_exact_declarations():
    long_name = "a" * 129
    raw = model({"op": "eq", "args": [
        {"var": long_name}, {"var": "2sum"}
    ]})
    raw["declarations"] = [
        {"name": long_name, "sort": {"Uninterpreted": "Entity"}},
        {"name": "2sum", "sort": {"Uninterpreted": "Entity"}, "extra": True},
        {"name": "missing-sort"},
        {"sort": {"Uninterpreted": "Entity"}},
    ]
    before = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted["declarations"][0]["name"].startswith("_somt_source_")
    assert len(adapted["declarations"][0]["name"]) <= 128
    assert adapted["declarations"][1:] == before["declarations"][1:]
    assert adapted["constraints"][0]["expr"]["args"][1] == {"var": "2sum"}
    assert raw == before
    assert replay_ledger(raw, ledger) == adapted


def test_function_definition_binders_scope_identifier_alpha_renaming():
    source = "A source span for the explicit definitions."
    raw = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "2sum", "sort": {"Uninterpreted": "Entity"}}],
        "functions": [
            {"name": "p", "arguments": [{"Uninterpreted": "Entity"}], "result": "Bool"},
            {"name": "uses_global", "arguments": [{"Uninterpreted": "Entity"}],
             "result": "Bool", "binders": [{"name": "x", "sort": {"Uninterpreted": "Entity"}}],
             "body": {"op": "and", "args": [
                 {"apply": "p", "args": [{"var": "x"}]},
                 {"apply": "p", "args": [{"var": "2sum"}]},
             ]}, "span": [0, len(source)]},
            {"name": "shadows_global", "arguments": [{"Uninterpreted": "Entity"}],
             "result": "Bool", "binders": [{"name": "2sum", "sort": {"Uninterpreted": "Entity"}}],
             "body": {"apply": "p", "args": [{"var": "2sum"}]},
             "span": [0, len(source)]},
        ],
        "constraints": [{"expr": {"var": "2sum"}, "span": [0, len(source)]}],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    adapted, _ = adapt_provider_forms(raw)
    encoded = adapted["declarations"][0]["name"]
    assert adapted["functions"][1]["body"]["args"][0]["args"][0] == {"var": "x"}
    assert adapted["functions"][1]["body"]["args"][1]["args"][0] == {"var": encoded}
    assert adapted["functions"][2]["body"]["args"][0] == {"var": "2sum"}
    assert adapted["constraints"][0]["expr"] == {"var": encoded}


def test_nested_quantifier_and_fold_binders_shadow_global_identifier():
    raw = model({"quantifier": "forall", "binders": [
        {"name": "2sum", "sort": {"Uninterpreted": "Entity"}}
    ], "body": {"op": "eq", "args": [
        {"var": "2sum"},
        {"fold": "sum", "var": "2sum", "range": [0, 2],
         "body": {"var": "2sum"}},
    ]}})
    raw["declarations"] = [{"name": "2sum", "sort": {"Uninterpreted": "Entity"}}]
    raw["constraints"].append({"expr": {"var": "2sum"}, "span": [12, 15]})
    adapted, _ = adapt_provider_forms(raw)
    encoded = adapted["declarations"][0]["name"]
    quantifier = adapted["constraints"][0]["expr"]
    assert quantifier["body"]["args"][0] == {"var": "2sum"}
    assert quantifier["body"]["args"][1]["body"] == {"var": "2sum"}
    assert adapted["constraints"][1]["expr"] == {"var": encoded}

    fold_model = model({"fold": "sum", "var": "2sum", "range": [0, 2],
                        "body": {"var": "2sum"}})
    fold_model["declarations"] = [{
        "name": "2sum", "sort": {"Uninterpreted": "Entity"}
    }]
    fold_model["constraints"].append({"expr": {"var": "2sum"}, "span": [12, 15]})
    fold_adapted, _ = adapt_provider_forms(fold_model)
    fold_encoded = fold_adapted["declarations"][0]["name"]
    assert fold_encoded != "2sum"
    assert fold_adapted["constraints"][0]["expr"]["var"] == "2sum"
    assert fold_adapted["constraints"][0]["expr"]["body"] == {"var": "2sum"}
    assert fold_adapted["constraints"][1]["expr"] == {"var": fold_encoded}


def test_scalar_entity_constant_function_collision_is_alpha_renamed():
    source = "Hyraxes are mammals; hyraxes lay eggs."
    raw = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "declarations": [
            {"name": "hyrax", "sort": {"Uninterpreted": "Entity"}},
            {"name": "somt_goal", "sort": "Bool"},
        ],
        "functions": [
            {"name": "hyrax", "arguments": [{"Uninterpreted": "Entity"}], "result": "Bool"},
            {"name": "mammal", "arguments": [{"Uninterpreted": "Entity"}], "result": "Bool"},
        ],
        "constraints": [
            {"expr": {"apply": "hyrax", "args": [{"var": "hyrax"}]},
             "span": [0, len(source)]},
            {"expr": {"apply": "mammal", "args": [{"var": "hyrax"}]},
             "span": [0, len(source)]},
            {"expr": {"op": "eq", "args": [
                {"var": "somt_goal"},
                {"op": "hyrax", "args": [{"var": "hyrax"}]},
            ]}, "span": [0, len(source)]},
        ],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    encoded = adapted["declarations"][0]["name"]
    assert encoded != "hyrax" and encoded.isidentifier() and len(encoded) <= 128
    assert adapted["functions"][0]["name"] == "hyrax"
    assert adapted["constraints"][0]["expr"]["apply"] == "hyrax"
    assert adapted["constraints"][0]["expr"]["args"] == [{"var": encoded}]
    assert adapted["constraints"][1]["expr"]["args"] == [{"var": encoded}]
    assert adapted["constraints"][2]["expr"]["args"][1] == {
        "apply": "hyrax", "args": [{"var": encoded}]
    }
    namespace_entries = [item for item in ledger
                         if item["rule"] == "entity-function-namespace-alpha-renaming"]
    assert len(namespace_entries) == 4
    assert raw == original
    assert replay_ledger(raw, ledger) == adapted
    assert adapt_provider_forms(adapted) == (adapted, [])

    translated = build_hir(adapted, source).translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2()))

    def find_constant(expression, name):
        if z3.is_const(expression) and str(expression.decl().name()) == name:
            return expression
        for child in expression.children():
            found = find_constant(child, name)
            if found is not None:
                return found
        return None

    def find_function(expression, name):
        if (z3.is_app(expression) and expression.num_args() > 0
                and str(expression.decl().name()) == name):
            return expression.decl()
        for child in expression.children():
            found = find_function(child, name)
            if found is not None:
                return found
        return None

    encoded_constant = find_constant(actual, encoded)
    entity = z3.FreshConst(encoded_constant.sort(), prefix="entity_hyrax")
    hyrax_predicate = find_function(actual, "hyrax")
    mammal_predicate = find_function(actual, "mammal")
    goal = find_constant(actual, "somt_goal")
    relabeled = z3.substitute(actual, (encoded_constant, entity))
    expected = z3.And(
        hyrax_predicate(entity), mammal_predicate(entity),
        goal == hyrax_predicate(entity),
    )
    solver = z3.Solver()
    solver.add(z3.Xor(relabeled, expected))
    assert solver.check() == z3.unsat


def test_ambiguous_function_or_declaration_names_are_not_alpha_renamed():
    raw = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "hyrax", "sort": {"Uninterpreted": "Entity"}}],
        "functions": [
            {"name": "hyrax", "arguments": [{"Uninterpreted": "Entity"}], "result": "Bool"},
            {"name": "hyrax", "arguments": [{"Uninterpreted": "Entity"}], "result": "Bool"},
        ],
        "constraints": [], "objectives": [], "objective_order": "single",
        "goal": None, "assumptions": [], "unresolved": [],
    }
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted == raw
    assert ledger == []

@pytest.mark.parametrize("guard_case", [
    "valid_plus_malformed_function_duplicate",
    "duplicate_functions",
    "duplicate_declarations",
    "datatype_constructor_collision",
    "datatype_selector_collision",
    "reserved_operator",
    "shaped_declaration",
    "bounded_declaration",
])
def test_namespace_alpha_renaming_requires_one_unambiguous_scalar_entity_and_function(guard_case):
    function = {"name": "hyrax", "arguments": [{"Uninterpreted": "Entity"}],
                "result": "Bool"}
    raw = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "hyrax", "sort": {"Uninterpreted": "Entity"}}],
        "functions": [deepcopy(function)],
        "constraints": [{"expr": {"apply": "hyrax", "args": [{"var": "hyrax"}]},
                        "span": [0, 10]}],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    if guard_case == "valid_plus_malformed_function_duplicate":
        raw["functions"].append({"name": "hyrax", "arguments": "not-a-list", "result": "Bool"})
    elif guard_case == "duplicate_functions":
        raw["functions"].append(deepcopy(function))
    elif guard_case == "duplicate_declarations":
        raw["declarations"].append(deepcopy(raw["declarations"][0]))
    elif guard_case == "datatype_constructor_collision":
        raw["datatypes"] = [{"name": "D", "constructors": [{"name": "hyrax", "fields": []}]}]
    elif guard_case == "datatype_selector_collision":
        raw["datatypes"] = [{"name": "D", "constructors": [{
            "name": "make_d", "fields": [{"name": "hyrax", "sort": "Int"}]
        }]}]
    elif guard_case == "reserved_operator":
        raw["declarations"][0]["name"] = "and"
        raw["functions"][0]["name"] = "and"
        raw["constraints"][0]["expr"] = {"apply": "and", "args": [{"var": "and"}]}
    elif guard_case == "shaped_declaration":
        raw["declarations"][0]["shape"] = [2]
    elif guard_case == "bounded_declaration":
        raw["declarations"][0]["lower"] = 0
    before = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert adapted == before
    assert ledger == []


def test_namespace_alpha_renaming_respects_same_named_lexical_binder():
    raw = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability",
        "declarations": [{"name": "hyrax", "sort": {"Uninterpreted": "Entity"}}],
        "functions": [{"name": "hyrax", "arguments": [{"Uninterpreted": "Entity"}],
                       "result": "Bool"}],
        "constraints": [
            {"expr": {"quantifier": "forall", "binders": [
                {"name": "hyrax", "sort": {"Uninterpreted": "Entity"}}
            ], "body": {"apply": "hyrax", "args": [{"var": "hyrax"}]}},
             "span": [0, 10]},
            {"expr": {"apply": "hyrax", "args": [{"var": "hyrax"}]},
             "span": [0, 10]},
        ],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    adapted, _ = adapt_provider_forms(raw)
    encoded = adapted["declarations"][0]["name"]
    assert encoded != "hyrax"
    assert adapted["constraints"][0]["expr"]["body"]["args"] == [{"var": "hyrax"}]
    assert adapted["constraints"][1]["expr"]["args"] == [{"var": encoded}]
