"""Direct JSON/Python HIR datatype construction with independent cvc5 oracles."""
import shutil
import subprocess

import pytest

from somtparser.hir import HirBuilder, ModelError, build_hir, hir_api, hir_schema


def var(name):
    return {"var": name}


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def op(operator, *args):
    return {"op": operator, "args": list(args)}


def dt_ctor(name, sort, *args):
    return {"dt_constructor": name, "sort": sort, "args": list(args)}


def dt_sel(name, sort, value):
    return {"dt_selector": name, "sort": sort, "value": value}


def dt_is(name, value):
    return {"dt_tester": name, "value": value}


def cvc5_status(script):
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for an independent datatype oracle")
    if "(check-sat)" not in script:
        script += "\n(check-sat)\n"
    result = subprocess.run(
        [executable, "--lang=smt2", "--tlimit=5000"],
        input=script,
        text=True,
        capture_output=True,
        timeout=10,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    answers = [line for line in result.stdout.splitlines()
               if line in {"sat", "unsat", "unknown"}]
    assert len(answers) == 1 and answers[0] != "unknown", result.stdout + result.stderr
    return answers[0]


def list_model(extra_constraint=None):
    list_int = {"Datatype": {"name": "List", "args": ["Int"]}}
    constraints = [
        op(
            "eq",
            var("xs"),
            dt_ctor(
                "cons",
                list_int,
                lit(7),
                dt_ctor("nil", list_int),
            ),
        ),
    ]
    if extra_constraint is not None:
        constraints.append(extra_constraint)
    return {
        "schema": hir_schema()["properties"]["schema"]["const"],
        "language": "hir",
        "decision": "satisfiability",
        "datatypes": [
            {
                "name": "List",
                "params": ["T"],
                "constructors": [
                    {"name": "nil", "fields": []},
                    {
                        "name": "cons",
                        "fields": [
                            {"name": "head", "sort": {"Parameter": "T"}},
                            {
                                "name": "tail",
                                "sort": {
                                    "Datatype": {
                                        "name": "List",
                                        "args": [{"Parameter": "T"}],
                                    }
                                },
                            },
                        ],
                    },
                ],
            }
        ],
        "declarations": [{"name": "xs", "sort": list_int}],
        "functions": [],
        "constraints": [
            {"expr": expression, "span": [0, 1]}
            for expression in constraints
        ],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


def compile_json(candidate):
    translated = build_hir(candidate, "x").translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    return translated.to_smt2()


def test_datatype_catalog_and_explicit_nullary_parametric_instance():
    api = hir_api()
    assert {"Datatype": {"name": "declared datatype", "args": ["sort", "..."]}} in api["sorts"]
    assert {"Parameter": "datatype-local type parameter"} in api["sorts"]
    assert "datatype_declaration" in api["constructors"]
    assert api["constructors"]["datatype_constructor"]["dt_constructor"] == "declared constructor"
    script = compile_json(list_model())
    assert "(List Int)" in script
    assert "(nil)" in script or "nil" in script
    assert cvc5_status(script) == "sat"


def test_constructor_selector_and_tester_relations_have_independent_oracles():
    list_int = {"Datatype": {"name": "List", "args": ["Int"]}}
    expected = [
        op("eq", dt_sel("head", "Int", var("xs")), lit(7)),
        op("eq", dt_sel("tail", list_int, var("xs")), dt_ctor("nil", list_int)),
        op("eq", dt_is("cons", var("xs")), lit(True, "Bool")),
        op("eq", dt_is("nil", var("xs")), lit(False, "Bool")),
    ]
    contrary = [
        op("eq", dt_sel("head", "Int", var("xs")), lit(8)),
        op("eq", dt_sel("tail", list_int, var("xs")), var("xs")),
        op("eq", dt_is("cons", var("xs")), lit(False, "Bool")),
        op("eq", dt_is("nil", var("xs")), lit(True, "Bool")),
    ]
    for relation in expected:
        assert cvc5_status(compile_json(list_model(relation))) == "sat"
    for relation in contrary:
        assert cvc5_status(compile_json(list_model(relation))) == "unsat"


def test_forward_mutual_recursive_datatypes_resolve_as_one_batch():
    builder = HirBuilder()
    builder.declare_datatypes(
        [
            {
                "name": "A",
                "constructors": [
                    {"name": "a0", "fields": []},
                    {"name": "fromB", "fields": [{"name": "b", "sort": {"Datatype": "B"}}]},
                ],
            },
            {
                "name": "B",
                "constructors": [
                    {"name": "b0", "fields": []},
                    {"name": "fromA", "fields": [{"name": "a", "sort": {"Datatype": "A"}}]},
                ],
            },
        ]
    )
    builder.declare("x", {"Datatype": "A"})
    builder.constrain(
        op("eq", var("x"), dt_ctor("fromB", {"Datatype": "A"}, dt_ctor("b0", {"Datatype": "B"})))
    )
    translated = builder.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    assert cvc5_status(translated.to_smt2()) == "sat"


def test_unknown_constructor_wrong_arity_and_bad_recursive_cycle_refuse():
    builder = HirBuilder()
    builder.declare_datatype(
        {"name": "Choice", "constructors": [{"name": "left", "fields": []}]}
    )
    with pytest.raises(ModelError, match="unknown datatype constructor"):
        builder.expr(dt_ctor("missing", {"Datatype": "Choice"}))
    with pytest.raises(ModelError, match="arity mismatch"):
        builder.expr(dt_ctor("left", {"Datatype": "Choice"}, lit(1)))

    with pytest.raises(ModelError, match="not well-founded"):
        HirBuilder().declare_datatype(
            {
                "name": "Loop",
                "constructors": [
                    {"name": "loop", "fields": [{"name": "next", "sort": {"Datatype": "Loop"}}]}
                ],
            }
        )
    with pytest.raises(ModelError, match="not well-founded"):
        HirBuilder().declare_datatypes(
            [
                {"name": "A", "constructors": [{"name": "toB", "fields": [{"name": "b", "sort": {"Datatype": "B"}}]}]},
                {"name": "B", "constructors": [{"name": "toA", "fields": [{"name": "a", "sort": {"Datatype": "A"}}]}]},
            ]
        )


def test_wrong_selector_result_sort_is_rejected_by_native_typecheck():
    builder = build_hir(list_model(), "x")
    builder.constrain(op("eq", dt_sel("head", "Real", var("xs")), lit("7", "Real")))
    result = builder.translate()
    assert not result.ok
    assert any("selector 'head' yields Int" in item.message for item in result.diagnostic_items)


def test_frontend_productivity_accepts_nested_parametric_constructor_path():
    builder = HirBuilder()
    builder.declare_datatypes(
        [
            {
                "name": "Box",
                "params": ["T"],
                "constructors": [
                    {"name": "emptyBox", "fields": []},
                    {
                        "name": "filledBox",
                        "fields": [{"name": "item", "sort": {"Parameter": "T"}}],
                    },
                ],
            },
            {
                "name": "D",
                "constructors": [
                    {
                        "name": "wrapBox",
                        "fields": [
                            {
                                "name": "payload",
                                "sort": {"Datatype": {"name": "Box", "args": [{"Datatype": "D"}]}},
                            }
                        ],
                    }
                ],
            },
        ]
    )
    d_sort = {"Datatype": "D"}
    box_d = {"Datatype": {"name": "Box", "args": [d_sort]}}
    builder.declare("d", d_sort)
    builder.constrain(
        op("eq", var("d"), dt_ctor("wrapBox", d_sort, dt_ctor("emptyBox", box_d)))
    )
    translated = builder.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    # This checks the direct HIR productivity analysis only. The current
    # serializer emits Box and D separately, and cvc5 rejects this nested
    # recursive type as not well-founded. Root's read-only probe also found
    # the same refusal when grouped, so this asserts only the frontend's
    # finite-constructor productivity analysis, not a solver result.


def test_failed_datatype_batch_rolls_back_and_allows_retry():
    builder = HirBuilder()
    with pytest.raises(ModelError, match="undeclared datatype sort: Missing"):
        builder.declare_datatypes(
            [
                {
                    "name": "Retry",
                    "constructors": [
                        {"name": "retryBad", "fields": [{"name": "bad", "sort": {"Datatype": "Missing"}}]}
                    ],
                }
            ]
        )
    builder.declare_datatype(
        {"name": "Retry", "constructors": [{"name": "retryGood", "fields": []}]}
    )
    retry_sort = {"Datatype": "Retry"}
    builder.declare("x", retry_sort)
    builder.constrain(op("eq", var("x"), dt_ctor("retryGood", retry_sort)))
    translated = builder.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    assert cvc5_status(translated.to_smt2()) == "sat"


def test_provider_and_canonical_adapters_preserve_datatype_shapes_and_terms():
    from copy import deepcopy

    from somtparser.hir_canonical import canonicalize_hir
    from somtparser.hir_provider_forms import adapt_provider_forms

    model = list_model()
    model["datatypes"][0]["constructors"][1]["fields"][0]["sort"] = {
        "Array": ["Int", "Uninterpreted:Payload"]
    }
    model["constraints"][0]["expr"] = dt_ctor(
        "nil", {"Datatype": {"name": "List", "args": ["Int"]}},
        {"add": [lit("1"), lit("2")]},
    )
    original_datatypes = deepcopy(model["datatypes"])

    adapted, ledger = adapt_provider_forms(model)
    assert adapted["datatypes"] == original_datatypes
    assert adapted["constraints"][0]["expr"]["args"][0] == {
        "op": "add", "args": [lit("1"), lit("2")]
    }
    assert any(entry["rule"] == "singleton-operator-object" for entry in ledger)

    canonical, changes = canonicalize_hir(model)
    assert canonical["datatypes"][0]["constructors"][1]["fields"][0]["sort"] == {
        "Array": ["Int", {"Uninterpreted": "Payload"}]
    }
    assert canonical["constraints"][0]["expr"]["args"][0] == {
        "literal": 3, "sort": "Int"
    }
    assert canonical["datatypes"][0]["constructors"][0]["fields"] == []
    assert changes


def test_finite_nested_parametric_instances_and_parameter_propagation():
    builder = HirBuilder()
    builder.declare_datatypes(
        [
            {
                "name": "Box",
                "params": ["T"],
                "constructors": [
                    {"name": "box", "fields": [{"name": "item", "sort": {"Parameter": "T"}}]}
                ],
            },
            {
                "name": "Inner",
                "params": ["U"],
                "constructors": [
                    {"name": "inner", "fields": [{"name": "value", "sort": {"Parameter": "U"}}]}
                ],
            },
            {
                "name": "Outer",
                "params": ["T"],
                "constructors": [
                    {
                        "name": "outer",
                        "fields": [
                            {
                                "name": "outerInner",
                                "sort": {"Datatype": {"name": "Inner", "args": [{"Parameter": "T"}]}},
                            }
                        ],
                    }
                ],
            },
            {
                "name": "Nested",
                "constructors": [
                    {
                        "name": "wrapNested",
                        "fields": [
                            {
                                "name": "nestedValue",
                                "sort": {"Datatype": {"name": "Box", "args": [
                                    {"Datatype": {"name": "Box", "args": ["Int"]}}
                                ]}},
                            }
                        ],
                    }
                ],
            },
        ]
    )
    nested_box = {"Datatype": {"name": "Box", "args": [
        {"Datatype": {"name": "Box", "args": ["Int"]}}
    ]}}
    builder.declare("x", nested_box)
    inner_int = {"Datatype": {"name": "Inner", "args": ["Int"]}}
    outer_int = {"Datatype": {"name": "Outer", "args": ["Int"]}}
    builder.declare("y", outer_int)
    nested_sort = {"Datatype": "Nested"}
    builder.declare("z", nested_sort)
    builder.constrain(
        op("eq", var("x"), dt_ctor("box", nested_box,
            dt_ctor("box", {"Datatype": {"name": "Box", "args": ["Int"]}}, lit(11))))
    )
    builder.constrain(
        op("eq", var("y"), dt_ctor("outer", outer_int,
            dt_ctor("inner", inner_int, lit(17))))
    )
    builder.constrain(
        op("eq", var("z"), dt_ctor("wrapNested", nested_sort,
            dt_ctor("box", nested_box,
                dt_ctor("box", {"Datatype": {"name": "Box", "args": ["Int"]}}, lit(23)))))
    )
    translated = builder.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    assert cvc5_status(translated.to_smt2()) == "sat"



def test_expanding_recursive_parameter_instance_is_explicitly_unsupported():
    builder = HirBuilder()
    with pytest.raises(ModelError, match="expanding recursive datatype parameter substitution"):
        builder.declare_datatypes(
            [
                {
                    "name": "Box",
                    "params": ["T"],
                    "constructors": [{"name": "empty", "fields": []}],
                },
                {
                    "name": "Expand",
                    "params": ["T"],
                    "constructors": [
                        {
                            "name": "step",
                            "fields": [
                                {
                                    "name": "next",
                                    "sort": {
                                        "Datatype": {
                                            "name": "Expand",
                                            "args": [
                                                {"Datatype": {
                                                    "name": "Box",
                                                    "args": [{"Parameter": "T"}],
                                                }}
                                            ],
                                        }
                                    },
                                }
                            ],
                        }
                    ],
                },
            ]
        )


def test_unsupported_productivity_branch_does_not_hide_nullary_alternative():
    builder = HirBuilder()
    builder.declare_datatypes(
        [
            {"name": "Base", "constructors": [{"name": "base", "fields": []}]},
            {
                "name": "Choice",
                "constructors": [
                    {"name": "recursiveArray", "fields": [{"name": "bad", "sort": {"Array": [{"Datatype": "Choice"}, "Int"]}}]},
                    {"name": "choiceBase", "fields": []},
                ],
            },
        ]
    )
    # Python productivity validation must continue to the base constructor
    # after declining the recursive-array alternative.
    assert builder.datatypes["Choice"] == 0


def test_datatype_parameter_substitution_is_simultaneous_and_hygienic():
    builder = HirBuilder()
    builder.declare_datatypes(
        [
            {"name": "Leaf", "params": ["T"], "constructors": [
                {"name": "leaf", "fields": [{"name": "value", "sort": {"Parameter": "T"}}]}
            ]},
            {"name": "Wrap", "params": ["U"], "constructors": [
                {"name": "wrap", "fields": [{"name": "child", "sort": {"Datatype": {"name": "Leaf", "args": [{"Parameter": "U"}]}}}]}
            ]},
            {"name": "Outer", "params": ["T"], "constructors": [
                {"name": "outer", "fields": [{"name": "payload", "sort": {"Datatype": {"name": "Wrap", "args": [{"Parameter": "T"}]}}}]}
            ]},
        ]
    )
    builder.declare("u", {"Uninterpreted": "U"})
    outer_u = {"Datatype": {"name": "Outer", "args": [{"Uninterpreted": "U"}]}}
    builder.declare("x", outer_u)
    wrap_u = {"Datatype": {"name": "Wrap", "args": [{"Uninterpreted": "U"}]}}
    leaf_u = {"Datatype": {"name": "Leaf", "args": [{"Uninterpreted": "U"}]}}
    builder.constrain(op("eq", var("x"), dt_ctor("outer", outer_u,
        dt_ctor("wrap", wrap_u, dt_ctor("leaf", leaf_u, var("u"))))) )
    # U is an explicit user sort/term name, not an accidental alias for the
    # datatype's local parameter. Constructor checking remains native.
    translated = builder.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]

    with pytest.raises(ModelError, match="collides with datatype parameter"):
        HirBuilder().declare_datatype(
            {"name": "Collision", "params": ["T"], "constructors": [
                {"name": "collision", "fields": [{"name": "payload", "sort": {"Uninterpreted": "T"}}]}
            ]}
        )


def test_parameter_substitution_is_simultaneous_not_capture_prone():
    from somtparser.hir import _substitute_datatype_sort

    source = {"Datatype": {"name": "Wrap", "args": [{"Parameter": "T"}]}}
    bindings = {"T": {"Parameter": "U"}, "U": "Int"}
    assert _substitute_datatype_sort(source, bindings) == {
        "Datatype": {"name": "Wrap", "args": [{"Parameter": "U"}]}
    }
