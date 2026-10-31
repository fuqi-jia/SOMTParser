"""Source-witness replay: exact values checked against the candidate's own ASTs.

The replay substitutes source-level values into the typed candidate's ASTs
under the same relational semantics the compiler encodes, so a wrong encoding
or projection cannot validate itself. The differential tests pin the mirror
against z3's reading of the emitted SMT.
"""
from fractions import Fraction

import pytest
import somtparser as sp
from somtparser.natural_language import _candidate, _compile, ModelError


def at(source, text):
    i = source.index(text)
    return [i, i + len(text)]


def typed(source, model, decision="satisfiability"):
    m = {
        "schema": "somt-nl-model-v1",
        "semantics": "relational-v1",
        "decision": decision,
        "domains": [],
        "symbols": [],
        "constraints": [],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }
    m.update(model)
    t = _compile(_candidate(source, m, "replay-test"), "test", "default", None)
    assert t.ok, t.diagnostics
    return t


def kinds(report):
    return [v["kind"] for v in report["violations"]]


def test_constraint_replay_holds_and_violates():
    source = "Let x be an integer between 0 and 10.\nx is at least 3.\nFind a solution.\n"
    t = typed(
        source,
        {
            "symbols": [
                {
                    "name": "x",
                    "sort": "Int",
                    "arguments": [],
                    "span": at(source, "x"),
                    "lower": 0,
                    "upper": 10,
                }
            ],
            "constraints": [
                {
                    "expr": {
                        "op": "ge",
                        "args": [{"var": "x"}, {"literal": 3, "sort": "Int"}],
                    },
                    "span": at(source, "x is at least 3"),
                }
            ],
        },
    )
    assert t.replay_assignment({"x": 3})["holds"]
    report = t.replay_assignment({"x": 2})
    assert not report["holds"]
    assert kinds(report) == ["constraint"]
    assert report["violations"][0]["fragment"] == "x is at least 3"
    # The declaration bound is a source constraint too: 11 satisfies the
    # comparison but violates "between 0 and 10".
    report = t.replay_assignment({"x": 11})
    assert kinds(report) == ["bound"]
    assert report["violations"][0]["fragment"] == "x"


def test_ite_evaluates_only_the_taken_branch():
    source = "If x is positive the value is 10 tdiv x, otherwise it is 7.\n"
    ite = {
        "op": "ite",
        "args": [
            {"op": "gt", "args": [{"var": "x"}, {"literal": 0, "sort": "Int"}]},
            {"op": "tdiv", "args": [{"literal": 10, "sort": "Int"}, {"var": "x"}]},
            {"literal": 7, "sort": "Int"},
        ],
    }
    t = typed(
        source,
        {
            "symbols": [
                {"name": "x", "sort": "Int", "arguments": [], "span": at(source, "x")}
            ],
            "constraints": [
                {
                    "expr": {
                        "op": "eq",
                        "args": [ite, {"literal": 7, "sort": "Int"}],
                    },
                    "span": [0, len(source) - 1],
                }
            ],
        },
    )
    # x = 0 takes the else branch: the tdiv is never evaluated, exactly as the
    # encoding's (ite c d1 d2) definedness guard short-circuits. A replay that
    # demanded both branches defined would invent a violation here.
    assert t.replay_assignment({"x": 0})["holds"]
    # x = 2 takes the tdiv branch: 10 tdiv 2 = 5, not 7.
    assert not t.replay_assignment({"x": 2})["holds"]


def test_taken_branch_division_by_zero_is_undefined():
    source = "10 tdiv x is 5.\n"
    t = typed(
        source,
        {
            "symbols": [
                {"name": "x", "sort": "Int", "arguments": [], "span": at(source, "x")}
            ],
            "constraints": [
                {
                    "expr": {
                        "op": "eq",
                        "args": [
                            {
                                "op": "tdiv",
                                "args": [{"literal": 10, "sort": "Int"}, {"var": "x"}],
                            },
                            {"literal": 5, "sort": "Int"},
                        ],
                    },
                    "span": [0, len(source) - 1],
                }
            ],
        },
    )
    # The encoding asserts the divisor is nonzero as part of the constraint,
    # so x = 0 is a violation -- the constraint is undefined, not "true".
    assert not t.replay_assignment({"x": 0})["holds"]
    assert t.replay_assignment({"x": 2})["holds"]
    assert not t.replay_assignment({"x": 3})["holds"]


def test_tdiv_sign_known_answers():
    source = "Truncating division follows the dividend's sign.\n"

    def eq_tdiv(a, b, r):
        return {
            "expr": {
                "op": "eq",
                "args": [
                    {
                        "op": "tdiv",
                        "args": [
                            {"literal": a, "sort": "Int"},
                            {"literal": b, "sort": "Int"},
                        ],
                    },
                    {"literal": r, "sort": "Int"},
                ],
            },
            "span": [0, len(source) - 1],
        }

    t = typed(
        source,
        {
            "constraints": [
                eq_tdiv(-7, 2, -3),
                eq_tdiv(7, -2, -3),
                eq_tdiv(-7, -2, 3),
                eq_tdiv(7, -2, -4),  # truncation gives -3, not floor's -4
            ]
        },
    )
    report = t.replay_assignment({})
    assert [v["index"] for v in report["violations"]] == [3]


def test_real_division_is_exact():
    source = "One half is 1/2, never a float.\n"
    t = typed(
        source,
        {
            "symbols": [
                {
                    "name": "r",
                    "sort": "Real",
                    "arguments": [],
                    "span": at(source, "half"),
                }
            ],
            "constraints": [
                {
                    "expr": {
                        "op": "eq",
                        "args": [
                            {"var": "r"},
                            {
                                "op": "div",
                                "args": [
                                    {"literal": "1", "sort": "Real"},
                                    {"literal": "2", "sort": "Real"},
                                ],
                            },
                        ],
                    },
                    "span": [0, len(source) - 1],
                }
            ],
        },
    )
    assert t.replay_assignment({"r": "1/2"})["holds"]
    assert not t.replay_assignment({"r": "0.500001"})["holds"]
    with pytest.raises(ModelError, match="not a float"):
        t.replay_assignment({"r": 0.5})


def test_quantifiers_enumerate_the_finite_domain():
    source = "域Color包含R、G、B。设c为Color类型变量。\n"
    t = typed(
        source,
        {
            "domains": [
                {"name": "Color", "members": ["R", "G", "B"], "span": at(source, "Color")}
            ],
            "symbols": [
                {
                    "name": "c",
                    "sort": "Color",
                    "arguments": [],
                    "span": at(source, "c"),
                }
            ],
            "constraints": [
                {
                    "expr": {
                        "op": "exists",
                        "var": "v",
                        "domain": "Color",
                        "body": {"op": "eq", "args": [{"var": "v"}, {"var": "c"}]},
                    },
                    "span": [0, len(source) - 1],
                },
                {
                    "expr": {
                        "op": "forall",
                        "var": "w",
                        "domain": "Color",
                        "body": {"op": "eq", "args": [{"var": "w"}, {"var": "c"}]},
                    },
                    "span": [0, len(source) - 1],
                },
            ],
        },
    )
    # Some member equals c (three candidates, one is), but not all do.
    report = t.replay_assignment({"c": "R"})
    assert [v["index"] for v in report["violations"]] == [1]
    # A non-member is a declaration violation first; both quantified
    # constraints then fail as well, and none of it crashes evaluation.
    report = t.replay_assignment({"c": "Z"})
    assert kinds(report) == ["domain", "constraint", "constraint"]


def test_objective_values_and_definedness():
    source = "Minimize the reciprocal of x.\n"
    t = typed(
        source,
        {
            "symbols": [
                {"name": "x", "sort": "Real", "arguments": [], "span": at(source, "x")}
            ],
            "objectives": [
                {
                    "direction": "minimize",
                    "expr": {
                        "op": "div",
                        "args": [
                            {"literal": "1", "sort": "Real"},
                            {"var": "x"},
                        ],
                    },
                    "span": at(source, "reciprocal"),
                }
            ],
        },
        decision="optimization",
    )
    report = t.replay_assignment({"x": "1/2"})
    assert report["holds"]
    assert report["objectives"] == [{"value": Fraction(2), "defined": True}]
    # The compiler asserts the objective's definedness as a constraint, so an
    # undefined objective is a violation, not a value.
    report = t.replay_assignment({"x": 0})
    assert kinds(report) == ["objective-definedness"]
    assert report["objectives"][0]["defined"] is False


def test_predicate_replay_is_refused_by_name():
    source = "p holds of x.\n"
    t = typed(
        source,
        {
            "symbols": [
                {
                    "name": "p",
                    "sort": "Bool",
                    "arguments": ["Int"],
                    "span": at(source, "p"),
                },
                {"name": "x", "sort": "Int", "arguments": [], "span": at(source, "x")},
            ],
            "constraints": [
                {
                    "expr": {"op": "call", "symbol": "p", "args": [{"var": "x"}]},
                    "span": [0, len(source) - 1],
                }
            ],
        },
    )
    with pytest.raises(ModelError, match="interpretation"):
        t.replay_assignment({"x": 1})


def test_assignment_interface_errors():
    source = "Let x be an integer.\nx is at least 0.\nFind a solution.\n"
    t = typed(
        source,
        {
            "symbols": [
                {"name": "x", "sort": "Int", "arguments": [], "span": at(source, "x")}
            ],
            "constraints": [
                {
                    "expr": {
                        "op": "ge",
                        "args": [{"var": "x"}, {"literal": 0, "sort": "Int"}],
                    },
                    "span": at(source, "x is at least 0"),
                }
            ],
        },
    )
    with pytest.raises(ModelError, match="missing value"):
        t.replay_assignment({})
    with pytest.raises(ModelError, match="no scalar symbol"):
        t.replay_assignment({"x": 1, "y": 2})
    with pytest.raises(ModelError, match="exact integer"):
        t.replay_assignment({"x": 0.5})
    with pytest.raises(ModelError, match="exact integer"):
        t.replay_assignment({"x": True})


def test_replay_requires_a_successful_typed_translation():
    source = "Let x be an integer.\nx is fairly small.\nFind a solution.\n"
    bad = {"unresolved": ["fairly small is ambiguous"]}
    m = {
        "schema": "somt-nl-model-v1",
        "semantics": "relational-v1",
        "decision": "satisfiability",
        "domains": [],
        "symbols": [],
        "constraints": [],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
    }
    m.update(bad)
    t = _compile(_candidate(source, m, "replay-test"), "test", "default", None)
    assert not t.ok
    with pytest.raises(ModelError, match="unsuccessful translation"):
        t.replay_assignment({})

    formal = {
        "schema": "somt-nl-formal-v1",
        "language": "minizinc",
        "program": "var 0..9: x;\nconstraint x > 2;\nsolve satisfy;\n",
        "decision": "satisfiability",
        "assumptions": [],
        "unresolved": [],
        "links": [{"span": at(source, "x"), "fragment": "var 0..9: x"}],
        "context": {},
    }
    t = _compile(_candidate(source, formal, "replay-test"), "test", "default", None)
    assert t.ok, t.diagnostics
    with pytest.raises(ModelError, match="no checked NL replay"):
        t.replay_assignment({"x": 3})


def test_goal_is_reported_for_validity():
    source = "Prove that x is at least 0.\n"
    t = typed(
        source,
        {
            "symbols": [
                {"name": "x", "sort": "Int", "arguments": [], "span": at(source, "x")}
            ],
            "goal": {
                "expr": {
                    "op": "ge",
                    "args": [{"var": "x"}, {"literal": 0, "sort": "Int"}],
                },
                "span": at(source, "x is at least 0"),
            },
        },
        decision="validity",
    )
    assert t.replay_assignment({"x": 1})["goal"] is True
    assert t.replay_assignment({"x": -1})["goal"] is False


def _z3_sat_with(script, name, value, sort):
    z3 = pytest.importorskip("z3")
    solver = z3.Solver()
    solver.from_string(script)
    solver.add(sort(name) == value)
    return solver.check() == z3.sat


def test_replay_agrees_with_the_emitted_encoding():
    """The mirror is checked against z3's reading of the emitted SMT: for every
    value in and around the declared bounds, the solver finding the pinned
    encoding (un)satisfiable must equal the replay's holds."""
    z3 = pytest.importorskip("z3")
    source = "Let x be an integer between 0 and 10.\nx is at least 3.\nFind a solution.\n"
    t = sp.translate_nl(source)
    assert t.ok, t.diagnostics
    script = t.to_smt2()
    for x in range(-1, 13):
        assert t.replay_assignment({"x": x})["holds"] == _z3_sat_with(
            script, "nl_s0", x, z3.Int
        ), x


def test_definedness_replay_agrees_with_the_emitted_encoding():
    """x = 0 is unsatisfiable in the encoding (the divisor guard is asserted)
    and a violation in the replay; agreement across signs of the divisor."""
    z3 = pytest.importorskip("z3")
    source = "10 tdiv x is 5.\n"
    t = typed(
        source,
        {
            "symbols": [
                {"name": "x", "sort": "Int", "arguments": [], "span": at(source, "x")}
            ],
            "constraints": [
                {
                    "expr": {
                        "op": "eq",
                        "args": [
                            {
                                "op": "tdiv",
                                "args": [{"literal": 10, "sort": "Int"}, {"var": "x"}],
                            },
                            {"literal": 5, "sort": "Int"},
                        ],
                    },
                    "span": [0, len(source) - 1],
                }
            ],
        },
    )
    script = t.to_smt2()
    for x in [-5, -2, 0, 2, 5]:
        assert t.replay_assignment({"x": x})["holds"] == _z3_sat_with(
            script, "nl_s0", x, z3.Int
        ), x


def test_solver_witness_projects_and_replays():
    """End to end: a z3 witness decodes through project_assignment and then
    passes the replay -- the chain the replay exists to audit."""
    z3 = pytest.importorskip("z3")
    source = "Let b be a boolean.\nLet x be a real.\nb.\nIf b, then x = 0.1.\nFind a solution.\n"
    t = sp.translate_nl(source)
    assert t.ok, t.diagnostics
    solver = z3.Solver()
    solver.from_string(t.to_smt2())
    assert solver.check() == z3.sat
    model = solver.model()
    witness = {
        "nl_s0": z3.is_true(model[z3.Bool("nl_s0")]),
        "nl_s1": model[z3.Real("nl_s1")].as_fraction(),
    }
    source_values = t.project_assignment(witness)
    assert source_values == {"b": True, "x": Fraction(1, 10)}
    assert t.replay_assignment(source_values)["holds"]
