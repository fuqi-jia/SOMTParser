"""Default backend Set configuration and quantified finite-carrier contract."""
import shutil

import pytest

from somtparser.hir import HirBuilder
import somtparser as sp
from somtparser._solving import FidelityError, Formula


def var(name):
    return {"var": name}


def lit(value, sort):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def solve(builder, args=None):
    if shutil.which("cvc5") is None:
        pytest.skip("cvc5 is required for the Set backend oracle")
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    formula = Formula(translated, "hir", backend="cvc5", timeout=10, args=args)
    return formula.solve()


def test_default_solve_auto_enables_sets_exp_and_records_mode():
    b = HirBuilder()
    b.declare("S", {"Set": "Bool"})
    explicit_pair = op("set.insert", lit(True, "Bool"), lit(False, "Bool"),
                       lit("set.empty", {"Set": "Bool"}))
    b.constrain(op("eq", op("set.card", explicit_pair), lit(2, "Int")))
    b.constrain(op("eq", var("S"), explicit_pair))
    result = solve(b)
    assert result.status == "sat"
    assert "--sets-exp" in result.backend_options
    assert result.semantic_mode == "quantifier-free-finite-sets"


def test_quantified_set_bool_matches_all_four_subsets_oracle():
    # For each of the four subsets of Bool, universal membership is equivalent
    # to checking the two carrier values directly.
    domain = {False, True}
    subsets = [set(), {False}, {True}, {False, True}]
    for subset in subsets:
        quantified_value = all(value in subset for value in domain)
        ground_value = (False in subset) and (True in subset)
        assert quantified_value == ground_value

    quantified = {
        "quantifier": "forall",
        "binders": [{"name": "x", "sort": "Bool"}],
        "body": op("set.member", var("x"), var("S")),
    }
    ground = op(
        "and",
        op("set.member", lit(False, "Bool"), var("S")),
        op("set.member", lit(True, "Bool"), var("S")),
    )
    claim = op("eq", quantified, ground)
    b = HirBuilder()
    b.declare("S", {"Set": "Bool"})
    b.constrain(claim)
    result = solve(b)
    assert result.status == "sat"
    assert result.semantic_mode == "quantified-finite-carrier-sets"
    assert "--sets-exp" in result.backend_options
    assert "--finite-model-find" in result.backend_options

    negated = HirBuilder()
    negated.declare("S", {"Set": "Bool"})
    negated.constrain(op("not", claim))
    assert solve(negated).status == "unsat"


def test_quantified_set_bool_cardinality_all_subsets_sat_and_negation_unsat():
    # The complete Bool carrier has exactly four subsets, each with size <= 2.
    subsets = [set(), {False}, {True}, {False, True}]
    assert len(subsets) == 4
    assert all(len(subset) <= 2 for subset in subsets)
    formula = {
        "quantifier": "forall",
        "binders": [{"name": "S", "sort": {"Set": "Bool"}}],
        "body": op("le", op("set.card", var("S")), lit(2, "Int")),
    }
    positive = HirBuilder()
    positive.constrain(formula)
    result = solve(positive)
    assert result.status == "sat"
    assert result.semantic_mode == "quantified-finite-carrier-sets"
    assert "--sets-exp" in result.backend_options
    assert "--finite-model-find" in result.backend_options

    negative = HirBuilder()
    negative.constrain(op("not", formula))
    assert solve(negative).status == "unsat"


def test_quantified_set_int_is_refused_before_solver_call(monkeypatch):
    from somtparser import _solving

    b = HirBuilder()
    b.declare("S", {"Set": "Int"})
    b.constrain({"quantifier": "forall", "binders": [{"name": "x", "sort": "Int"}], "body": op("set.member", var("x"), var("S"))})
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    monkeypatch.setattr(_solving._backends, "run", lambda *a, **k: pytest.fail("solver must not run"))
    with pytest.raises(FidelityError, match="infinite or unknown carrier"):
        Formula(translated, "hir", backend="cvc5", timeout=10).solve()


@pytest.mark.parametrize("choice", ["--no-finite-model-find", "--finite-model-find=false", "--finite-model-find"])
def test_quantified_set_preserves_explicit_model_finding_choice(monkeypatch, choice):
    from somtparser import _solving

    b = HirBuilder()
    b.declare("S", {"Set": "Bool"})
    b.constrain({"quantifier": "forall", "binders": [{"name": "x", "sort": "Bool"}],
                 "body": op("set.member", var("x"), var("S"))})
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    seen = []

    def run(name, script, timeout, seed, path, args):
        seen.append(tuple(args))
        return "unknown", "unknown", 0.0

    monkeypatch.setattr(_solving._backends, "run", run)
    expected = ("--lang=smt2", choice, "--sets-exp")
    result = Formula(translated, "hir", backend="cvc5", args=expected[:2]).solve()
    assert seen == [expected]
    assert result.backend_options == expected
    assert result.status == "unknown"


def test_explicit_disable_conflicts_with_required_sets_exp():
    b = HirBuilder()
    b.declare("S", {"Set": "Bool"})
    b.constrain(op("eq", var("S"), lit("set.empty", {"Set": "Bool"})))
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    with pytest.raises(FidelityError, match="disable required --sets-exp"):
        Formula(translated, "hir", backend="cvc5", args=("--lang=smt2", "--sets-exp=false")).solve()


def test_set_requirement_follows_array_and_function_signatures():
    from somtparser import _solving

    for container_sort, make_set in (
        ({"Array": ["Int", {"Set": "Int"}]}, lambda: op("select", var("A"), var("x"))),
        (None, lambda: {"apply": "make", "args": [var("x")]}),
    ):
        b = HirBuilder()
        if container_sort is not None:
            b.declare("A", container_sort)
        else:
            b.declare_function("make", ["Int"], {"Set": "Int"})
        selected = make_set()
        b.constrain({
            "quantifier": "forall",
            "binders": [{"name": "x", "sort": "Int"}],
            "body": op("eq", op("set.card", selected), lit(0, "Int")),
        })
        translated = b.translate()
        assert translated.ok, [d.message for d in translated.diagnostic_items]
        assert translated.set_solver_requirements.has_sets
        assert translated.set_solver_requirements.has_quantifiers
        assert translated.set_solver_requirements.infinite_or_unknown_carrier
        monkeypatch_result = []
        old_run = _solving._backends.run
        _solving._backends.run = lambda *a, **k: monkeypatch_result.append(True)
        try:
            with pytest.raises(FidelityError, match="infinite or unknown carrier"):
                Formula(translated, "hir", backend="cvc5", timeout=10).solve()
        finally:
            _solving._backends.run = old_run
        assert not monkeypatch_result


def test_result_records_actual_backend_argv_including_seed(monkeypatch):
    from somtparser import _solving

    b = HirBuilder()
    b.declare("S", {"Set": "Bool"})
    b.constrain(op("eq", var("S"), lit("set.empty", {"Set": "Bool"})))
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    seen = {}

    def fake_run(name, script, timeout, seed, path, args):
        seen["name"] = name
        seen["args"] = tuple(args)
        seen["seed"] = seed
        return "sat", "sat", 0.0

    monkeypatch.setattr(_solving._backends, "run", fake_run)
    result = Formula(translated, "hir", backend="cvc5", seed=17).solve()
    assert result.status == "sat"
    assert seen["args"] == ("--lang=smt2", "--sets-exp")
    assert seen["seed"] == 17
    assert result.backend_options == ("--lang=smt2", "--sets-exp", "--seed=17")


def test_nested_finite_and_infinite_array_carriers_are_classified():
    finite = HirBuilder()
    finite.declare("S", {"Set": {"Array": ["Bool", "Bool"]}})
    finite_result = finite.translate()
    assert finite_result.ok, [d.message for d in finite_result.diagnostic_items]
    requirements = finite_result.set_solver_requirements
    assert requirements.has_sets and not requirements.infinite_or_unknown_carrier

    infinite = HirBuilder()
    infinite.declare("S", {"Set": {"Array": ["Int", "Bool"]}})
    infinite_result = infinite.translate()
    assert infinite_result.ok, [d.message for d in infinite_result.diagnostic_items]
    assert infinite_result.set_solver_requirements.infinite_or_unknown_carrier


def test_nonrecursive_finite_datatype_set_carrier_is_classified():
    source = """(set-logic ALL)
(declare-datatype Flag ((off) (on)))
(declare-const S (Set Flag))
(assert (forall ((x Flag)) (set.member x S)))
"""
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    requirements = translated.set_solver_requirements
    assert requirements.has_sets and requirements.has_quantifiers
    assert not requirements.infinite_or_unknown_carrier


def test_optimize_without_objectives_still_configures_sets_exp():
    if shutil.which("cvc5") is None:
        pytest.skip("cvc5 is required for the Set backend oracle")
    b = HirBuilder()
    b.declare("S", {"Set": "Bool"})
    b.constrain(op("eq", var("S"), lit("set.empty", {"Set": "Bool"})))
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    result = Formula(translated, "hir", backend="cvc5", timeout=10).optimize()
    assert result.status == "sat"
    assert "--sets-exp" in result.backend_options
    assert result.semantic_mode == "quantifier-free-finite-sets"


def test_parametric_datatype_set_carrier_uses_instantiated_fields():
    template = """(set-logic ALL)
(declare-datatypes ((Box 1))
  ((par (T) ((box (payload T))))))
"""
    cases = (
        ("(Box Bool)", False),
        ("(Box Int)", True),
        ("(Set Bool)", False),
        ("(Box (Set Bool))", False),
        ("(Box (Box Bool))", False),
    )
    for element_sort, unknown in cases:
        source = template + f"""(declare-const S (Set {element_sort}))
(assert (forall ((x {element_sort})) (set.member x S)))
"""
        translated = sp.translate(source=source, language="smtlib2")
        assert translated.ok, [item.message for item in translated.diagnostic_items]
        requirements = translated.set_solver_requirements
        assert requirements.has_sets and requirements.has_quantifiers
        assert requirements.infinite_or_unknown_carrier is unknown


def test_parametric_datatype_set_field_substitutes_parameters():
    template = """(set-logic ALL)
(declare-datatypes ((SetBox 1))
  ((par (T) ((setbox (contents (Set T)))))))
"""
    for parameter, unknown in (("Bool", False), ("Int", True)):
        source = template + f"""(declare-const x (SetBox {parameter}))
(assert (= x x))
"""
        translated = sp.translate(source=source, language="smtlib2")
        assert translated.ok, [item.message for item in translated.diagnostic_items]
        requirements = translated.set_solver_requirements
        assert requirements.has_sets
        assert requirements.infinite_or_unknown_carrier is unknown


def test_nested_parametric_datatype_set_carrier_preserves_instance_scope():
    source = """(set-logic ALL)
(declare-datatypes ((Box 1))
  ((par (T) ((box (payload T))))))
(declare-datatypes ((BoxBox 1))
  ((par (T) ((boxbox (outer_payload (Box (Box T))))))))
(declare-const S (Set (BoxBox Bool)))
(assert (= S (as set.empty (Set (BoxBox Bool)))))
"""
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    requirements = translated.set_solver_requirements
    assert requirements.has_sets
    assert not requirements.infinite_or_unknown_carrier


def test_sort_cache_distinguishes_quoted_datatype_name_from_set_spelling():
    # Both sort spellings stringify as `(Set Bool)` in display-oriented code.
    # The quoted datatype contains a Set Int field; inspecting the real Set Bool
    # first must not hide its infinite field carrier.
    source = """(set-logic ALL)
(declare-datatypes ((|(Set Bool)| 0))
  (((quoted_box (payload (Set Int))))) )
(declare-const finite_sets (Set Bool))
(declare-const quoted_value |(Set Bool)|)
(assert (= finite_sets (as set.empty (Set Bool))))
(assert (forall ((x |(Set Bool)|)) (= (payload x) (as set.empty (Set Int)))))
"""
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    requirements = translated.set_solver_requirements
    assert requirements.has_sets
    assert requirements.has_quantifiers
    assert requirements.infinite_or_unknown_carrier
