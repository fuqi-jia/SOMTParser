"""Exact provider envelopes and actionable sorts; no inferred model meaning."""
from copy import deepcopy

import pytest
import z3
import somtparser as sp
from somtparser.hir import HirBuilder, ModelError, build_hir, hir_api
from somtparser.hir_provider_forms import adapt_provider_forms
from somtparser.natural_language import Candidate, _candidate
from test_hir_provider_forms import model, replay_ledger


SOURCE = "Choose the declared values satisfying the displayed relation."


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def raw_model(expr):
    value = model(expr)
    value.pop("context")
    value["declarations"] = [{"name": "x", "sort": "Int"}]
    value["constraints"] = [dict(deepcopy(expr), span=[0, len(SOURCE)])]
    return value


def parsed(value):
    translated = build_hir(value, SOURCE).translate()
    assert translated.ok, translated.diagnostic_items
    target = z3.Optimize()
    text = translated.to_smt2(dialect=sp.OmtDialect.Z3)
    assert "define-objective" not in text and "optimize-sat" not in text
    target.from_string(text)
    assert len(target.objectives()) == len(value["objectives"])
    return z3.And(*target.assertions()), list(target.objectives())


def same(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def project_private_witnesses(formula, source_names):
    # Positive-exists lowering extends a target assignment with fresh private
    # constants. Compare the complete relation on source-visible coordinates,
    # not its value at an arbitrary assignment to those private witnesses.
    # Source names remain public even when they resemble the generated prefix.
    public = {name[1:-1] if name.startswith("|") and name.endswith("|") else name
              for name in source_names}
    witnesses, seen, pending = [], set(), [formula]
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if z3.is_quantifier(term):
            pending.append(term.body())
        elif z3.is_app(term):
            if z3.is_const(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                name = str(term.decl().name())
                if name not in public:
                    assert name.startswith("!somt_exists_"), ("unexpected target-private symbol", name)
                    witnesses.append(term)
            pending.extend(term.children())
    # Quantify around all assertions together; no witness constraint is dropped
    # and existing inner quantifiers/binder scope remain untouched.
    return z3.Exists(witnesses, formula) if witnesses else formula


@pytest.mark.parametrize("expr,oracle", [
    (op("eq", {"var": "x"}, lit(7)), z3.Int("x") == 7),
    ({"cp": "all_different", "items": [{"var": "x"}, lit(7)]}, z3.Int("x") != 7),
    ({"cp": "global_cardinality", "items": [{"var": "x"}],
      "values": [2, 3], "counts": [lit(1), lit(0)], "closed": True}, z3.Int("x") == 2),
])
def test_explicit_statement_normalization_preserves_full_relation_and_replay(expr, oracle):
    raw = raw_model(expr)
    before = deepcopy(raw)
    with pytest.raises(ModelError, match="missing fields"):
        build_hir(raw, SOURCE)
    adapted, ledger = adapt_provider_forms(raw)
    assert raw == before and replay_ledger(raw, ledger) == adapted
    assert ledger[0]["rule"] == "annotated-expression-statement"
    assert ledger[0]["path"] == "/constraints/0"
    assert adapted["constraints"][0]["span"] == raw["constraints"][0]["span"]
    assert adapt_provider_forms(adapted) == (adapted, [])
    actual, _ = parsed(adapted)
    same(actual, oracle)
    candidate = sp.propose_nl(SOURCE, language="hir", provider=lambda _: raw)
    assert candidate.valid, candidate.diagnostics
    assert replay_ledger(dict(raw, context={}), candidate.normalization_ledger) == candidate.model
    assert raw == before
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest and restored.to_json() == candidate.to_json()


def test_original_rejected_snapshot_is_not_recanonicalized_on_load():
    raw = raw_model(op("eq", {"var": "x"}, lit(7)))
    original = _candidate(SOURCE, raw, "frozen-before-provider-adapter")
    assert not original.valid and not original.normalization_ledger
    restored = Candidate.from_json(original.to_json())
    assert restored.to_json() == original.to_json()
    assert not restored.valid and restored.model == raw


def test_objective_envelope_keeps_exact_signed_cost_and_constraint_relation():
    raw = raw_model(op("ge", {"var": "x"}, lit(-4)))
    raw.update(decision="optimization", objectives=[dict(
        op("add", {"var": "x"}, lit(2)), sense="maximize", span=[0, len(SOURCE)])])
    adapted, ledger = adapt_provider_forms(raw)
    assert [item["path"] for item in ledger] == ["/constraints/0", "/objectives/0"]
    assert replay_ledger(raw, ledger) == adapted
    actual, costs = parsed(adapted)
    same(actual, z3.Int("x") >= -4)
    solver = z3.Solver()
    solver.add(costs[0] != -(z3.Int("x") + 2))
    assert solver.check() == z3.unsat


def test_goal_envelope_keeps_boolean_formula_and_span():
    raw = raw_model(op("ge", {"var": "x"}, lit(-4)))
    raw.update(decision="validity", goal=dict(op("eq", {"var": "x"}, lit(7)),
                                              span=[0, len(SOURCE)]))
    adapted, ledger = adapt_provider_forms(raw)
    assert replay_ledger(raw, ledger) == adapted
    assert ledger[-1]["path"] == "/goal"
    canonical = deepcopy(raw)
    canonical["constraints"] = [{"expr": op("ge", {"var": "x"}, lit(-4)), "span": [0, len(SOURCE)]}]
    canonical["goal"] = {"expr": op("eq", {"var": "x"}, lit(7)), "span": [0, len(SOURCE)]}
    same(parsed(adapted)[0], parsed(canonical)[0])


@pytest.mark.parametrize("entry", [
    {"op": "eq", "args": [lit(1)], "span": [0, 1]},
    {"op": "invented", "args": [lit(1)], "span": [0, 1]},
    {"op": "eq", "args": [lit(1), lit(1)]},
    {"op": "eq", "args": [lit(1), lit(1)], "span": [True, 1]},
    {"op": "eq", "args": [lit(1), lit(1)], "span": [1, 0]},
    {"op": "eq", "args": [lit(1), lit(1)], "span": [0, 1], "typo": 1},
    {"expr": lit(True, "Bool"), "op": "eq", "args": [lit(1), lit(2)], "span": [0, 1]},
    {"cp": "global_cardinality", "items": [], "values": [], "counts": [], "span": [0, 1]},
    {"cp": "all_different", "items": [], "span": [0, 1], "extra": 1},
])
def test_missing_or_conflicting_fields_are_never_filled_or_discarded(entry):
    raw = raw_model(op("eq", lit(1), lit(1)))
    raw["constraints"] = [entry]
    assert adapt_provider_forms(raw) == (raw, [])


def test_unresolved_and_bad_cp_types_remain_errors_after_rehousing():
    raw = raw_model({"cp": "all_different", "items": [lit(True, "Bool")]})
    adapted, ledger = adapt_provider_forms(raw)
    assert ledger
    with pytest.raises(ModelError):
        build_hir(adapted, SOURCE)
    raw = raw_model(op("eq", {"var": "x"}, lit(7)))
    raw["unresolved"] = ["Two source readings remain."]
    candidate = sp.propose_nl(SOURCE, language="hir", provider=lambda _: raw)
    assert not candidate.valid and candidate.model["unresolved"] == raw["unresolved"]


@pytest.mark.parametrize("sort,shape,expr,expected,actual", [
    ("Int", [1], op("mul", {"var": "x"}, {"var": "x"}), "Int or Real", "(Array Int Int)"),
    ("Int", None, op("ite", {"var": "x"}, lit(1), lit(0)), "Bool", "Int"),
    ("Bool", None, op("add", {"var": "x"}, lit(1)), "Int or Real", "Bool"),
    ("Real", None, op("not", {"var": "x"}), "Bool", "Real"),
])
def test_sort_diagnostic_reports_compiled_type_without_coercion(sort, shape, expr, expected, actual):
    builder = HirBuilder()
    builder.declare("x", sort, shape=shape)
    before = deepcopy(expr)
    with pytest.raises(ModelError) as error:
        builder.expr(expr)
    assert f"expected {expected}, got {actual}" in str(error.value)
    assert error.value.path == "model.args[0]"
    assert expr == before


def test_boolean_diagnostic_uses_lexical_operand_sort_not_global_declaration():
    builder = HirBuilder()
    builder.declare("x", "Int", shape=[1])
    expr = {"quantifier": "forall", "binders": [{"name": "x", "sort": "Int"}],
            "body": op("ite", {"var": "x"}, lit(True, "Bool"), lit(False, "Bool"))}
    with pytest.raises(ModelError) as error:
        builder.expr(expr)
    assert "expected Bool, got Int" in str(error.value)
    assert "array" not in str(error.value)


def test_repair_receives_actual_sort_and_keeps_original_candidate_unchanged():
    raw = raw_model(op("eq", op("ite", {"var": "x"}, lit(1), lit(0)), lit(1)))
    raw["constraints"] = [{"expr": {k: v for k, v in raw["constraints"][0].items() if k != "span"},
                            "span": [0, len(SOURCE)]}]
    original = deepcopy(raw)
    calls = []

    def provider(request):
        calls.append(deepcopy(request))
        if "repair" in request:
            detail, = request["repair"]["diagnostic_details"]
            assert "expected Bool, got Int" in detail["message"]
            assert detail["json_pointer"] == "/constraints/0/expr/args/0/args/0"
        return deepcopy(raw)

    trace = sp.propose_nl_with_repair(SOURCE, language="hir", provider=provider, max_attempts=2)
    assert len(trace.attempts) == 2 and all(not item.valid for item in trace.attempts)
    assert raw == original
    assert "Boolean_indicators" in hir_api()["semantics"]


def test_explicit_scalar_array_and_boolean_indicator_have_independent_relation():
    builder = HirBuilder()
    builder.declare("x", "Int")
    builder.declare("a", "Int", shape=[1], lower=0, upper=1)
    value = {"at": "a", "indices": [lit(0)]}
    builder.constrain(op("eq", {"var": "x"}, op("ite", op("eq", value, lit(1)), lit(7), lit(2))))
    translated = builder.translate()
    assert translated.ok
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2()))
    a, x = z3.Array("a", z3.IntSort(), z3.IntSort()), z3.Int("x")
    same(actual, z3.And(a[0] >= 0, a[0] <= 1, x == z3.If(a[0] == 1, 7, 2)))


@pytest.mark.parametrize("kind,body,expected", [
    ("forall", {"var": "x"}, False),
    ("exists", {"var": "x"}, True),
    ("exists_unique", {"var": "x"}, True),
])
def test_annotated_quantifier_keeps_kind_body_scope_and_complete_relation(kind, body, expected):
    expr = {"quantifier": kind, "binders": [{"name": "x", "sort": "Bool"}], "body": body}
    raw = raw_model(expr)
    # The top-level x is Int. The bound Bool x has its own lexical meaning.
    original = deepcopy(raw)
    adapted, ledger = adapt_provider_forms(raw)
    assert replay_ledger(raw, ledger) == adapted and raw == original
    assert ledger[0]["rule"] == "annotated-expression-statement"
    assert adapted["constraints"][0]["expr"] == expr
    assert adapt_provider_forms(adapted) == (adapted, [])
    actual, _ = parsed(adapted)
    projected = project_private_witnesses(actual, [d["name"] for d in adapted["declarations"]])
    same(projected, z3.BoolVal(expected))
    candidate = sp.propose_nl(SOURCE, language="hir", provider=lambda _: raw)
    assert candidate.valid, candidate.diagnostics


def test_private_witness_projection_retains_public_coordinates_and_all_constraints():
    public = z3.Bool("!somt_exists_public")
    witness = z3.Bool("!somt_exists_private")
    complete = z3.And(witness == public, witness)
    projected = project_private_witnesses(complete, [str(public.decl().name())])
    same(projected, public)
    # Forgetting the public coordinate or dropping a contradictory witness
    # assertion would incorrectly turn either relation into True.
    wrong = z3.Solver()
    wrong.add(z3.Xor(projected, z3.BoolVal(True)))
    assert wrong.check() == z3.sat
    inconsistent = z3.And(complete, z3.Not(witness))
    same(project_private_witnesses(inconsistent, [str(public.decl().name())]), z3.BoolVal(False))


@pytest.mark.parametrize("expr", [
    {"quantifier": "unknown", "binders": [{"name": "x", "sort": "Bool"}], "body": {"var": "x"}},
    {"quantifier": "forall", "binders": [], "body": lit(True, "Bool")},
    {"quantifier": "forall", "binders": [{"name": "x"}], "body": {"var": "x"}},
    {"quantifier": "forall", "binders": [{"name": "x", "sort": "Bool"}]},
    {"quantifier": "forall", "binders": [{"name": "x", "sort": "Bool"}],
     "body": {"var": "x"}, "extra": "never discard"},
])
def test_annotated_quantifier_never_fills_missing_binding_or_changes_unknown_kind(expr):
    raw = raw_model(expr)
    assert adapt_provider_forms(raw) == (raw, [])
