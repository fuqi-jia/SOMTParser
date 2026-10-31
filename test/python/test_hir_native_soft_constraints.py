"""Native weighted HIR: exact feasible relation and complete cost vector."""
from itertools import product

import pytest
import z3

from somtparser import _somtparser as native


def op(name, *args):
    return native._hir_op(name, list(args))


def integer(value):
    return native._hir_literal(native.HirSort.integer(), str(value))


def boolean(value):
    return native._hir_literal(native.HirSort.boolean(), "true" if value else "false")


def compile_model(model, profile="default"):
    translation = model.translate(profile=profile, dialect=native.OmtDialect.Z3)
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    text = translation.to_smt2(native.OmtDialect.Z3)
    optimizer = z3.Optimize()
    optimizer.from_string(text)
    return translation, optimizer, text


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def exact_vector(optimizer, hard, costs):
    equivalent(z3.And(*optimizer.assertions()), hard)
    actual = optimizer.objectives()
    assert len(actual) == len(costs)
    # Complete pointwise expression equality, including infeasible assignments:
    # neither matching optima nor a successful SMT parse suffices here.
    for expression, expected in zip(actual, costs):
        solver = z3.Solver()
        solver.add(expression != expected)
        assert solver.check() == z3.unsat


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_exact_large_weight_duplicates_and_unsplit_conjunction(profile):
    model = native.HirModel()
    p = model.declare("p", native.HirSort.boolean())
    q = model.declare("q", native.HirSort.boolean())
    model.constrain(op("or", p, q))
    weight = 10**90 + 9007199254740993
    model.soft_constrain(p, str(weight), source_path="preferences[0]")
    model.soft_constrain(p, "0007")
    model.soft_constrain(op("and", p, q), "11")
    model.soft_constrain(boolean(False), "13")
    model.soft_constrain(boolean(True), "17")
    translation, optimizer, text = compile_model(model, profile)
    zp, zq = z3.Bools("p q")
    cost = (weight + 7) * z3.If(zp, 0, 1) + 11 * z3.If(z3.And(zp, zq), 0, 1) + 13
    exact_vector(optimizer, z3.Or(zp, zq), [cost])
    assert translation.report.stats.num_objectives == 1
    assert str(weight) in text and "assert-soft" in text
    assert len(translation.parser.soft_assertions) == 5
    assert translation.report.fidelity.preserves_optimum
    for p_value, q_value in product([False, True], repeat=2):
        solver = z3.Solver()
        solver.add(*optimizer.assertions(), zp == p_value, zq == q_value)
        assert solver.check() == (z3.sat if p_value or q_value else z3.unsat)


def test_groups_require_explicit_combination_and_follow_first_appearance():
    model = native.HirModel()
    p = model.declare("p", native.HirSort.boolean())
    model.soft_constrain(p, "1", group="z_first")
    model.soft_constrain(op("not", p), "100", group="a_second")
    assert any("no combination" in d.message for d in model.validate())
    assert not model.translate().ok
    model.objective_order("lexicographic")
    translation, optimizer, text = compile_model(model)
    zp = z3.Bool("p")
    exact_vector(optimizer, z3.BoolVal(True), [z3.If(zp, 0, 1), z3.If(zp, 100, 0)])
    assert translation.report.stats.num_objectives == 2
    assert ":opt.priority lex" in text
    assert optimizer.check() == z3.sat
    assert z3.is_true(optimizer.model().eval(zp))


def test_quoted_group_identity_and_default_group_are_preserved():
    model = native.HirModel()
    p = model.declare("p", native.HirSort.boolean())
    model.soft_constrain(p, "2", group="named")
    model.soft_constrain(p, "3", group="|named|")
    model.soft_constrain(op("not", p), "7", group="|cost with spaces|")
    model.soft_constrain(p, "11")
    model.objective_order("lexicographic")
    translation, optimizer, _ = compile_model(model)
    zp = z3.Bool("p")
    exact_vector(optimizer, z3.BoolVal(True),
                 [z3.If(zp, 0, 5), z3.If(zp, 7, 0), z3.If(zp, 0, 11)])
    assert translation.report.stats.num_objectives == 3


@pytest.mark.parametrize("maximize", [False, True])
def test_mixed_objective_cost_order_is_soft_groups_then_explicit(maximize):
    model = native.HirModel()
    p = model.declare("p", native.HirSort.boolean())
    x = model.declare("x", native.HirSort.integer())
    # Calling objective first must not imply command interleaving. The native
    # container's documented order is soft groups, then arithmetic objectives.
    model.objective(maximize, x)
    model.constrain(op("and", op("ge", x, integer(0)), op("le", x, integer(2))))
    model.constrain(op("eq", p, op("eq", x, integer(0))))
    model.soft_constrain(p, "19")
    assert not model.translate().ok
    model.objective_order("lexicographic")
    translation, optimizer, text = compile_model(model)
    zp, zx = z3.Bool("p"), z3.Int("x")
    exact_vector(optimizer, z3.And(zx >= 0, zx <= 2, zp == (zx == 0)),
                 [z3.If(zp, 0, 19), -zx if maximize else zx])
    assert translation.report.stats.num_objectives == 2
    assert text.index("assert-soft") < text.index("(maximize" if maximize else "(minimize")
    assert optimizer.check() == z3.sat
    assert optimizer.model().eval(zx).as_long() == 0


def test_single_group_rejects_redundant_combination_and_snapshot_is_immutable():
    model = native.HirModel()
    p = model.declare("p", native.HirSort.boolean())
    model.soft_constrain(p, "3")
    first, _, first_text = compile_model(model)
    model.objective_order("lexicographic")
    assert not model.translate().ok
    model.objective_order("single")
    model.soft_constrain(op("not", p), "5")
    _, optimizer, _ = compile_model(model)
    exact_vector(optimizer, z3.BoolVal(True), [z3.If(z3.Bool("p"), 5, 3)])
    assert first.to_smt2(native.OmtDialect.Z3) == first_text


@pytest.mark.parametrize("weight", ["", "0", "000", "-1", "+1", "1.0", "1/2",
                                    "1e2", " 1", "1 ", "1\n", "nan", "inf", "1) (assert false)"])
def test_invalid_exact_weight_is_rejected_without_mutation(weight):
    model = native.HirModel()
    with pytest.raises(ValueError, match="positive integer"):
        model.soft_constrain(boolean(True), weight, source_path="invalid.weight")
    translation, optimizer, _ = compile_model(model)
    assert translation.report.stats.num_objectives == 0
    exact_vector(optimizer, z3.BoolVal(True), [])


@pytest.mark.parametrize("weight", [1, 1.0, True, None, b"1"])
def test_weight_must_be_string(weight):
    with pytest.raises(TypeError):
        native.HirModel().soft_constrain(boolean(True), weight)


@pytest.mark.parametrize("group", ["bad group", "1abc", "|unfinished", "a|b", "|a\\b|",
                                   "||", "|a\n|", "a) (assert false)", "let", "_"])
def test_invalid_group_is_rejected(group):
    with pytest.raises(ValueError, match="group"):
        native.HirModel().soft_constrain(boolean(True), "1", group=group)


@pytest.mark.parametrize("group", [1, None, b"a"])
def test_group_must_be_string(group):
    with pytest.raises(TypeError):
        native.HirModel().soft_constrain(boolean(True), "1", group=group)


def test_soft_formula_must_be_boolean():
    with pytest.raises(ValueError, match="Bool"):
        native.HirModel().soft_constrain(integer(1), "1")


def test_soft_constraint_source_path_reaches_native_type_diagnostic():
    foreign = native.HirModel().declare("missing", native.HirSort.boolean())
    model = native.HirModel()
    model.soft_constrain(foreign, "7", source_path="soft_constraints[3].expr")
    diagnostics = model.validate()
    assert diagnostics
    assert any(d.file == "soft_constraints[3].expr" for d in diagnostics)
    assert not model.translate().ok


def test_grouped_soft_feasibility_dialect_is_an_explicit_diagnostic():
    model = native.HirModel()
    model.soft_constrain(boolean(True), "1", group="a")
    model.soft_constrain(boolean(False), "1", group="b")
    model.objective_order("lexicographic")
    result = model.translate(profile="feasibility", dialect=native.OmtDialect.NONE)
    assert not result.ok
    assert any("combined soft groups" in d.message for d in result.diagnostic_items)


def test_grouped_soft_gomt_uses_named_objectives_and_retains_the_exact_cost_vector():
    model = native.HirModel()
    p = model.declare("p", native.HirSort.boolean())
    model.soft_constrain(p, "1", group="a")
    model.soft_constrain(op("not", p), "3", group="b")
    model.objective_order("lexicographic")
    result = model.translate(dialect=native.OmtDialect.SmtLib2025)
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2(native.OmtDialect.SmtLib2025)
    assert text.count("(define-maxsmt-objective ") == 2
    assert text.count(":objective ") == 2
    assert ":id " not in text
    assert text.count("(optimize-sat ") == 1
    assert "(check-sat)" not in text
    assert "OBJECTIVE_LEX" in text
    optimizer = z3.Optimize()
    optimizer.from_string(native.parse(text).dump_smt2(native.OmtDialect.Z3))
    zp = z3.Bool("p")
    exact_vector(optimizer, z3.BoolVal(True), [z3.If(zp, 0, 1), z3.If(zp, 3, 0)])
    assert optimizer.check() == z3.sat
    assert z3.is_true(optimizer.model().eval(zp))


@pytest.mark.parametrize("mutation", ["dropped_duplicate", "hardened_soft", "merged_groups", "reversed_groups"])
def test_independent_cost_oracle_detects_bad_relations(mutation):
    p, q = z3.Bools("p q")
    if mutation == "hardened_soft":
        solver = z3.Solver()
        solver.add(z3.Xor(z3.BoolVal(True), p))
    else:
        expected = [z3.If(p, 0, 5), z3.If(q, 0, 7)]
        actual = {"dropped_duplicate": [z3.If(p, 0, 2), expected[1]],
                  "merged_groups": [expected[0] + expected[1], z3.IntVal(0)],
                  "reversed_groups": list(reversed(expected))}[mutation]
        solver = z3.Solver()
        solver.add(z3.Or(*[left != right for left, right in zip(actual, expected)]))
    assert solver.check() == z3.sat
