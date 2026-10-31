"""Finite-set export through the public HIR and Translation APIs."""
import pytest
import z3

import somtparser as sp
from somtparser.hir import HirBuilder
from somtparser._solving import FidelityError, Formula


def var(name):
    return {"var": name}


def lit(value, sort):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def set_int(values):
    result = lit("set.empty", {"Set": "Int"})
    for value in sorted(values):
        result = op("set.insert", lit(value, "Int"), result)
    return result


def quantified_carrier(element_name, set_expr):
    x = var(element_name)
    inside = op("set.member", x, set_expr)
    bounded = op("and", op("ge", x, lit(0, "Int")),
                 op("le", x, lit(2, "Int")))
    return {"quantifier": "forall", "binders": [{"name": element_name, "sort": "Int"}],
            "body": op("implies", inside, bounded)}


def solver_for(script):
    solver = z3.Solver()
    solver.from_string(script)
    return solver


@pytest.mark.parametrize("name", [
    "set-logic", "declare-const", "declare-fun", "define-fun",
    "define-fun-rec", "define-funs-rec", "define-sort",
    "declare-datatype", "declare-datatypes", "declare-codatatypes",
])
def test_quoted_command_names_survive_public_export(name):
    source = (
        f"(set-logic ALL)(declare-fun |{name}| (Int) Bool)"
        "(declare-const S (Set Int))"
        "(assert (= S (set.singleton 0)))"
        f"(assert (|{name}| 1))(check-sat)"
    )
    translated = sp.translate(source=source, language="smtlib2", dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    lowered = translated.to_smt2(sp.OmtDialect.Z3)
    solver = solver_for(lowered)
    assert solver.check() == z3.sat
    predicate = z3.Function(name, z3.IntSort(), z3.BoolSort())
    solver.add(z3.Not(predicate(1)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("claimed,expected", [(1, z3.sat), (0, z3.unsat)])
def test_simultaneous_let_support_does_not_capture_shadowed_scalar(claimed, expected):
    source = (
        "(declare-const x Int)(assert (= x 0))"
        "(assert (let ((x 9) (S (set.singleton x))) "
        f"(= (set.card S) {claimed})))"
    )
    translated = sp.translate(source=source, language="smtlib2")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert solver_for(translated.to_smt2(sp.OmtDialect.Z3)).check() == expected


def model_with_set_and_card(values, claimed_card):
    builder = HirBuilder()
    builder.declare("S", {"Set": "Int"})
    builder.constrain(op("eq", var("S"), set_int(values)))
    builder.constrain(quantified_carrier("u", var("S")))
    builder.constrain(op("eq", op("set.card", var("S")), lit(claimed_card, "Int")))
    return builder


def test_public_translation_exhausts_all_subsets_of_three_element_carrier():
    # Compare the complete public exporter against all 8 finite interpretations,
    # testing both the true cardinality and an adjacent false cardinality.
    for mask in range(8):
        values = {i for i in range(3) if mask & (1 << i)}
        good = model_with_set_and_card(values, len(values)).translate(dialect=sp.OmtDialect.Z3)
        assert good.ok, [d.message for d in good.diagnostic_items]
        lowered = good.to_smt2(sp.OmtDialect.Z3)
        assert "(Set Int)" not in lowered
        assert "set.card" not in lowered and "set.member" not in lowered
        assert "(Array Int Bool)" in lowered
        assert solver_for(lowered).check() == z3.sat

        wrong_size = (len(values) + 1) % 4
        bad = model_with_set_and_card(values, wrong_size).translate(dialect=sp.OmtDialect.Z3)
        assert bad.ok, [d.message for d in bad.diagnostic_items]
        assert solver_for(bad.to_smt2(sp.OmtDialect.Z3)).check() == z3.unsat


def test_dynamic_set_array_index_uses_cell_carriers_and_keeps_index_semantics():
    builder = HirBuilder()
    builder.declare("A", {"Array": ["Int", {"Set": "Int"}]})
    builder.declare("i", "Int")
    builder.constrain(op("ge", var("i"), lit(0, "Int")))
    builder.constrain(op("le", var("i"), lit(1, "Int")))
    for index in (0, 1):
        selected = op("select", var("A"), lit(index, "Int"))
        builder.constrain(quantified_carrier(f"u{index}", selected))
    cell0 = op("select", var("A"), lit(0, "Int"))
    cell1 = op("select", var("A"), lit(1, "Int"))
    builder.constrain(op("eq", cell0, set_int({0, 1})))
    builder.constrain(op("eq", cell1, set_int({2})))
    dynamic = op("select", var("A"), var("i"))
    builder.constrain(op("eq", op("set.card", dynamic), lit(1, "Int")))

    translated = builder.translate(dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    text = translated.to_smt2(sp.OmtDialect.Z3)
    assert "set.card" not in text and "set.member" not in text
    assert "(Array Int (Array Int Bool))" in text
    solver = solver_for(text)
    i = z3.Int("i")
    assert solver.check() == z3.sat
    solver.push(); solver.add(i == 0)
    assert solver.check() == z3.unsat
    solver.pop(); solver.push(); solver.add(i == 1)
    assert solver.check() == z3.sat
    solver.pop()


def test_native_smtlib2025_set_dialect_is_not_rewritten():
    translated = model_with_set_and_card({0, 2}, 2).translate(
        dialect=sp.OmtDialect.SmtLib2025)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    native_sets = translated.to_smt2(sp.OmtDialect.SmtLib2025)
    assert "(Set Int)" in native_sets
    assert "set.card" in native_sets and "set.member" in native_sets
    # The Z3 representation rewrite is selected by the requested dialect only.
    z3_text = translated.to_smt2(sp.OmtDialect.Z3)
    assert "(Set Int)" not in z3_text and "set.card" not in z3_text


def test_formula_z3_solver_accepts_proved_finite_carrier():
    translated = model_with_set_and_card({0, 2}, 2).translate()
    result = Formula(translated, "hir", backend="z3", timeout=10).solve()
    assert result.status == "sat"
    assert result.semantic_mode == "z3-finite-set-arrays"
    assert "--sets-exp" not in result.backend_options


def test_formula_z3_refuses_infinite_set_before_invoking_solver(monkeypatch):
    from somtparser import _solving

    builder = HirBuilder()
    builder.declare("S", {"Set": "Int"})
    builder.constrain({"quantifier": "forall", "binders": [{"name": "u", "sort": "Int"}],
                       "body": op("set.member", var("u"), var("S"))})
    translated = builder.translate()
    assert translated.ok
    monkeypatch.setattr(_solving._backends, "run",
                        lambda *a, **k: pytest.fail("unsupported encoding reached the solver"))
    with pytest.raises(FidelityError, match="unbounded carriers"):
        Formula(translated, "hir", backend="z3", timeout=10).solve()


def test_nested_cardinality_in_singleton_element_is_lowered_recursively():
    builder = model_with_set_and_card({0, 2}, 2)
    singleton = op("set.singleton", op("set.card", var("S")))
    builder.constrain(op("ne", op("set.card", singleton), lit(1, "Int")))
    translated = builder.translate()
    assert translated.ok
    script = translated.to_smt2(sp.OmtDialect.Z3)
    assert "set.card" not in script
    assert solver_for(script).check() == z3.unsat


def test_noninteger_implicit_set_sort_is_checked_before_z3_export():
    # Neither a Set declaration nor a Set literal spells out the sort here.
    # The exporter must inspect the typed singleton result, not guess Int.
    builder = HirBuilder()
    builder.constrain(op("eq", op("set.singleton", lit(True, "Bool")),
                         op("set.singleton", lit(False, "Bool"))))
    translated = builder.translate()
    assert translated.ok
    assert translated.set_solver_requirements.non_integer_carrier
    with pytest.raises(RuntimeError, match="requires Set Int"):
        translated.to_smt2(sp.OmtDialect.Z3)
    assert "set.singleton" in translated.to_smt2(sp.OmtDialect.SmtLib2025)


def test_finite_set_operators_and_cardinality_agree_with_python_sets():
    # Fully fix both inputs, then refute the conjunction of every expected
    # result. All 64 pairs cover empty, overlapping, equal and disjoint sets.
    for left_mask in range(8):
        for right_mask in range(8):
            left = {i for i in range(3) if left_mask & (1 << i)}
            right = {i for i in range(3) if right_mask & (1 << i)}
            a, b = set_int(left), set_int(right)
            terms = [(op("set.union", a, b), left | right),
                     (op("set.inter", a, b), left & right),
                     (op("set.minus", a, b), left - right),
                     (op("set.insert", lit(1, "Int"), a), left | {1})]
            claims = [op("eq", op("set.subset", a, b), lit(left <= right, "Bool"))]
            for term, expected in terms:
                claims.append(op("eq", term, set_int(expected)))
                claims.append(op("eq", op("set.card", term), lit(len(expected), "Int")))
            builder = HirBuilder()
            builder.constrain(op("not", op("and", *claims)))
            translated = builder.translate()
            assert translated.ok, [d.message for d in translated.diagnostic_items]
            assert solver_for(translated.to_smt2(sp.OmtDialect.Z3)).check() == z3.unsat, (left, right)
