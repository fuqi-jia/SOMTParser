"""Exact integer index spelling for provider CP vector descriptors."""
from copy import deepcopy

import pytest
import z3

from somtparser.hir_canonical import canonicalize_hir
from somtparser.hir_cp import build_cp_hir
from somtparser._nl_model import ModelError
from test_hir_cp import model, lit, op


def row_count(prefix):
    return {"cp": "count_true", "items": {"array": "matrix", "length": 3, "prefix": prefix}}


def translated_formula(value):
    translated = build_cp_hir(value, "x").translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(translated.to_smt2()))


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_prefix_integers_keep_exact_row_relation_and_audited_changes():
    raw = model(op("eq", row_count([1]), lit(2)),
                [dict(name="matrix", sort="Bool", shape=[2, 3])])
    original = deepcopy(raw)
    with pytest.raises(ModelError, match="CP expression must be an object"):
        build_cp_hir(raw, "x")
    fixed, ledger = canonicalize_hir(raw)
    assert raw == original
    assert ledger == [dict(path="/constraints/0/expr/args/0/items/prefix/0",
                           rule="explicit-CP-prefix-integer", before=1, after=lit(1))]
    assert canonicalize_hir(fixed) == (fixed, [])
    matrix = z3.Array("matrix", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    expected = z3.Sum([z3.If(matrix[1][j], 1, 0) for j in range(3)]) == 2
    equivalent(translated_formula(fixed), expected)
    typed = deepcopy(raw)
    typed["constraints"][0]["expr"]["args"][0]["items"]["prefix"] = [lit(1)]
    equivalent(translated_formula(fixed), translated_formula(typed))


def test_mixed_symbolic_and_integer_prefix_keeps_fold_scope():
    raw = model({"fold": "forall", "var": "i", "range": [0, 2],
                 "body": op("eq", row_count([{"var": "i"}, 1]), lit(2))},
                [dict(name="matrix", sort="Bool", shape=[2, 2, 3])])
    fixed, ledger = canonicalize_hir(raw)
    assert len(ledger) == 1 and ledger[0]["path"].endswith("/prefix/1")
    assert fixed["constraints"][0]["expr"]["body"]["args"][0]["items"]["prefix"][0] == {"var": "i"}
    matrix = z3.Array("matrix", z3.IntSort(),
                      z3.ArraySort(z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort())))
    expected = z3.And(*[z3.Sum([z3.If(matrix[i][1][j], 1, 0) for j in range(3)]) == 2
                        for i in range(2)])
    equivalent(translated_formula(fixed), expected)


@pytest.mark.parametrize("value", [True, False, 1.0, "1", "01", None])
def test_other_untyped_prefix_values_are_not_guessed(value):
    raw = model(op("eq", row_count([value]), lit(2)),
                [dict(name="matrix", sort="Bool", shape=[2, 3])])
    fixed, ledger = canonicalize_hir(raw)
    assert fixed == raw and ledger == []
    with pytest.raises(ModelError):
        build_cp_hir(fixed, "x")


@pytest.mark.parametrize("value", [-1, 2**100])
def test_no_clipping_rounding_or_domain_change(value):
    raw = model(op("eq", row_count([value]), lit(2)),
                [dict(name="matrix", sort="Bool", shape=[2, 3])])
    fixed, ledger = canonicalize_hir(raw)
    assert fixed["constraints"][0]["expr"]["args"][0]["items"]["prefix"] == [lit(value)]
    assert fixed["declarations"] == raw["declarations"]
    assert len(ledger) == 1 and ledger[0]["before"] == value


def test_nonvector_shapes_and_model_data_are_unchanged():
    raw = model(op("eq", row_count([1]), lit(2)),
                [dict(name="matrix", sort="Bool", shape=[2, 3])])
    raw["constraints"][0]["expr"]["args"][0]["items"]["extra"] = 0
    raw["data"] = {"prefix": [1, 0], "matrix": [[True, False]]}
    fixed, ledger = canonicalize_hir(raw)
    assert fixed == raw and ledger == []


def test_integer_condition_stays_integer_and_is_rejected():
    raw = model(op("eq", op("ite", {"var": "bit"}, lit(1), lit(0)), lit(1)),
                [dict(name="bit", sort="Int", lower=0, upper=1)])
    fixed, ledger = canonicalize_hir(raw)
    assert fixed == raw and ledger == []
    with pytest.raises(ModelError, match="ite condition must have sort Bool"):
        build_cp_hir(fixed, "x")
