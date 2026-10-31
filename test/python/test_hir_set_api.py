"""Set API checked against cvc5 and exhaustive finite Python set oracles."""
import shutil
import subprocess

import pytest

from somtparser import OmtDialect
from somtparser.hir import HirBuilder, ModelError, hir_api


def var(name):
    return {"var": name}


def lit(value, sort):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def set_sort(element_sort):
    return {"Set": element_sort}


def set_value(elements, element_sort="Bool"):
    result = lit("set.empty", set_sort(element_sort))
    for element in sorted(elements):
        result = op("set.insert", lit(element, element_sort), result)
    return result


def cvc5_status(script):
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for an independent finite-set oracle")
    if "(check-sat)" not in script:
        script += "\n(check-sat)\n"
    if "(set-option :sets-exp true)" not in script:
        lines = script.splitlines()
        for i, line in enumerate(lines):
            if line.startswith("(set-logic "):
                lines.insert(i + 1, "(set-option :sets-exp true)")
                break
        else:
            lines.insert(0, "(set-option :sets-exp true)")
        script = "\n".join(lines) + "\n"
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


def compiled_status(builder):
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2(OmtDialect.SmtLib2025)
    return cvc5_status(script)


def make_claim_model(left, right, negative=False):
    b = HirBuilder()
    b.declare("S", set_sort("Bool"))
    b.declare("T", set_sort("Bool"))
    # These are the only base facts: they choose the oracle assignment.
    b.constrain(op("eq", var("S"), set_value(left)))
    b.constrain(op("eq", var("T"), set_value(right)))

    union = op("set.union", var("S"), var("T"), set_value({False}))
    inter = op("set.inter", var("S"), var("T"), set_value({False, True}))
    minus = op("set.minus", var("S"), var("T"))
    insert = op("set.insert", lit(False, "Bool"), lit(True, "Bool"), var("S"))
    expected = [
        (union, left | right | {False}),
        (inter, left & right),
        (minus, left - right),
        (insert, left | {False, True}),
    ]
    claims = []
    for expression, values in expected:
        claims.append(op("eq", expression, set_value(values)))
        claims.append(op("eq", op("set.card", expression), lit(len(values), "Int")))
        for item in (False, True):
            claims.append(
                op("eq", op("set.member", lit(item, "Bool"), expression),
                   lit(item in values, "Bool"))
            )
    claims.extend(
        [
            op("eq", op("set.subset", var("S"), var("T")), lit(left <= right, "Bool")),
            op("eq", op("set.subset", var("T"), var("S")), lit(right <= left, "Bool")),
            op("eq", op("set.card", var("S")), lit(len(left), "Int")),
            op("eq", op("set.card", var("T")), lit(len(right), "Int")),
            op("eq", op("set.singleton", lit(True, "Bool")), set_value({True})),
        ]
    )
    relation = op("and", *claims)
    b.constrain(op("not", relation) if negative else relation)
    return b


def test_set_catalog_nested_sorts_and_open_int_translation():
    api = hir_api()
    assert {"Set": "element sort"} in api["sorts"]
    assert api["operations"]["set.member"] == [2, 2]
    assert api["operations"]["set.insert"] == [2, 10000]
    assert "set.is_empty" not in api["operations"]

    b = HirBuilder()
    b.declare("s", set_sort("Int"))
    b.declare("x", "Int")
    b.constrain(op("set.member", var("x"), var("s")))
    nested = set_sort(set_sort("Int"))
    b.declare("ss", nested)
    b.constrain(
        op(
            "eq",
            var("ss"),
            op("set.singleton", op("set.singleton", lit(3, "Int"))),
        )
    )
    result = b.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert "(Set Int)" in result.to_smt2(OmtDialect.SmtLib2025)
    assert "(Set (Set Int))" in result.to_smt2(OmtDialect.SmtLib2025)


def test_all_bool_set_pairs_match_exhaustive_python_oracle():
    subsets = [set(), {False}, {True}, {False, True}]
    for left in subsets:
        for right in subsets:
            # Positive expected relation is SAT; its negation under only the
            # base input-set equalities is UNSAT.
            positive = make_claim_model(left, right)
            negative = make_claim_model(left, right, negative=True)
            assert compiled_status(positive) == "sat"
            assert compiled_status(negative) == "unsat"


def test_empty_and_universe_literals_and_finite_bool_complement_oracle():
    for values in (set(), {False}, {True}, {False, True}):
        b = HirBuilder()
        b.declare("S", set_sort("Bool"))
        b.declare("U", set_sort("Bool"))
        # The finite oracle explicitly makes both Bool values members of the
        # cvc5 input-active universe; no production Int carrier is inferred.
        b.constrain(op("eq", var("S"), set_value(values)))
        b.constrain(op("eq", var("U"), lit("set.universe", set_sort("Bool"))))
        b.constrain(op("set.member", lit(False, "Bool"), var("U")))
        b.constrain(op("set.member", lit(True, "Bool"), var("U")))
        expected = {False, True} - values
        claim = op(
            "eq",
            op("set.complement", var("S")),
            set_value(expected),
        )
        b.constrain(claim)
        positive = b
        assert compiled_status(positive) == "sat"

        b_negative = HirBuilder()
        b_negative.declare("S", set_sort("Bool"))
        b_negative.declare("U", set_sort("Bool"))
        b_negative.constrain(op("eq", var("S"), set_value(values)))
        b_negative.constrain(op("eq", var("U"), lit("set.universe", set_sort("Bool"))))
        b_negative.constrain(op("set.member", lit(False, "Bool"), var("U")))
        b_negative.constrain(op("set.member", lit(True, "Bool"), var("U")))
        b_negative.constrain(op("not", claim))
        assert compiled_status(b_negative) == "unsat"


@pytest.mark.parametrize(
    "expression",
    [
        op("set.member", lit(True, "Bool"), var("ints")),
        op("set.union", var("bools"), var("ints")),
        op("set.insert", lit(True, "Bool"), var("ints")),
        op("set.card", lit(1, "Int")),
        op("set.minus", var("ints")),
        op("set.singleton"),
        op("set.union", var("bools")),
        op("set.insert", lit(True, "Bool")),
        op("set.member", lit(True, "Bool")),
    ],
)
def test_wrong_set_sorts_and_arities_refuse_before_native_builder(expression):
    b = HirBuilder()
    b.declare("ints", set_sort("Int"))
    b.declare("bools", set_sort("Bool"))
    with pytest.raises((ModelError, ValueError)):
        b.expr(expression)


@pytest.mark.parametrize(
    "expression",
    [
        lit("set.empty", "Int"),
        lit("set.universe", {"Set": "Bool", "extra": 1}),
        lit("set.all", set_sort("Bool")),
    ],
)
def test_set_constants_require_exact_tag_and_set_sort(expression):
    with pytest.raises((ModelError, ValueError)):
        HirBuilder().expr(expression)
