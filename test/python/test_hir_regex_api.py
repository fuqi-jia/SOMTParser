"""Regex HIR semantics checked against an independent finite-language oracle."""
from itertools import product

import pytest
import z3

from somtparser.hir import HirBuilder, ModelError, hir_api


def lit(value, sort="String"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def indexed(name, indices, *args):
    return {"op_indexed": {"op": name, "indices": indices, "args": list(args)}}


def check_word(regex_expr, word, expected):
    b = HirBuilder()
    b.constrain(op("str.in_re", lit(word), regex_expr))
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.And(*z3.parse_smt2_string(translated.to_smt2())))
    result = solver.check()
    assert result == (z3.sat if expected else z3.unsat)


def universe(alphabet, max_length):
    return {
        "".join(chars)
        for length in range(max_length + 1)
        for chars in product(alphabet, repeat=length)
    }


def concat(left, right, limit):
    return {a + b for a in left for b in right if len(a) + len(b) <= limit}


def closure(base, limit, minimum=0, maximum=None):
    maximum = limit if maximum is None else min(maximum, limit)
    result = set()
    frontier = {""}
    if minimum == 0:
        result.add("")
    for count in range(1, maximum + 1):
        frontier = concat(frontier, base, limit)
        if count >= minimum:
            result |= frontier
    return result


@pytest.mark.parametrize("word", ["", "a", "b", "ab", "bb", "c"])
def test_native_reglan_constants(word):
    check_word(lit("re.none", "RegLan"), word, False)
    check_word(lit("re.all", "RegLan"), word, True)
    check_word(lit("re.allchar", "RegLan"), word, len(word) == 1)


def test_regex_constructors_match_independent_bounded_language_oracle():
    words = universe("ab", 3)
    a = op("str.to_re", lit("a"))
    b = op("str.to_re", lit("b"))
    char_ab = op("re.range", lit("a"), lit("b"))
    cases = [
        (op("re.union", a, b), {"a", "b"}),
        (op("re.inter", char_ab, op("re.union", a, b)), {"a", "b"}),
        (op("re.diff", char_ab, a), {"b"}),
        (op("re.++", a, b), {"ab"}),
        (op("re.*", char_ab), closure({"a", "b"}, 3)),
        (op("re.+", a), closure({"a"}, 3, minimum=1)),
        (op("re.opt", a), {"", "a"}),
        (op("re.comp", a), words - {"a"}),
        (op("re.range", lit(""), lit("z")), set()),
        (op("re.range", lit("ab"), lit("z")), set()),
        (op("re.range", lit("z"), lit("a")), set()),
        (indexed("re.loop", [0, 0], char_ab), {""}),
        (indexed("re.loop", [0, 1], char_ab), {"", "a", "b"}),
        (indexed("re.loop", [1, 2], char_ab), {"a", "b", "aa", "ab", "ba", "bb"}),
        (indexed("re.loop", [2, 1], char_ab), set()),
        (indexed("re.loop", [0, 0], lit("re.none", "RegLan")), {""}),
        (indexed("re.loop", [1, 2], lit("re.none", "RegLan")), set()),
        (indexed("re.loop", [2, 2], op("str.to_re", lit(""))), {""}),
    ]
    for regex_expr, accepted in cases:
        for word in sorted(words):
            check_word(regex_expr, word, word in accepted)


def test_regex_sort_and_catalog_are_exposed():
    b = HirBuilder()
    b.declare("r", "RegLan")
    assert repr(b.symbols["r"].sort) == "RegLan"
    api = hir_api()
    assert "RegLan" in api["sorts"]
    assert api["operations"]["str.in_re"] == [2, 2]
    assert api["indexed_operations"]["re.loop"] == [2, 1]


@pytest.mark.parametrize(
    "expr",
    [
        op("str.to_re", lit(1, "Int")),
        op("str.in_re", lit("a"), lit("re.all", "String")),
        op("re.union", lit("re.all", "RegLan"), lit("re.all", "String")),
        op("re.diff", lit("re.all", "RegLan")),
        indexed("re.loop", [1], lit("re.all", "RegLan")),
        indexed("re.loop", [0, 2**32], lit("re.all", "RegLan")),
    ],
)
def test_malformed_regex_shapes_are_refused(expr):
    with pytest.raises((ModelError, ValueError)):
        HirBuilder().expr(expr)


@pytest.mark.parametrize("bound", [2**31, 2**32 - 1])
def test_re_loop_preserves_full_unsigned_indices_in_smt(bound):
    b = HirBuilder()
    b.constrain(
        op(
            "str.in_re",
            lit(""),
            indexed("re.loop", [bound, bound], lit("re.allchar", "RegLan")),
        )
    )
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert f"((_ re.loop {bound} {bound})" in translated.to_smt2()


@pytest.mark.parametrize("word", ["", "a", "b", "ab"])
def test_re_range_accepts_symbolic_endpoints(word):
    b = HirBuilder()
    b.declare("lo", "String")
    b.declare("hi", "String")
    b.constrain(op("eq", {"var": "lo"}, lit("a")))
    b.constrain(op("eq", {"var": "hi"}, lit("b")))
    b.constrain(op("str.in_re", lit(word), op("re.range", {"var": "lo"}, {"var": "hi"})))
    translated = b.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.And(*z3.parse_smt2_string(translated.to_smt2())))
    expected = len(word) == 1 and word in {"a", "b"}
    result = solver.check()
    assert result == (z3.sat if expected else z3.unsat)


@pytest.mark.parametrize("word", ["é", "😀"])
def test_unicode_membership_is_not_folded_as_bytes(word):
    check_word(lit("re.allchar", "RegLan"), word, True)
    check_word(op("re.++", lit("re.allchar", "RegLan"),
                  lit("re.allchar", "RegLan")), word, False)
    check_word(op("re.range", lit(word), lit(word)), word, True)
