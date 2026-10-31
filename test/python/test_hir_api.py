"""Native HIR construction checked against independent solver formulas."""
from copy import deepcopy

import pytest
import z3
from somtparser.hir import HirBuilder, ModelError, hir_api, hir_schema
from somtparser.hir_canonical import canonicalize_hir
from somtparser import propose_nl, compile_candidate


def lit(n, sort="Int"):
    return {"literal": n, "sort": sort}


def bv(text, width):
    return {"literal": text, "sort": {"BitVec": width}}


def fp(value, eb=8, sb=24):
    return {"literal": value, "sort": {"FloatingPoint": [eb, sb]}}


def string(text):
    return {"literal": text, "sort": "String"}


def rm(mode="RNE"):
    return {"rm": mode}


def var(n):
    return {"var": n}


def op(n, *args):
    return {"op": n, "args": list(args)}


def indexed(n, indices, *args):
    return {"op_indexed": {"op": n, "indices": indices, "args": list(args)}}


def relation(builder):
    t = builder.translate()
    assert t.ok, [d.message for d in t.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(t.to_smt2()))


def same(actual, expected):
    s = z3.Solver()
    s.add(z3.Xor(actual, expected))
    assert s.check() == z3.unsat


def test_integer_bounds_and_direct_provenance():
    b = HirBuilder()
    b.declare("x", "Int", -5, 8)
    b.constrain(op("ge", var("x"), lit(3)))
    x = z3.Int("x")
    same(relation(b), z3.And(x >= -5, x <= 8, x >= 3))
    assert b.translate().report.provenance.language_id == "hir"


def test_exact_rationals():
    b = HirBuilder()
    b.declare("x", "Real")
    b.constrain(op("eq", var("x"), lit("-1/3", "Real")))
    same(relation(b), z3.Real("x") == z3.RealVal("-1/3"))


def test_mathematical_operator_aliases_normalize_without_mutating_input():
    b = HirBuilder()
    b.declare("x", "Int")
    b.declare("y", "Int")
    expression = {
        "op": "=",
        "args": [
            {"op": "+", "args": [var("x"), lit(2)]},
            var("y"),
        ],
    }
    before = deepcopy(expression)
    b.constrain(expression)
    b.constrain({"op": "=>", "args": [
        {"op": "≤", "args": [var("x"), var("y")]},
        {"op": "≠", "args": [var("x"), var("y")]},
    ]})
    x, y = z3.Int("x"), z3.Int("y")
    same(relation(b), z3.And(x + 2 == y, z3.Implies(x <= y, x != y)))
    assert expression == before
    aliases = hir_api()["operator_aliases"]
    assert aliases["+"] == "add" and aliases["≤"] == "le"

    # Aliases in comparison guards must grant exactly the same local
    # nonzero fact as their canonical spellings.
    guarded = HirBuilder()
    guarded.declare("x", "Int")
    guarded.constrain({"op": "=>", "args": [
        {"op": ">", "args": [var("x"), lit(0)]},
        {"op": "eq", "args": [op("div", lit(1), var("x")), lit(0)]},
    ]})
    x = z3.Int("x")
    same(relation(guarded), z3.Implies(x > 0, z3.ToReal(z3.IntVal(1)) / z3.ToReal(x) == 0))


def test_absolute_value_is_exact_for_int_real_and_compact_cp_form():
    raw = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability", "declarations": [], "functions": [],
        "constraints": [{"expr": {"op": "abs", "args": [var("x")]},
                         "span": [0, 1]}],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    canonical, _ = canonicalize_hir(raw)
    assert canonical["constraints"][0]["expr"]["op"] == "abs"

    for sort, samples in [("Int", [-4, 0, 4]), ("Real", ["-3/2", "0", "3/2"])]:
        for value in samples:
            expected_value = abs(value) if sort == "Int" else (
                "3/2" if value.startswith("-") else value
            )
            b = HirBuilder()
            b.declare("x", sort)
            b.constrain(op("eq", var("x"), lit(value, sort)))
            b.constrain(op("eq", {"op": "abs", "args": [var("x")]},
                           lit(expected_value, sort)))
            x = z3.Int("x") if sort == "Int" else z3.Real("x")
            expected = z3.And(x == value, z3.Abs(x) == expected_value)
            same(relation(b), expected)

    b = HirBuilder()
    b.declare("x", "Int")
    b.constrain({"op": "eq", "args": [
        {"cp": {"abs": {"op": "sub", "args": [var("x"), lit(3)]}}},
        lit(2),
    ]})
    x = z3.Int("x")
    same(relation(b), z3.Abs(x - 3) == 2)


def test_named_global_constructor_form_normalizes_to_cp_api():
    b = HirBuilder()
    b.declare("successors", "Int", lower=0, upper=2, shape=[3])
    result = b.expr({
        "op": "circuit",
        "successors": {"array": "successors", "length": 3, "prefix": []},
    })
    assert repr(result.sort) == "Bool"
    cp_api = hir_api()["cp_constructors"]
    assert "named_operator_form" in cp_api


def test_compact_cp_abs_schema_is_exact_and_matches_builder():
    jsonschema = pytest.importorskip("jsonschema")
    schema = jsonschema.Draft202012Validator(hir_schema())
    base = {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability", "declarations": [], "functions": [],
        "constraints": [{"expr": {"cp": {"abs": lit(-2)}}, "span": [0, 1]}],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }
    assert schema.is_valid(base)
    invalid = dict(base)
    invalid["constraints"] = [{
        "expr": {"cp": {"abs": lit(-2)}, "items": []}, "span": [0, 1],
    }]
    assert not schema.is_valid(invalid)
    with pytest.raises(ModelError):
        HirBuilder().expr(invalid["constraints"][0]["expr"])


def test_arrays_folds_and_global():
    b = HirBuilder()
    b.declare("a", {"Array": ["Int", "Int"]})
    select = op("select", var("a"), var("i"))
    b.constrain(
        {
            "fold": "forall",
            "var": "i",
            "range": [0, 3],
            "body": op("and", op("ge", select, lit(0)), op("le", select, lit(2))),
        }
    )
    b.constrain(
        op("all_different", *(op("select", var("a"), lit(i)) for i in range(3)))
    )
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    same(
        relation(b),
        z3.And(
            *[z3.And(a[i] >= 0, a[i] <= 2) for i in range(3)],
            z3.Distinct(*[a[i] for i in range(3)])
        ),
    )


def test_open_domain_quantifier_and_function():
    b = HirBuilder()
    sort = {"Uninterpreted": "Person"}
    b.declare("alice", sort)
    b.declare_function("P", [sort], "Bool")
    b.constrain(
        {
            "quantifier": "forall",
            "binders": [{"name": "x", "sort": sort}],
            "body": {"apply": "P", "args": [var("x")]},
        }
    )
    b.constrain(op("not", {"apply": "P", "args": [var("alice")]}))
    solver = z3.Solver()
    solver.add(relation(b))
    assert solver.check() == z3.unsat


def test_native_exists_and_context_observable_builder_pattern():
    b = HirBuilder()
    entity = {"Uninterpreted": "Entity"}
    b.declare("alice", entity)
    b.declare("somt_goal", "Bool")
    b.declare_function("knows", [entity, entity], "Bool")
    conclusion = {
        "quantifier": "exists",
        "binders": [{"name": "y", "sort": entity}],
        "body": {
            "apply": "knows",
            "args": [var("alice"), var("y")],
        },
    }
    b.constrain(op("eq", var("somt_goal"), conclusion))

    domain = z3.DeclareSort("Entity")
    alice = z3.Const("alice", domain)
    y = z3.Const("y", domain)
    knows = z3.Function("knows", domain, domain, z3.BoolSort())
    same(relation(b), z3.Bool("somt_goal") == z3.Exists([y], knows(alice, y)))


@pytest.mark.parametrize("value", [True, 1.0])
def test_integer_literal_does_not_accept_boolean_or_float(value):
    with pytest.raises(ModelError):
        HirBuilder().expr({"literal": value, "sort": "Int"})


def test_count_and_empty_folds():
    b = HirBuilder()
    b.declare("p", "Bool")
    b.declare("q", "Bool")
    b.constrain(op("eq", op("count", var("p"), var("q")), lit(1)))
    b.constrain(
        {"fold": "forall", "var": "i", "range": [0, 0], "body": lit(False, "Bool")}
    )
    same(relation(b), z3.Xor(z3.Bool("p"), z3.Bool("q")))


@pytest.mark.parametrize(
    "expr",
    [
        op("and", lit(1)),
        op("add", lit(True, "Bool")),
        op("div", lit(1), lit(0)),
        op("div", lit(1), var("x")),
        {"op": "exec", "args": []},
        {"quantifier": "forall", "binders": [], "body": lit(True, "Bool")},
    ],
)
def test_invalid_constructors_refuse(expr):
    with pytest.raises(ModelError):
        HirBuilder().expr(expr)


def test_native_typecheck_and_snapshot():
    b = HirBuilder()
    b.declare("x", "Int")
    t = b.translate()
    assert t.ok
    b.constrain(var("x"))
    assert not b.translate().ok
    assert "(assert x)" not in t.to_smt2()


def test_nl_hir_candidate_selection_and_objective():
    source = "Choose x between 0 and 10. Maximize x."
    model = dict(
        schema="somt-hir-model-v1",
        language="hir",
        decision="optimization",
        declarations=[dict(name="x", sort="Int", lower=0, upper=10)],
        functions=[],
        constraints=[],
        objectives=[dict(sense="maximize", expr=var("x"), span=[0, len(source)])],
        objective_order="single",
        goal=None,
        assumptions=[],
        unresolved=[],
    )
    seen = []

    def provider(request):
        seen.append(request)
        return model

    c = propose_nl(source, language="hir", provider=provider, context={"domain": "Int"})
    assert c.valid, c.diagnostics
    assert "constructor_api" in seen[0]["schema"]
    assert not compile_candidate(c).ok
    t = compile_candidate(c, accept_digest=c.digest)
    assert t.ok, t.diagnostics
    opt = z3.Optimize()
    opt.from_string(t.to_smt2())
    assert opt.check() == z3.sat
    assert opt.model()[z3.Int("x")].as_long() == 10
    assert t.report()["intent_preservation"] == "not-proved"


def test_finite_shape_and_total_data_table():
    b = HirBuilder()
    b.declare("a", "Int", 0, 2, shape=[2, 3])
    b.data = {"cost": [[2, 3, 5], [7, 11, 13]]}
    b.constrain(
        op(
            "eq",
            {"at": "a", "indices": [lit(1), lit(2)]},
            {"data": "cost", "indices": [lit(0), lit(0)], "default": lit(-1)},
        )
    )
    array = z3.Array("a", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    same(
        relation(b),
        z3.And(
            *[
                z3.And(array[i][j] >= 0, array[i][j] <= 2)
                for i in range(2)
                for j in range(3)
            ],
            array[1][2] == 2
        ),
    )
    b.constrain(
        op(
            "eq",
            {"data": "cost", "indices": [lit(99), lit(0)], "default": lit(-1)},
            lit(-1),
        )
    )
    assert b.translate().ok


@pytest.mark.parametrize("sort,value", [("Int", 0), ("Real", "0")])
def test_native_zero_sum_retains_operand_sort_under_all(sort, value):
    b = HirBuilder()
    zero = lit(value, sort)
    b.constrain(op("eq", op("add", zero, zero, zero), zero))
    same(relation(b), z3.BoolVal(True))


def test_bitvector_ground_wraparound():
    b = HirBuilder()
    b.constrain(op("eq", op("bvadd", bv("#xFF", 8), bv("#x01", 8)), bv("#x00", 8)))
    b.constrain(op("bvult", bv("#x01", 8), bv("#xFF", 8)))
    b.constrain(op("bvslt", bv("#xFF", 8), bv("#x01", 8)))
    b.constrain(op("eq", op("concat", bv("#b10", 2), bv("#b01", 2)), bv("#b1001", 4)))
    t = b.translate()
    assert t.ok
    # Ground bit-vector constraints are constant-folded by the pipeline, so the
    # known answer is the fold itself: a wrong wraparound or signedness would
    # emit `false` instead.
    same(relation(b), z3.BoolVal(True))


def test_bitvector_variables_against_z3():
    b = HirBuilder()
    b.declare("x", {"BitVec": 8})
    b.constrain(op("bvule", op("bvadd", var("x"), bv("#b00000001", 8)), var("x")))
    t = b.translate()
    assert t.ok
    text = t.to_smt2()
    assert "bvadd" in text and "bvule" in text
    x = z3.BitVec("x", 8)
    same(relation(b), z3.ULE(x + 1, x))


def test_indexed_bitvector_operators():
    b = HirBuilder()
    b.declare("x", {"BitVec": 8})
    b.declare("n", "Int")
    b.constrain(
        op(
            "eq",
            indexed("rotate_left", [1], var("x")),
            indexed("rotate_right", [7], var("x")),
        )
    )
    b.constrain(
        op(
            "eq",
            indexed("repeat", [2], indexed("extract", [3, 0], var("x"))),
            op(
                "concat",
                indexed("extract", [3, 0], var("x")),
                indexed("extract", [3, 0], var("x")),
            ),
        )
    )
    b.constrain(
        op(
            "eq",
            indexed("sign_extend", [8], indexed("extract", [3, 0], var("x"))),
            indexed("zero_extend", [8], indexed("extract", [3, 0], var("x"))),
        )
    )
    b.constrain(op("eq", var("n"), lit(9)))
    b.constrain(op("eq", indexed("int2bv", [4], var("n")), bv("#b1001", 4)))
    t = b.translate()
    assert t.ok
    text = t.to_smt2()
    for token in [
        "extract",
        "zero_extend",
        "sign_extend",
        "rotate_left",
        "rotate_right",
        "repeat",
        "concat",
        "int2bv",
    ]:
        assert token in text, token
    x = z3.BitVec("x", 8)
    n = z3.Int("n")
    e = z3.Extract(3, 0, x)
    same(
        relation(b),
        z3.And(
            z3.RotateLeft(x, 1) == z3.RotateRight(x, 7),
            # `(_ repeat 2)` of the low nibble is the nibble concatenated
            # with itself: a valid identity, so the parsed relation is True.
            z3.BoolVal(True),
            z3.SignExt(8, e) == z3.ZeroExt(8, e),
            n == 9,
            z3.Int2BV(n, 4) == z3.BitVecVal(9, 4),
        ),
    )
    # z3's SMT-LIB reader has no `divisible`, so this one is checked by
    # translation and emission alone.
    d = HirBuilder()
    d.declare("n", "Int")
    d.constrain(indexed("divisible", [3], var("n")))
    t = d.translate()
    assert t.ok
    assert "divisible" in t.to_smt2()


def test_indexed_extract_rejects_invalid_ranges():
    b = HirBuilder()
    b.declare("x", {"BitVec": 8})
    b.constrain(
        op(
            "eq",
            indexed("extract", [3, 0], var("x")),
            indexed("extract", [7, 4], var("x")),
        )
    )
    t = b.translate()
    assert t.ok
    assert "extract" in t.to_smt2()
    x = z3.BitVec("x", 8)
    same(relation(b), z3.Extract(3, 0, x) == z3.Extract(7, 4, x))

    narrow = HirBuilder()
    narrow.declare("x", {"BitVec": 8})
    narrow.constrain(
        op("eq", indexed("extract", [9, 0], var("x")), bv("#b0000000000", 10))
    )
    assert not narrow.translate().ok

    reversed_bounds = HirBuilder()
    reversed_bounds.declare("x", {"BitVec": 8})
    # The invalid range records a zero-width result. The operand check now
    # refuses the comparison during construction, before target translation.
    with pytest.raises(ModelError, match="compares"):
        reversed_bounds.constrain(
            op("eq", indexed("extract", [3, 5], var("x")), bv("#b11", 2))
        )


@pytest.mark.parametrize(
    "expr",
    [
        indexed("extract", [3], bv("#b1010", 4)),
        indexed("extract", [3, 0, 1], bv("#b1010", 4)),
        indexed("extract", [-1, 0], bv("#b1010", 4)),
        indexed("extract", [True, 0], bv("#b1010", 4)),
        indexed("repeat", [2], bv("#b10", 2), bv("#b10", 2)),
        indexed("to_fp", [8], rm(), lit(1)),
        indexed("nonsense", [1], bv("#b10", 2)),
    ],
)
def test_indexed_operator_validation_refuses(expr):
    with pytest.raises(ModelError):
        HirBuilder().expr(expr)


def test_floating_point_variable_against_z3():
    b = HirBuilder()
    b.declare("f", {"FloatingPoint": [8, 24]})
    b.constrain(op("fp.eq", op("fp.add", rm(), var("f"), var("f")), fp("3.0")))
    t = b.translate()
    assert t.ok
    assert "fp.add" in t.to_smt2()
    f = z3.FP("f", z3.Float32())
    same(
        relation(b),
        z3.fpEQ(z3.fpAdd(z3.RNE(), f, f), z3.FPVal(3.0, z3.Float32())),
    )


def test_floating_point_ground_literals_and_conversions():
    b = HirBuilder()
    # IEEE equality: NaN equals nothing, not even itself.
    b.constrain(op("not", op("fp.eq", fp("NaN"), fp("NaN"))))
    # The bit triple for 1.0 at (8, 24): sign 0, biased exponent 127, mantissa 0.
    b.constrain(
        op("fp.eq", fp(["#b0", "#b01111111", "#b00000000000000000000000"]), fp("1.0"))
    )
    # The same pattern through the bit-pattern reinterpretation conversion.
    b.constrain(op("fp.eq", indexed("ieee_bv_to_fp", [8, 24], bv("#x3F800000", 32)), fp("1.0")))
    b.constrain(
        op("fp.eq", indexed("to_fp", [8, 24], rm(), lit("0.5", "Real")), fp("0.5"))
    )
    b.constrain(op("fp.eq", op("fp.abs", fp("-2.5")), fp("2.5")))
    b.constrain(op("fp.eq", op("fp.neg", fp("2.5")), fp("-2.5")))
    b.constrain(op("fp.leq", fp("-oo"), fp("+zero")))
    t = b.translate()
    assert t.ok
    text = t.to_smt2()
    assert "NaN" in text and "fp.abs" in text
    same(relation(b), z3.BoolVal(True))


def test_string_ground_properties():
    b = HirBuilder()
    b.constrain(op("eq", op("str.len", op("str.++", string("ab"), string("cd"))), lit(4)))
    b.constrain(op("str.contains", string("abcd"), string("bc")))
    b.constrain(op("not", op("str.contains", string("abcd"), string("dc"))))
    b.constrain(op("str.prefixof", string("ab"), string("abcd")))
    b.constrain(op("str.suffixof", string("cd"), string("abcd")))
    b.constrain(op("eq", op("str.at", string("abcd"), lit(1)), string("b")))
    b.constrain(op("eq", op("str.substr", string("abcd"), lit(1), lit(2)), string("bc")))
    b.constrain(op("eq", op("str.indexof", string("abcd"), string("c"), lit(0)), lit(2)))
    b.constrain(op("eq", op("str.replace", string("abc"), string("b"), string("xy")), string("axyc")))
    b.constrain(op("eq", op("str.to_int", string("42")), lit(42)))
    b.constrain(op("eq", op("str.from_int", lit(42)), string("42")))
    t = b.translate()
    assert t.ok
    # As for bit-vectors, ground string constraints are constant-folded at
    # construction; the fold's answer is the known answer.
    same(relation(b), z3.BoolVal(True))


def test_string_variable_against_z3():
    b = HirBuilder()
    b.declare("w", "String")
    b.constrain(op("eq", op("str.++", var("w"), string("!")), string("hi!")))
    b.constrain(op("str.prefixof", string("h"), var("w")))
    b.constrain(op("str.suffixof", string("!"), var("w")))
    b.constrain(op("str.contains", var("w"), string("i")))
    b.constrain(op("eq", op("str.len", var("w")), lit(2)))
    b.constrain(op("eq", op("str.at", var("w"), lit(1)), string("i")))
    b.constrain(op("eq", op("str.substr", var("w"), lit(0), lit(1)), string("h")))
    b.constrain(op("eq", op("str.indexof", var("w"), string("i"), lit(0)), lit(1)))
    b.constrain(op("eq", op("str.replace", var("w"), string("i"), string("u")), string("hu!")))
    t = b.translate()
    assert t.ok
    text = t.to_smt2()
    for token in [
        "str.++",
        "str.len",
        "str.at",
        "str.substr",
        "str.indexof",
        "str.replace",
        "str.prefixof",
        "str.suffixof",
        "str.contains",
    ]:
        assert token in text, token
    w = z3.String("w")
    same(
        relation(b),
        z3.And(
            z3.Concat(w, z3.StringVal("!")) == z3.StringVal("hi!"),
            z3.PrefixOf(z3.StringVal("h"), w),
            z3.SuffixOf(z3.StringVal("!"), w),
            z3.Contains(w, z3.StringVal("i")),
            z3.Length(w) == 2,
            z3.SubString(w, 1, 1) == z3.StringVal("i"),
            z3.SubString(w, 0, 1) == z3.StringVal("h"),
            z3.IndexOf(w, z3.StringVal("i"), 0) == 1,
            z3.Replace(w, z3.StringVal("i"), z3.StringVal("u"))
            == z3.StringVal("hu!"),
        ),
    )


@pytest.mark.parametrize(
    "expr",
    [
        {"literal": "#b1010", "sort": {"BitVec": 8}},
        {"literal": "#x0F", "sort": {"BitVec": 4}},
        {"literal": "#b102", "sort": {"BitVec": 3}},
        {"literal": "abc", "sort": {"BitVec": 3}},
        {"literal": 42, "sort": "String"},
        {"literal": "1e3", "sort": {"FloatingPoint": [8, 24]}},
        {"literal": ["#b0", "#b01111111"], "sort": {"FloatingPoint": [8, 24]}},
        {
            "literal": ["#b0", "#b01111111", "#b000"],
            "sort": {"FloatingPoint": [8, 24]},
        },
        {"rm": "NEAREST"},
        op("bvadd", lit(1), lit(2)),
        op("add", string("a"), string("b")),
        op("str.len", lit(1)),
        op("str.to_int", lit(1)),
        op("fp.add", rm(), lit(1), lit(2)),
        op("fp.eq", fp("1.0"), string("a")),
    ],
)
def test_new_theory_constructors_refuse(expr):
    with pytest.raises(ModelError):
        HirBuilder().expr(expr)


@pytest.mark.parametrize(
    "sort",
    [
        {"BitVec": 0},
        {"BitVec": -3},
        {"BitVec": True},
        {"FloatingPoint": [8]},
        {"FloatingPoint": [8, 0]},
        {"FloatingPoint": "8,24"},
    ],
)
def test_new_sort_validation_refuses(sort):
    with pytest.raises(ModelError):
        HirBuilder().declare("v", sort)


def test_catalog_lists_the_new_theories():
    api = hir_api()
    assert "String" in api["sorts"]
    assert {"BitVec": "positive width in bits"} in api["sorts"]
    assert any(
        isinstance(s, dict) and "FloatingPoint" in s for s in api["sorts"]
    )
    for name in ["bvadd", "concat", "fp.add", "fp.eq", "str.++", "str.len"]:
        assert name in api["operations"]
    for name in ["extract", "zero_extend", "to_fp", "ieee_bv_to_fp"]:
        assert name in api["indexed_operations"]
    assert api["constructors"]["rounding_mode"] == {"rm": "RNE|RNA|RTP|RTN|RTZ"}
    schema = hir_schema()
    assert schema["constructor_api"]["indexed_operations"] == {
        k: list(v) for k, v in api["indexed_operations"].items()
    }
