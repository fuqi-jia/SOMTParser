"""Checked JSON construction for heterogeneous HIR tuples."""
import pytest
import shutil
import subprocess

from somtparser.hir import HirBuilder, ModelError, hir_api


def var(name):
    return {"var": name}


def lit(value, sort):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


def indexed(name, indices, *args):
    return {"op_indexed": {"op": name, "indices": indices, "args": list(args)}}


def test_tuple_catalog_and_heterogeneous_nested_sorts():
    api = hir_api()
    assert {"Tuple": ["field sort", "..."]} in api["sorts"]
    assert "tuple" in api["constructors"]
    assert "tuple_unit" in api["constructors"]
    assert {"tuple.select", "tuple.update", "tuple.project"} <= set(
        api["indexed_operations"]
    )

    builder = HirBuilder()
    nested = {"Tuple": ["Bool", {"BitVec": 2}, {"Tuple": []}]}
    builder.declare("value", nested)
    builder.constrain(op("eq", indexed("tuple.select", [0], var("value")), lit(True, "Bool")))
    builder.constrain(
        op(
            "eq",
            indexed("tuple.update", [0], var("value"), lit(False, "Bool")),
            var("value"),
        )
    )
    builder.constrain(
        op("eq", indexed("tuple.project", [1, 0, 1], var("value")),
           {"tuple": [lit("#b01", {"BitVec": 2}), lit(True, "Bool"),
                      lit("#b10", {"BitVec": 2})]})
    )
    builder.constrain(
        op("eq", indexed("tuple.select", [2], var("value")), {"tuple_unit": True})
    )
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2()
    assert "(Tuple Bool (_ BitVec 2) UnitTuple)" in text
    assert "((_ tuple.select 0) value)" in text
    assert "((_ tuple.update 0) value false)" in text
    assert "((_ tuple.project 1 0 1) value)" in text


def test_unit_and_empty_projection_are_real_tuple_values():
    builder = HirBuilder()
    builder.declare("t", {"Tuple": ["Bool"]})
    builder.declare("unit", {"Tuple": []})
    builder.constrain(op("eq", var("unit"), {"tuple_unit": True}))
    builder.constrain(
        op("eq", indexed("tuple.project", [], var("t")), {"tuple_unit": True})
    )
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert "tuple.unit" in result.to_smt2()
    assert "((_ tuple.project)" not in result.to_smt2()


def test_bool_bitvector_tuple_semantics_against_cvc5_exhaustively():
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for an independent native tuple oracle")

    tuple_sort = {"Tuple": ["Bool", {"BitVec": 2}, {"Tuple": []}]}
    for boolean in (False, True):
        for bits in range(4):
            bit_text = f"#b{bits:02b}"
            boolean_literal = lit(boolean, "Bool")
            bit_literal = lit(bit_text, {"BitVec": 2})
            expected_projection = {
                "tuple": [bit_literal, boolean_literal, bit_literal]
            }
            expected_update = {
                "tuple": [lit(False, "Bool"), bit_literal, {"tuple_unit": True}]
            }
            input_value = {
                "tuple": [boolean_literal, bit_literal, {"tuple_unit": True}]
            }
            equations = [
                op("eq", indexed("tuple.select", [0], var("t")), boolean_literal),
                op("eq", indexed("tuple.select", [1], var("t")), bit_literal),
                op("eq", indexed("tuple.select", [2], var("t")), {"tuple_unit": True}),
                op("eq", indexed("tuple.project", [1, 0, 1], var("t")),
                   expected_projection),
                op("eq", indexed("tuple.project", [], var("t")), {"tuple_unit": True}),
                op("eq", indexed("tuple.update", [0], var("t"), lit(False, "Bool")),
                   expected_update),
            ]

            def compile_with_claim(claim):
                builder = HirBuilder()
                builder.declare("t", tuple_sort)
                builder.constrain(op("eq", var("t"), input_value))
                builder.constrain(claim)
                translated = builder.translate()
                assert translated.ok, [d.message for d in translated.diagnostic_items]
                text = translated.to_smt2()
                if "(check-sat)" not in text:
                    text += "\n(check-sat)\n"
                return text

            positive = compile_with_claim(op("and", *equations))
            negative = compile_with_claim(op("not", op("and", *equations)))
            statuses = []
            reference = f"""(set-logic ALL)
(declare-const t (Tuple Bool (_ BitVec 2) UnitTuple))
(assert (= t (tuple {str(boolean).lower()} {bit_text} tuple.unit)))
(assert (= ((_ tuple.select 0) t) {str(boolean).lower()}))
(assert (= ((_ tuple.select 1) t) {bit_text}))
(assert (= ((_ tuple.select 2) t) tuple.unit))
(assert (= ((_ tuple.project 1 0 1) t) (tuple {bit_text} {str(boolean).lower()} {bit_text})))
(assert (= tuple.unit tuple.unit))
(assert (= ((_ tuple.update 0) t false) (tuple false {bit_text} tuple.unit)))
(check-sat)
"""
            for script in (reference, positive, negative):
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
                assert len(answers) == 1, result.stdout + result.stderr
                statuses.extend(answers)
            assert statuses == ["sat", "sat", "unsat"], statuses


@pytest.mark.parametrize(
    "sort",
    [
        {"Tuple": ()},
        {"Tuple": ["UnsupportedSort", "Int"]},
        {"Tuple": ["Bool"], "ignored": True},
    ],
)
def test_tuple_sort_requires_exact_object_and_list(sort):
    with pytest.raises(ModelError):
        HirBuilder().declare("t", sort)


@pytest.mark.parametrize(
    "expression",
    [
        {"tuple": []},
        {"tuple": [lit(True, "Bool"), "bad"]},
        {"tuple_unit": False},
        {"tuple_unit": True, "extra": 1},
        indexed("tuple.select", [-1], var("t")),
        indexed("tuple.select", [0, 1], var("t")),
        indexed("tuple.select", [0], var("x")),
        indexed("tuple.select", [2], var("t")),
        indexed("tuple.select", [2**40], var("t")),
        indexed("tuple.update", [1], var("t"), lit(1, "Int")),
        indexed("tuple.update", [0], var("t"), lit(False, "Bool")),
        indexed("tuple.project", [0, 2], var("t")),
    ],
)
def test_tuple_expression_shapes_and_types_fail_before_lowering(expression):
    builder = HirBuilder()
    builder.declare("t", {"Tuple": ["Int", "Bool"]})
    builder.declare("x", "Int")
    with pytest.raises((ModelError, ValueError)):
        builder.expr(expression)


def test_tuple_constructor_and_indexed_operator_arity_are_strict():
    builder = HirBuilder()
    builder.declare("t", {"Tuple": ["Int", "Bool"]})
    for expression in (
        {"tuple": [lit(1, "Int")], "extra": None},
        indexed("tuple.select", [], var("t")),
        indexed("tuple.select", [0], var("t"), var("t")),
        indexed("tuple.update", [0], var("t")),
        indexed("tuple.project", [], var("t"), var("t")),
    ):
        with pytest.raises((ModelError, ValueError)):
            builder.expr(expression)


def test_selected_field_sort_is_checked_by_native_typechecker():
    builder = HirBuilder()
    builder.declare("t", {"Tuple": ["Int", "Bool"]})
    with pytest.raises(ModelError, match="compares Bool with Int") as error:
        builder.constrain(
            op("eq", indexed("tuple.select", [1], var("t")), lit(1, "Int"))
        )
    assert error.value.path == "model.args[1]"
    # Direct native users can still construct an ill-typed node. Keep the
    # independent C++ guard covered after Python starts refusing it earlier.
    from somtparser import _somtparser as native
    field = builder.expr(indexed("tuple.select", [1], var("t")))
    builder.model.constrain(native._hir_op("eq", [field, builder.expr(lit(1, "Int"))]))
    with pytest.raises(ModelError, match="Bool"):
        builder.validate()
    result = builder.translate()
    assert not result.ok
    assert any("Bool" in diagnostic.message or "sort" in diagnostic.message
               for diagnostic in result.diagnostic_items)
