"""Joint uniqueness differs from nested per-coordinate uniqueness."""
import z3

from somtparser.hir import HirBuilder
from test_hir_exists_unique import formula, lit, op, quantified, same, unique, var


def test_joint_unique_does_not_become_nested_unique():
    # x=False has one y; x=True has two y's. There is one x with a unique y,
    # but there are three full satisfying tuples, so joint uniqueness is false.
    relation = op("or", *(op("and", op("eq", var("x"), lit(x, "Bool")),
                             op("eq", var("y"), lit(y, "Bool")))
        for x, y in [(False, False), (True, False), (True, True)]))
    joint = unique(relation, (("x", "Bool"), ("y", "Bool")))
    nested = unique(unique(relation, (("y", "Bool"),)), (("x", "Bool"),))
    same(formula(joint), z3.BoolVal(False))
    same(formula(nested), z3.BoolVal(True))


def test_reglan_binder_retains_native_sort_without_inventing_an_encoding():
    # Native HIR has regex sorts; solver support for quantified regex variables
    # remains backend-dependent, just as for ordinary forall and exists.
    builder = HirBuilder()
    builder.declare("target", "RegLan")
    builder.constrain(unique(op("eq", var("x"), var("target")), (("x", "RegLan"),)))
    builder.validate()
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert "RegLan" in translated.to_smt2()
