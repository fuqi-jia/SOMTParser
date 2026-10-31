"""Exact extensional finite-set carriers through MiniZinc -> HIR -> Z3."""
import pytest
import z3
import somtparser as sp


def _translate(source, quantifier_free=True):
    result = sp.translate(source=source, language="minizinc", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2(sp.OmtDialect.Z3)
    if quantifier_free:
        assert "(forall " not in text and "(exists " not in text
    return text


def _literal(values):
    value = z3.EmptySet(z3.IntSort())
    for item in values:
        value = z3.SetAdd(value, item)
    return value


def _equal_relation(text, expected):
    actual = z3.And(*z3.parse_smt2_string(text))
    solver = z3.Solver(); solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("lo,hi", [(-2, 2), (1, 0), (-3, -1), (2, 2)])
def test_every_array_cell_excludes_all_outside_members(lo, hi):
    text = _translate(f"array[-1..0] of var set of {lo}..{hi}:s; solve satisfy;")
    array = z3.Array("s", z3.IntSort(), z3.SetSort(z3.IntSort()))
    value = z3.Int("reference_element")
    expected = z3.And(*(z3.ForAll(value, z3.Implies(z3.IsMember(value, array[index]),
                      z3.And(value >= lo, value <= hi))) for index in (-1, 0)))
    _equal_relation(text, expected)
    solver = z3.Solver(); solver.from_string(text)
    solver.add(z3.IsMember(hi + 1, array[-1]))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("members", [[], [-2], [-2, 2], [-1, 0, 2]])
@pytest.mark.parametrize("context", ["plain", "negated", "reified"])
def test_fixed_array_set_equality_preserves_holes_and_boolean_context(members, context):
    fixed = "{" + ",".join(map(str, members)) + "}"
    equality = f"[s[1]] = [{fixed}]"
    relation = {"plain": equality, "negated": "not (" + equality + ")",
                "reified": "b <-> (" + equality + ")"}[context]
    text = _translate("array[1..1] of var set of -2..2:s; var bool:b; "
                      f"constraint {relation}; solve satisfy;")
    array = z3.Array("s", z3.IntSort(), z3.SetSort(z3.IntSort()))
    equal = array[1] == _literal(members)
    expected = {"plain": equal, "negated": z3.Not(equal),
                "reified": z3.Bool("b") == equal}[context]
    _equal_relation(text, z3.And(z3.IsSubset(array[1], _literal(range(-2, 3))), expected))


@pytest.mark.parametrize("claimed", [0, 1, 2, 3, 4, 5, 6])
def test_array_carrier_proves_cardinality_support(claimed):
    text = _translate("array[1..1] of var set of -2..2:s; "
                      f"constraint card(s[1])={claimed}; solve satisfy;")
    cell = z3.Select(z3.Array("s", z3.IntSort(), z3.SetSort(z3.IntSort())), 1)
    count = z3.Sum(*(z3.If(z3.IsMember(i, cell), 1, 0) for i in range(-2, 3)))
    _equal_relation(text, z3.And(z3.IsSubset(cell, _literal(range(-2, 3))), count == claimed))


def test_empty_carrier_cardinality_is_zero():
    text = _translate("array[1..1] of var set of 1..0:s; constraint card(s[1])=0; solve satisfy;")
    cell = z3.Select(z3.Array("s", z3.IntSort(), z3.SetSort(z3.IntSort())), 1)
    _equal_relation(text, cell == _literal([]))


def test_scalar_set_carrier_and_cardinality_have_no_explicit_quantifier():
    text = _translate("var set of -1..1:s; constraint card(s)=2; solve satisfy;")
    value = z3.Const("s", z3.SetSort(z3.IntSort()))
    count = z3.Sum(*(z3.If(z3.IsMember(i, value), 1, 0) for i in range(-1, 2)))
    _equal_relation(text, z3.And(z3.IsSubset(value, _literal(range(-1, 2))), count == 2))


def test_large_domain_retains_exact_quantified_fallback():
    text = _translate("array[1..1] of var set of -100000..100000:s; solve satisfy;", False)
    assert "(forall " in text
    cell = z3.Select(z3.Array("s", z3.IntSort(), z3.SetSort(z3.IntSort())), 1)
    element = z3.Int("outside_reference")
    _equal_relation(text, z3.ForAll(element, z3.Implies(z3.IsMember(element, cell),
                    z3.And(element >= -100000, element <= 100000))))
