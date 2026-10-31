"""Zero-exempt distinct retains Int semantics, slices and partiality."""

import pytest
import z3
import somtparser as sp


def _relation(terms):
    return z3.And(*[z3.Or(a == 0, b == 0, a != b)
                    for i, a in enumerate(terms) for b in terms[i + 1:]])


def _equivalent(source, expected, profile="default"):
    result = sp.translate(source=source, language="minizinc", profile=profile)
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("name", ["alldifferent_except_0", "all_different_except_0",
                                  "fzn_alldifferent_except_0"])
@pytest.mark.parametrize("negated", [False, True])
def test_unbounded_integer_terms_in_both_polarities(name, negated):
    values = z3.Ints("x y z")
    formula = _relation(values)
    _equivalent("var int:x; var int:y; var int:z; constraint "
                + ("not " if negated else "") + name + "([x,y,z]); solve satisfy;",
                z3.Not(formula) if negated else formula)


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_whole_array_uses_its_actual_index_set(profile):
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    _equivalent("array[-2..1]of var int:a; constraint alldifferent_except_0(a); solve satisfy;",
                _relation([a[i] for i in range(-2, 2)]), profile)


@pytest.mark.parametrize("body", ["alldifferent_except_0(a[2,..])",
                                 "alldifferent_except_0(j in 1..3)(a[2,j])",
                                 "alldifferent_except_0([a[2,j] | j in 1..3])"])
def test_row_slice_generator_and_comprehension(body):
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    _equivalent("array[1..2,1..3]of var int:a; constraint " + body + "; solve satisfy;",
                _relation([a[i] for i in range(3, 6)]))


@pytest.mark.parametrize("body", ["alldifferent_except_0([])",
                                 "alldifferent_except_0([0,0,-3,3])",
                                 "alldifferent_except_0(i in 1..0)(i)"])
def test_zero_repetitions_and_vacuous_relations(body):
    _equivalent("constraint " + body + "; solve satisfy;", z3.BoolVal(True))


@pytest.mark.parametrize("body", ["alldifferent_except_0([0,-3,-3])",
                                 "alldifferent_except_0([2,2,0])"])
def test_repeated_nonzero_values_are_forbidden(body):
    _equivalent("constraint " + body + "; solve satisfy;", z3.BoolVal(False))


@pytest.mark.parametrize("declarations,body", [
    ("", "alldifferent_except_0([true])"),
    ("", "alldifferent_except_0([1.0])"),
    ("", "alldifferent_except_0(i in 1..0)(true)"),
    ("array[1..0]of bool:a=[];", "alldifferent_except_0(a)"),
    ("array[1..1]of var float:a;", "alldifferent_except_0(a)"),
])
def test_wrong_types_are_rejected_even_in_vacuous_cases(declarations, body):
    result = sp.translate(source=declarations + "constraint " + body + ";solve satisfy;",
                          language="minizinc")
    assert not result.ok
    assert any("Int" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("negated", [False, True])
def test_partial_singleton_is_not_silently_replaced_by_true(negated):
    d = z3.Int("d")
    _equivalent("var int:d; constraint " + ("not " if negated else "")
                + "alldifferent_except_0([1 div d]); solve satisfy;",
                d == 0 if negated else d != 0)
