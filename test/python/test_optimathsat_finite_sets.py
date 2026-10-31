"""Finite-set lowering keeps exact membership, cardinality and Boolean scope."""
import itertools

import pytest
import somtparser as sp
import z3


def literal(values):
    values = list(values)
    return "(as set.empty (Set Int))" if not values else (
        "(set.insert " + " ".join(f"(- {-v})" if v < 0 else str(v) for v in values)
        + " (as set.empty (Set Int)))")


def translate(source):
    translated = sp.translate(source=source, language="smtlib2", dialect=sp.OmtDialect.OptiMathSAT)
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    output = translated.to_smt2(sp.OmtDialect.OptiMathSAT)
    assert "((_ map " not in output
    assert "(Set " not in output
    assert "(Array Int Bool)" not in output
    assert sp.parse(output)
    return output


@pytest.mark.parametrize("left_mask,right_mask", list(itertools.product(range(8), repeat=2)))
def test_all_subsets_preserve_three_operations_and_cardinality(left_mask, right_mask):
    carrier = [-2, 0, 3]
    left = {value for index, value in enumerate(carrier) if left_mask & (1 << index)}
    right = {value for index, value in enumerate(carrier) if right_mask & (1 << index)}
    expected = {"set.union": left | right, "set.inter": left & right, "set.minus": left - right}
    assertions = []
    for operation, result in expected.items():
        term = f"({operation} S T)"
        assertions.extend([f"(= {term} {literal(result)})", f"(= (set.card {term}) {len(result)})"])
    # Negating the conjunction distinguishes exact preservation from a mere
    # equisatisfiable encoding that accidentally drops the actual operations.
    source = ("(set-logic ALL)(declare-const S (Set Int))(declare-const T (Set Int))"
              f"(assert (= S {literal(left)}))(assert (= T {literal(right)}))"
              "(assert (not (and " + " ".join(assertions) + ")))(check-sat)")
    output = translate(source)
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(output))
    assert solver.check() == z3.unsat


def test_symbolic_duplicate_candidates_are_counted_once_and_remain_scoped():
    source = (
        "(set-logic ALL)(declare-const x Int)(declare-const y Int)"
        "(assert (= x y))"
        "(assert (let ((S (set.insert x y (as set.empty (Set Int)))))"
        " (not (= (set.card (set.union S (set.singleton x))) 1))))(check-sat)"
    )
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(translate(source)))
    assert solver.check() == z3.unsat


def test_nested_set_array_selects_keep_outside_members_excluded():
    source = (
        "(set-logic ALL)(declare-const x (Array Int (Set Int)))"
        "(assert (= (select x 0) (set.inter (select x 0) " + literal([-2, 0, 3]) + ")))"
        "(assert (set.member 4 (select x 0)))(check-sat)"
    )
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(translate(source)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("route", ["translation", "parser_dump"])
def test_optimization_routes_encode_sets_and_preserve_objective(route):
    source = (
        "(set-logic ALL)(declare-const S (Set Int))"
        "(assert (= S (set.inter S " + literal([-2, 0, 3]) + ")))"
        "(assert (>= (set.card S) 1))(minimize (set.card S))"
        "(check-sat)(get-objectives)"
    )
    output = (translate(source) if route == "translation" else
              sp.parse(source).dump_smt2(dialect=sp.OmtDialect.OptiMathSAT))
    assert "((_ map " not in output
    assert "(Set " not in output
    assert "(Array Int Bool)" not in output
    assert "BitVec 1" in output
    assert "(minimize " in output
    assert "(get-objectives)" in output
    parsed = sp.parse(output)
    assert parsed is not None
