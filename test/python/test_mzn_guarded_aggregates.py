"""Finite generator semantics checked by enumerating source assignments."""
import itertools
import math

import pytest
import z3
import somtparser as sp


def translate(source):
    result = sp.translate(source=source, language="minizinc", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result, z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))


@pytest.mark.parametrize("fold", ["sum", "product", "count", "forall", "exists"])
def test_decision_filter_preserves_every_source_assignment(fold):
    boolean = fold in {"forall", "exists"}
    body = "a[i] == 1" if fold in {"count", "forall", "exists"} else "a[i]"
    _, formula = translate(
        "array[1..3] of var -1..1: a; "
        f"var {'bool' if boolean else 'int'}: answer; "
        f"constraint answer = {fold}(i in 1..3 where a[i] != 0)({body}); "
        "solve satisfy;"
    )
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    answer = z3.Bool("answer") if boolean else z3.Int("answer")
    solver = z3.Solver()
    solver.set(timeout=3000)
    solver.add(formula)
    for values in itertools.product((-1, 0, 1), repeat=3):
        selected = [x for x in values if x != 0]
        expected = {
            "sum": sum(selected), "product": math.prod(selected),
            "count": selected.count(1), "forall": all(x == 1 for x in selected),
            "exists": any(x == 1 for x in selected),
        }[fold]
        solver.push()
        solver.add(*[a[i + 1] == value for i, value in enumerate(values)])
        assert solver.check() == z3.sat
        solver.add(answer != expected)
        assert solver.check() == z3.unsat, (fold, values, expected)
        solver.pop()


@pytest.mark.parametrize("expression", [
    "count(i, j in 1..2)(i == j)",
    "count([true, false, true])", "count(flags)",
    "count([i == 2 | i in 1..4]) + 1",
])
def test_count_unary_and_grouped_generator_overloads(expression):
    _, formula = translate(
        "array[3..5] of bool: flags = array1d(3..5, [true, false, true]); "
        f"constraint {expression} = 2; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_both_dynamic_bounds_and_empty_intervals():
    _, formula = translate(
        "var -2..2: lower; var -1..3: upper; var int: answer; "
        "constraint answer = sum(i in lower..upper)(i*i); solve satisfy;"
    )
    lower, upper, answer = z3.Ints("lower upper answer")
    solver = z3.Solver()
    solver.add(formula)
    for lo, hi in itertools.product(range(-2, 3), range(-1, 4)):
        expected = sum(i * i for i in range(lo, hi + 1))
        solver.push()
        solver.add(lower == lo, upper == hi)
        assert solver.check() == z3.sat
        solver.add(answer != expected)
        assert solver.check() == z3.unsat, (lo, hi)
        solver.pop()


def test_array_element_bound_arithmetic_and_outer_generator_dependency():
    _, formula = translate("""
array[1..2] of var 0..3: stop;
var int: answer;
constraint answer = sum(d in 1..2)(sum(i in 1..stop[d]-1)(i*d));
solve satisfy;
""")
    stop = z3.Array("stop", z3.IntSort(), z3.IntSort())
    answer = z3.Int("answer")
    solver = z3.Solver()
    solver.add(formula)
    for first, second in itertools.product(range(4), repeat=2):
        expected = sum(range(1, first)) + 2 * sum(range(1, second))
        solver.push()
        solver.add(stop[1] == first, stop[2] == second)
        assert solver.check() == z3.sat
        solver.add(answer != expected)
        assert solver.check() == z3.unsat
        solver.pop()


@pytest.mark.parametrize("negated", [False, True])
def test_partial_range_bound_does_not_turn_into_an_empty_sum(negated):
    relation = "sum(i in 1..stop[index])(i) = 0"
    if negated:
        relation = "not (" + relation + ")"
    _, formula = translate(
        "array[1..1] of var 0..3: stop; var 0..1: index; "
        f"constraint index = 0; constraint {relation}; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == (z3.sat if negated else z3.unsat)


@pytest.mark.parametrize("selected", [False, True])
@pytest.mark.parametrize("negated", [False, True])
def test_only_selected_numeric_body_requires_a_value(selected, negated):
    relation = "sum(i in 1..2 where selected)(i div 0) = 0"
    if negated:
        relation = "not (" + relation + ")"
    _, formula = translate(
        "var bool: selected; "
        f"constraint selected = {str(selected).lower()}; "
        f"constraint {relation}; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == (z3.sat if (not selected) != negated else z3.unsat)


def test_search_annotation_preserves_objective():
    result, _ = translate("""
var 0..3: x;
ann: search = int_search([x], smallest, indomain_min, complete);
solve :: search minimize x;
""")
    solver = z3.Optimize()
    solver.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert len(solver.objectives()) == 1
    assert solver.check() == z3.sat
    assert solver.model().eval(z3.Int("x")).as_long() == 0


def test_empty_inner_generator_does_not_read_a_provisional_out_of_range_cell():
    _, formula = translate("""
int: n = 1;
array[1..n,1..n] of int: compatible = array2d(1..n,1..n,[1]);
array[1..n] of var 0..1: value;
constraint forall(i in 1..n, j in i+1..n where compatible[i,j] = 0)(
  value[j] = 0
);
constraint value[1] = 1;
solve satisfy;
""")
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_empty_domain_keeps_type_checking_without_leaking_probe_declarations():
    result, formula = translate("""
constraint forall(i in 1..0)(let { array[1..2] of var bool: local; } in local[1]);
solve satisfy;
""")
    assert "@let" not in result.to_smt2()
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat
    assert not sp.translate(source="constraint forall(i in 1..0)(missing); solve satisfy;",
                            language="minizinc").ok
    assert not sp.translate(source="constraint forall(i in 1..0)(42); solve satisfy;",
                            language="minizinc").ok


def test_constant_count_is_available_to_parameter_elaboration():
    _, formula = translate("""
int: size = count(i in 1..3)(i > 1);
array[1..size] of var bool: flags;
constraint count(flags) = 2;
solve satisfy;
""")
    flags = z3.Array("flags", z3.IntSort(), z3.BoolSort())
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat
    solver.add(z3.Not(flags[1]))
    assert solver.check() == z3.unsat


def test_count_of_an_initialized_decision_array_preserves_holes():
    _, formula = translate("""
array[1..2] of var bool: flags = [_, true];
constraint count(flags) = 2;
solve satisfy;
""")
    flags = z3.Array("flags", z3.IntSort(), z3.BoolSort())
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat
    solver.add(z3.Not(flags[1]))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("source", [
    "var int: n; constraint sum(i in 1..n)(i) = 0; solve satisfy;",
    "constraint count(i in 1..2)(i) = 1; solve satisfy;",
    "constraint count([1, 2]) = 1; solve satisfy;",
    "constraint forall(i in 1..2 where 1)(true); solve satisfy;",
    "ann: search = ; solve satisfy;",
    "ann: search = int_search([1), first_fail); solve satisfy;",
    "ann: search = int_search([1], first_fail)",
])
def test_missing_bounds_wrong_sorts_and_incomplete_annotations_are_diagnosed(source):
    assert not sp.translate(source=source, language="minizinc").ok
