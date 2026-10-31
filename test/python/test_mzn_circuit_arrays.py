"""Circuit and composed finite arrays, checked against independent graph semantics."""
import itertools

import pytest
import z3
import somtparser as sp


def translate(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result, z3.And(*z3.parse_smt2_string(result.to_smt2()))


def one_cycle(successors, start):
    n = len(successors)
    if n == 0:
        return True
    if n == 1:
        return False
    seen = set()
    current = start
    for _ in range(n):
        if current in seen or not start <= current < start + n:
            return False
        seen.add(current)
        current = successors[current - start]
    return current == start and len(seen) == n


@pytest.mark.parametrize("start", [-2, 1, 5])
@pytest.mark.parametrize("negated", [False, True])
def test_circuit_all_three_vertex_functions_and_out_of_domain_edges(start, negated):
    formula = "circuit(s)"
    if negated:
        formula = "not (" + formula + ")"
    result, relation = translate(
        f"array[{start}..{start+2}] of var int: s; constraint {formula}; solve satisfy;"
    )
    assert "circuit-local-ranks" in result.report.to_json()
    successors = z3.Array("s", z3.IntSort(), z3.IntSort())
    assignments = list(itertools.product(range(start, start + 3), repeat=3))
    assignments += [(start - 1, start + 2, start), (start + 3, start, start + 1)]
    for values in assignments:
        # Each assignment checks the same complete formula in a fresh solver.
        # The incremental solver timed out on later unsatisfiable assignments
        # in the full suite; fresh contexts keep checks independent.
        solver = z3.Solver()
        solver.set(timeout=3000)
        solver.add(relation)
        solver.add(*[successors[start + i] == value for i, value in enumerate(values)])
        expected = one_cycle(values, start) != negated
        actual = solver.check()
        assert actual == (z3.sat if expected else z3.unsat), (values, solver.reason_unknown())


@pytest.mark.parametrize("cells, expected", [
    ("[]", z3.sat), ("[1]", z3.unsat), ("[2, 1]", z3.sat),
    ("[2, 1, 4, 3]", z3.unsat), ("[2, 3, 4, 1]", z3.sat),
])
def test_circuit_empty_singleton_and_disjoint_cycles(cells, expected):
    _, formula = translate(f"constraint circuit({cells}); solve satisfy;")
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == expected


def test_negated_circuit_keeps_partial_successor_definedness_local():
    _, formula = translate("constraint not circuit([1 div 0, 1]); solve satisfy;")
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_parameter_constructor_concat_and_expression_domain_preserve_exact_values():
    source = r"""
array[4..5] of int: costs = array1d(4..5, [3, 7]);
array[0..2] of int: padded = array1d(0..2, [0] ++ costs);
array[0..2] of var min(padded)..(max(padded)+1): departures =
    array1d(0..2, [0] ++ [padded[i] + 1 | i in 1..2]);
constraint departures[0] = 0 /\ departures[1] = 4 /\ departures[2] = 8;
solve satisfy;
"""
    _, formula = translate(source)
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat
    departures = z3.Array("departures", z3.IntSort(), z3.IntSort())
    solver.add(departures[1] != 4)
    assert solver.check() == z3.unsat


def test_concatenation_preserves_free_holes_and_named_decision_cells():
    _, formula = translate("""
array[4..5] of var int: free = array1d(4..5, [_, 7]);
array[1..3] of var int: copied = ([0] ++ free);
constraint copied[2] = 19;
solve satisfy;
""")
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat
    free = z3.Array("free", z3.IntSort(), z3.IntSort())
    solver.add(free[4] != 19)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("source", [
    "array[0..1] of var int: a = array1d(1..2, [1,2]); solve satisfy;",
    "array[1..2] of int: a = array1d(1..2, [1]); solve satisfy;",
    "array[1..2,1..2] of var int: a; constraint circuit(a); solve satisfy;",
    "array[1..2,1..2] of var int: a; array[1..5] of var int: b = [0] ++ a; solve satisfy;",
    "constraint circuit([true, false]); solve satisfy;",
])
def test_incompatible_shapes_and_sorts_are_rejected(source):
    assert not sp.translate(source=source, language="minizinc").ok
