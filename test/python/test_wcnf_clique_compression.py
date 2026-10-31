"""Exact hard relations and soft costs after binary-clause compression."""
from itertools import combinations

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def literal(index):
    value = z3.Bool(f"x{abs(index)}")
    return value if index > 0 else z3.Not(value)


def translated(hard, soft, old_format=False, variables=None):
    count = len(hard) + len(soft)
    variables = variables or max(abs(x) for clause in hard + [c for _, c in soft]
                                for x in clause)
    text = f"p wcnf {variables} {count} 1000000000000000000\n" if old_format else ""
    marker = "1000000000000000000" if old_format else "h"
    for clause in hard:
        text += marker + " " + " ".join(map(str, clause)) + " 0\n"
    for weight, clause in soft:
        text += str(weight) + " " + " ".join(map(str, clause)) + " 0\n"
    result = sp.translate(source=text, language="wcnf")
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    return target


def check_relation_and_cost(target, hard, soft):
    expected_hard = z3.And(*[z3.Or(*map(literal, clause)) for clause in hard])
    expected_cost = z3.Sum([z3.If(z3.Or(*map(literal, clause)), 0, weight)
                            for weight, clause in soft])
    assert len(target.objectives()) == 1
    solver = z3.Solver()
    solver.set(timeout=10000)
    # The cost comparison is deliberately independent of feasibility: an
    # empty hard clause must not make a wrong soft cost pass vacuously.
    solver.add(z3.Or(z3.Xor(z3.And(*target.assertions()), expected_hard),
                     target.objectives()[0] != expected_cost))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("old_format", [False, True])
@pytest.mark.parametrize("vertices", [(1, 2, 3, 4), (-1, -2, -3, -4),
                                      (1, -2, 3, -4), (1, -1, 2, 3)])
def test_signed_cliques_duplicates_and_exact_soft_weights(old_format, vertices):
    hard = list(combinations(vertices, 2))
    hard += [hard[0], (1, 1), (1, -1), (-1, 2, 3)]
    soft = [(5, (-3,)), (7, ()), (9007199254740993, (1, -4)), (3, (1, -1))]
    target = translated(hard, soft, old_format)
    check_relation_and_cost(target, hard, soft)


def test_overlapping_cliques_and_uncovered_edges():
    hard = list(combinations((1, -2, 3, 4), 2))
    hard += list(combinations((1, -2, 5, -6), 2))
    hard += [(3, 5), (4, 6), (2,), (1, -3, 6)]
    soft = [(11, (2, -4)), (13, (-1, 5))]
    check_relation_and_cost(translated(hard, soft), hard, soft)


def test_empty_hard_clause_retains_exact_constant_soft_cost():
    hard = list(combinations((1, 2, 3, 4), 2)) + [()]
    soft = [(9, ())]
    check_relation_and_cost(translated(hard, soft), hard, soft)


def test_sparse_large_vocabulary_keeps_uncovered_edges():
    hard = [(1, 1000), (-1, 500), (1, 1000)]
    soft = [(17, (-500,))]
    check_relation_and_cost(translated(hard, soft, old_format=True), hard, soft)


def test_large_clique_has_one_hard_constraint_and_the_same_relation():
    hard = list(combinations(range(1, 49), 2))
    soft = [(7, (1,))]
    target = translated(hard, soft, old_format=True)
    assert len(target.assertions()) == 1
    expected = z3.Sum([z3.If(z3.Bool(f"x{i}"), 0, 1) for i in range(1, 49)]) <= 1
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Or(z3.Xor(target.assertions()[0], expected),
                     target.objectives()[0] != z3.If(z3.Bool("x1"), 0, 7)))
    assert solver.check() == z3.unsat
