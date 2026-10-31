import itertools
import pytest
import z3
from tools.semantic_checks.conjunctive_array_projection import (
    prepare_conjunctive_array_body, project_conjunctive_array_reads)
from tools.semantic_checks.circuit_rank_witness import normalize_root_circuit_ranks
from tools.semantic_checks.existential_definitions import eliminate_existential_definitions


def relation(a, rank, n):
    xs = [a[i] for i in range(n)]
    parts = [z3.Distinct(*xs), rank[0] == 0]
    for i,x in enumerate(xs):
        parts.extend([x >= 0, x < n, x != i, rank[i] >= 0, rank[i] < n,
                      z3.Or(x == 0, rank[x] == rank[i] + 1)])
    return z3.Exists(rank, z3.And(*parts))


@pytest.mark.parametrize('sign', [-1, 1])
def test_complete_conjoined_arrays_finite_guard_circuit_and_signed_cost(sign):
    a = z3.Array('composition_a', z3.IntSort(), z3.IntSort())
    rank = z3.Array('composition_rank', z3.IntSort(), z3.IntSort())
    ps = z3.Ints('public0 public1 public2')
    cost, i = z3.Ints('public_cost iteration')
    original = z3.And(*(a[j] == p for j,p in enumerate(ps)), relation(a, rank, 3),
                z3.ForAll(i, z3.Implies(z3.And(i >= 0, i < 3), a[i] >= 0)),
                cost == sign * (a[0] - 2*a[1] + 3*a[2] - 7))
    matched = normalize_root_circuit_ranks(original)
    assert matched.normalized_circuits == 1
    prepared = prepare_conjunctive_array_body(matched.formula, [a])
    assert prepared.lifted_quantifiers == 1
    assert prepared.finite_expansion.expanded_quantifiers == 1
    projected = project_conjunctive_array_reads(matched.formula, [a])
    assert len(projected.eliminated_arrays) == 1
    closed = z3.Exists(list(projected.private_variables), projected.body)
    reduced = eliminate_existential_definitions(closed).formula
    expected = z3.And(z3.Or(z3.And(ps[0]==1, ps[1]==2, ps[2]==0),
                             z3.And(ps[0]==2, ps[1]==0, ps[2]==1)),
                      cost == sign * (ps[0]-2*ps[1]+3*ps[2]-7))
    solver = z3.Solver()
    solver.add(z3.Xor(reduced, expected))
    assert solver.check() == z3.unsat


def test_open_before_finite_expansion_avoids_six_position_cartesian_product():
    a = z3.Array('large_a', z3.IntSort(), z3.IntSort())
    rank = z3.Array('large_rank', z3.IntSort(), z3.IntSort())
    i = z3.Int('bounded_i')
    body = z3.And(relation(a, rank, 6),
                  z3.ForAll(i, z3.Implies(z3.And(i>=0,i<6), a[i]>=0)))
    normalized = normalize_root_circuit_ranks(body)
    assert normalized.normalized_circuits == 1
    prepared = prepare_conjunctive_array_body(normalized.formula, [a])
    assert len(prepared.lifted_variables) == 6
    assert prepared.finite_expansion.expanded_quantifiers == 1
    result = project_conjunctive_array_reads(normalized.formula, [a])
    assert len(result.eliminated_arrays) == 1
    todo = [result.body]
    while todo:
        node = todo.pop()
        assert not z3.is_quantifier(node)
        todo.extend(node.children())
