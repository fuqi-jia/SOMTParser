import pytest
import z3

from tools.semantic_checks.conjunctive_array_projection import (
    prepare_conjunctive_array_body, project_conjunctive_array_reads)
from tools.semantic_checks.ground_array_projection import UnsupportedArrayProjection


def close(variables, body):
    return z3.Exists(list(variables), body) if variables else body


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('sign', [-1, 1])
def test_complete_array_relation_and_signed_cost_with_nested_witness(sign):
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    rank = z3.Array('rank', z3.IntSort(), z3.IntSort())
    p, q, cost = z3.Ints('public_p public_q public_cost')
    inner = z3.Exists(rank, z3.And(rank[0] == a[0] + 1, rank[1] == a[1] + 1,
                                     rank[0] < rank[1]))
    body = z3.And(a[0] == p, a[1] == q, inner, cost == sign * (a[0] - 2 * a[1]))
    prepared = prepare_conjunctive_array_body(body, [a])
    assert prepared.lifted_quantifiers == 1
    result = project_conjunctive_array_reads(body, [a])
    assert len(result.eliminated_arrays) == 2
    projected = close(result.private_variables, result.body)
    expected = z3.And(p < q, cost == sign * (p - 2 * q))
    equivalent(projected, expected)
    # Necessity uses arbitrary arrays; sufficiency constructs total arrays.
    # This proves both directions without asking Z3 to decide quantified-array
    # XOR (which may return unknown even for these finite observations).
    open_body = z3.And(a[0] == p, a[1] == q,
                       rank[0] == a[0] + 1, rank[1] == a[1] + 1,
                       rank[0] < rank[1], cost == sign * (a[0] - 2 * a[1]))
    equivalent(z3.And(open_body, z3.Not(expected)), z3.BoolVal(False))
    array_witness = z3.Store(z3.Store(z3.K(z3.IntSort(), 0), 0, p), 1, q)
    rank_witness = z3.Store(z3.Store(z3.K(z3.IntSort(), 0), 0, p + 1), 1, q + 1)
    witnessed = z3.substitute(open_body, (a, array_witness), (rank, rank_witness))
    equivalent(z3.And(expected, z3.Not(witnessed)), z3.BoolVal(False))


@pytest.mark.parametrize('offset', [-2, 4])
def test_finite_forall_uses_only_its_original_guard(offset):
    a = z3.Array('guard_a', z3.IntSort(), z3.IntSort())
    i, p, q = z3.Ints('guard_i guard_p guard_q')
    body = z3.And(a[offset] == p, a[offset + 1] == q,
                  z3.ForAll(i, z3.Implies(z3.And(i >= offset, i <= offset + 1), a[i] >= i)))
    prepared = prepare_conjunctive_array_body(body, [a])
    assert prepared.finite_expansion.expanded_quantifiers == 1
    result = project_conjunctive_array_reads(body, [a])
    projected = close(result.private_variables, result.body)
    expected = z3.And(p >= offset, q >= offset + 1)
    equivalent(projected, expected)
    # The guard is exactly these two integers; no endpoint is sampled away.
    guard = z3.And(i >= offset, i <= offset + 1)
    equivalent(guard, z3.Or(i == offset, i == offset + 1))
    necessary_instances = z3.And(a[offset] == p, a[offset + 1] == q,
                                 a[offset] >= offset, a[offset + 1] >= offset + 1)
    equivalent(z3.And(necessary_instances, z3.Not(expected)), z3.BoolVal(False))
    witness = z3.Store(z3.Store(z3.K(z3.IntSort(), 0), offset, p), offset + 1, q)
    equivalent(z3.And(expected, guard, z3.Not(witness[i] >= i)), z3.BoolVal(False))
    equivalent(z3.And(expected, z3.Not(z3.And(witness[offset] == p,
                                             witness[offset + 1] == q))), z3.BoolVal(False))


def test_fresh_opening_preserves_same_spelled_free_array():
    free = z3.Array('collision', z3.IntSort(), z3.IntSort())
    inner = z3.Array('collision', z3.IntSort(), z3.IntSort())
    p = z3.Int('collision_public')
    body = z3.And(free[0] == p, z3.Exists(inner, inner[0] == 3))
    prepared = prepare_conjunctive_array_body(body, [free])
    assert not prepared.lifted_variables[0].eq(free)
    result = project_conjunctive_array_reads(body, [free])
    equivalent(close(result.private_variables, result.body), z3.BoolVal(True))
    equivalent(close([free], body), close(result.private_variables, result.body))


def test_nested_existential_dependence_is_not_detached():
    a = z3.Array('outer', z3.IntSort(), z3.IntSort())
    b = z3.Array('inner', z3.IntSort(), z3.IntSort())
    p, cost = z3.Ints('dependence_public dependence_cost')
    body = z3.Exists(a, z3.And(a[0] == p, z3.Exists(b, z3.And(b[0] == a[0] + 1, cost == b[0]))))
    prepared = prepare_conjunctive_array_body(body, [])
    assert prepared.lifted_quantifiers == 2
    result = project_conjunctive_array_reads(body, [])
    equivalent(close(result.private_variables, result.body), cost == p + 1)
    equivalent(body, close(result.private_variables, result.body))


@pytest.mark.parametrize('context', ['negative', 'disjunction', 'implication'])
def test_existential_is_not_hoisted_from_nonconjunctive_context(context):
    a = z3.Array('protected_a', z3.IntSort(), z3.IntSort())
    b = z3.Array('protected_b', z3.IntSort(), z3.IntSort())
    public = z3.Bool('public_guard')
    inner = z3.Exists(b, b[0] > a[0])
    body = {'negative': z3.Not(inner), 'disjunction': z3.Or(public, inner),
            'implication': z3.Implies(public, inner)}[context]
    prepared = prepare_conjunctive_array_body(body, [a])
    assert prepared.lifted_quantifiers == 0
    with pytest.raises(UnsupportedArrayProjection):
        project_conjunctive_array_reads(body, [a])


def test_unbounded_forall_remains_unsupported_instead_of_assuming_finite_domain():
    a = z3.Array('unbounded_a', z3.IntSort(), z3.IntSort())
    i = z3.Int('unbounded_i')
    body = z3.ForAll(i, z3.Implies(i >= 0, a[i] == i))
    prepared = prepare_conjunctive_array_body(body, [a])
    assert prepared.finite_expansion.expanded_quantifiers == 0
    with pytest.raises(UnsupportedArrayProjection):
        project_conjunctive_array_reads(body, [a])


def test_symbolic_indices_retain_read_congruence_without_added_bounds():
    a = z3.Array('congruence_a', z3.IntSort(), z3.IntSort())
    b = z3.Array('congruence_b', z3.IntSort(), z3.IntSort())
    i, j, p, q = z3.Ints('i j p q')
    body = z3.And(a[i] == p, a[j] == q, z3.Exists(b, b[i] == a[j]))
    result = project_conjunctive_array_reads(body, [a])
    equivalent(close(result.private_variables, result.body), z3.Implies(i == j, p == q))
    equivalent(close([a], body), close(result.private_variables, result.body))
