import itertools

import pytest
import z3

from tools.semantic_checks.circuit_rank_witness import normalize_root_circuit_ranks


def original(xs, first, rank):
    n = len(xs)
    parts = [z3.Distinct(*xs), rank[first] == 0]
    for i, x in enumerate(xs, first):
        parts.extend((x >= first, x < first + n, x != i,
                      rank[i] >= 0, rank[i] < n,
                      z3.Or(x == first, rank[x] == rank[i] + 1)))
    return parts


def proves(formula):
    solver = z3.Solver(ctx=formula.ctx)
    solver.add(z3.Not(formula))
    assert solver.check() == z3.unsat


def circuit(values, first):
    n = len(values)
    if sorted(values) != list(range(first, first + n)):
        return False
    node, seen = first, set()
    for _ in values:
        if node in seen:
            return False
        seen.add(node)
        node = values[node - first]
    return node == first and len(seen) == n


def assignments(xs, values):
    return z3.And(*(x == value for x, value in zip(xs, values)))


@pytest.mark.parametrize('n,first', [(2, 0), (3, -3), (4, 1)])
@pytest.mark.parametrize('sign', [-1, 1])
def test_complete_relation_and_signed_cost_with_total_array_witness(n, first, sign):
    ctx = z3.Context()
    xs = [z3.Int('x' + str(i), ctx=ctx) for i in range(n)]
    rank = z3.Array('unrelated_rank_spelling', z3.IntSort(ctx), z3.IntSort(ctx))
    cost = z3.Int('signed_cost', ctx=ctx)
    cost_eq = cost == sign * (z3.Sum(*(x * (i + 1) for i, x in enumerate(xs))) - 7)
    native_body = z3.And(*original(xs, first, rank))
    formula = z3.And(z3.Exists(rank, native_body), cost_eq)
    transformed = normalize_root_circuit_ranks(formula)
    assert transformed.normalized_circuits == 1 and transformed.nodes == (n,)
    cycles = [values for values in itertools.permutations(range(first, first + n))
              if circuit(values, first)]
    expected = z3.And(z3.Or(*(assignments(xs, values) for values in cycles)), cost_eq)
    # Necessity uses the complete native body and arbitrary total rank array.
    proves(z3.Implies(z3.And(native_body, cost_eq), expected))
    # Sufficiency extends each full Hamiltonian cycle's distance map to a
    # total array. All original native conjuncts and signed cost remain.
    for values in cycles:
        witness = z3.K(z3.IntSort(ctx), z3.IntVal(0, ctx))
        node = first
        for distance in range(n):
            witness = z3.Store(witness, node, distance)
            node = values[node - first]
        witnessed = z3.substitute(native_body, (rank, witness))
        proves(z3.Implies(z3.And(assignments(xs, values), cost_eq),
                          z3.And(witnessed, cost_eq)))
    # The replacement's DISTINCT + [1,n] bounds prove its witnesses are
    # exactly these n! permutations. Expand every permutation, not samples.
    quant = next(c for c in transformed.formula.children() if z3.is_quantifier(c))
    alternatives = [z3.substitute_vars(quant.body(),
                    *[z3.IntVal(v, ctx) for v in reversed(values)])
                    for values in itertools.permutations(range(1, n + 1))]
    scalar_relation = z3.And(z3.Or(*alternatives), cost_eq)
    proves(scalar_relation == expected)
    proves(z3.Not(scalar_relation) == z3.Not(expected))


@pytest.mark.parametrize('missing', ['permutation', 'anchor', 'lower-x', 'upper-x',
                                     'self-loop', 'lower-rank', 'upper-rank', 'edge'])
def test_missing_any_original_contract_part_is_not_normalized(missing):
    xs = z3.Ints('m0 m1 m2')
    rank = z3.Array('m_rank', z3.IntSort(), z3.IntSort())
    parts = original(xs, 0, rank)
    index = {'permutation': 0, 'anchor': 1, 'lower-x': 2, 'upper-x': 3,
             'self-loop': 4, 'lower-rank': 5, 'upper-rank': 6, 'edge': 7}[missing]
    formula = z3.Exists(rank, z3.And(*(p for i, p in enumerate(parts) if i != index)))
    result = normalize_root_circuit_ranks(formula)
    assert result.normalized_circuits == 0 and result.formula.eq(formula)


@pytest.mark.parametrize('mutation', ['extra-rank-cost', 'increment-two', 'noncontiguous',
                                      'second-anchor', 'rank-dependent-successor'])
def test_changed_or_additional_rank_constraints_are_not_erased(mutation):
    xs = list(z3.Ints('c0 c1 c2'))
    rank = z3.Array('c_rank', z3.IntSort(), z3.IntSort())
    if mutation == 'rank-dependent-successor':
        xs[1] = rank[9]
    parts = original(xs, 0, rank)
    if mutation == 'extra-rank-cost':
        parts.append(z3.Int('public_extra_cost') == rank[1])
    elif mutation == 'increment-two':
        parts[7] = z3.Or(xs[0] == 0, rank[xs[0]] == rank[0] + 2)
    elif mutation == 'noncontiguous':
        parts[7] = z3.Or(xs[0] == 0, rank[xs[0]] == rank[10] + 1)
    elif mutation == 'second-anchor':
        parts.append(rank[1] == 0)
    formula = z3.Exists(rank, z3.And(*parts))
    result = normalize_root_circuit_ranks(formula)
    assert result.normalized_circuits == 0 and result.formula.eq(formula)


def test_missing_permutation_has_real_counterexample_to_cycle_claim():
    xs = z3.Ints('bad0 bad1 bad2')
    rank = z3.Array('bad_rank', z3.IntSort(), z3.IntSort())
    weakened = z3.And(*original(xs, 0, rank)[1:])
    solver = z3.Solver()
    solver.add(weakened, assignments(xs, [1, 0, 1]))
    assert solver.check() == z3.sat
    assert not circuit([1, 0, 1], 0)
    assert normalize_root_circuit_ranks(z3.Exists(rank, weakened)).normalized_circuits == 0


@pytest.mark.parametrize('context', ['not', 'or', 'implies', 'outer-forall', 'outer-exists'])
def test_nonconjunctive_and_bound_contexts_keep_exact_ast(context):
    xs = z3.Ints('ctx0 ctx1 ctx2')
    rank = z3.Array('ctx_rank', z3.IntSort(), z3.IntSort())
    raw = z3.Exists(rank, z3.And(*original(xs, 0, rank)))
    guard = z3.Bool('context_guard')
    formula = {'not': z3.Not(raw), 'or': z3.Or(guard, raw),
               'implies': z3.Implies(guard, raw),
               'outer-forall': z3.ForAll(xs[0], raw),
               'outer-exists': z3.Exists(xs[0], raw)}[context]
    result = normalize_root_circuit_ranks(formula)
    assert result.normalized_circuits == 0 and result.formula.eq(formula)


def test_permuted_conjuncts_and_spelling_collision_preserve_public_context():
    rank = z3.Array('circuit_position', z3.IntSort(), z3.IntSort())
    free = z3.Int('circuit_position')
    xs = z3.Ints('p0 p1 p2')
    parts = original(xs, -1, rank)
    formula = z3.And(free == 19, z3.Exists(rank, z3.And(*reversed(parts))))
    result = normalize_root_circuit_ranks(formula)
    assert result.normalized_circuits == 1
    assert any(c.eq(free == 19) for c in result.formula.children())


def test_two_independent_circuit_contracts_are_both_preserved():
    a, b = [z3.Array(name, z3.IntSort(), z3.IntSort()) for name in ['ar', 'br']]
    xs, ys = z3.Ints('a0 a1 a2'), z3.Ints('b0 b1')
    formula = z3.And(z3.Exists(a, z3.And(*original(xs, -2, a))),
                     z3.Exists(b, z3.And(*original(ys, 4, b))))
    result = normalize_root_circuit_ranks(formula)
    assert result.normalized_circuits == 2 and result.nodes == (3, 2)


@pytest.mark.parametrize('first', [-2, 0, 1])
def test_reversed_edge_equalities_match_without_arithmetic_isolation(first):
    xs = z3.Ints('reversed0 reversed1 reversed2')
    rank = z3.Array('reversed_rank', z3.IntSort(), z3.IntSort())
    parts = original(xs, first, rank)
    for offset, x in enumerate(xs):
        index = first + offset
        # This is the real emitted orientation seen in the 21-node circuit.
        parts[2 + 6*offset + 5] = z3.Or(rank[index] + 1 == rank[x], first == x)
        parts[2 + 6*offset + 2] = z3.Distinct(index, x)
    formula = z3.Exists(rank, z3.And(*reversed(parts)))
    result = normalize_root_circuit_ranks(formula)
    assert result.normalized_circuits == 1 and result.nodes == (3,)
