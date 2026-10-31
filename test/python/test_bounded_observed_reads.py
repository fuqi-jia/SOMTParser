"""Whole-formula checks for bounded nested reads and their refusal boundaries."""
import pytest
import z3

from tools.semantic_checks.bounded_observed_reads import expand_bounded_observed_reads
from tools.semantic_checks.checker_adapter import candidate_projection
from tools.semantic_checks.projection import free_constants


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def bridges(array, coordinates):
    result = []
    for coordinate in coordinates:
        term = array
        for index in coordinate:
            term = term[index]
        result.append((z3.FreshConst(term.sort(), "observed"), term))
    return result


@pytest.mark.parametrize("bounds", [
    lambda i: z3.And(i >= -2, i <= 1),
    lambda i: z3.And(-3 < i, 2 > i),
    lambda i: z3.And(-2 <= i, 1 >= i),
    lambda i: z3.And(i > -3, i < 2),
    lambda i: z3.And(i >= -4, i >= -2, i <= 8, i <= 1),
])
def test_signed_inclusive_and_strict_bounds_preserve_entire_formula(bounds):
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    i = z3.Int("i")
    formula = z3.And(bounds(i), a[i] == 7)
    result = expand_bounded_observed_reads(formula, bridges(a, [(k,) for k in range(-2, 2)]))
    assert result.expanded_reads == 1 and result.expanded_cells == 4
    equivalent(formula, result.formula)


def test_equality_bound_keeps_the_original_guard():
    a = z3.Array("a", z3.IntSort(), z3.BoolSort())
    i = z3.Int("i")
    formula = z3.And(i == 4, a[i])
    result = expand_bounded_observed_reads(formula, bridges(a, [(4,)]))
    assert result.expanded_reads == 1
    equivalent(formula, result.formula)
    solver = z3.Solver()
    solver.add(result.formula, i != 4)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("guard", [
    lambda i: i >= 0,
    lambda i: i <= 1,
    lambda i: z3.Or(i == 0, i == 1),
    lambda i: z3.Implies(z3.Bool("enabled"), z3.And(i >= 0, i <= 1)),
    lambda i: z3.Not(z3.And(i < 0, i > 1)),
])
def test_shape_and_nonmandatory_bounds_never_supply_a_domain(guard):
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    i = z3.Int("i")
    formula = z3.And(guard(i), a[i] == 7)
    result = expand_bounded_observed_reads(formula, bridges(a, [(0,), (1,)]))
    assert result.expanded_reads == 0 and result.formula.eq(formula)


@pytest.mark.parametrize("upper", [2, 10**100])
def test_incomplete_observation_rectangle_is_not_truncated(upper):
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    i = z3.Int("i")
    formula = z3.And(i >= 0, i <= upper, a[i] == 7)
    result = expand_bounded_observed_reads(formula, bridges(a, [(0,), (1,)]))
    assert result.expanded_reads == 0 and result.formula.eq(formula)


def test_quantifier_context_stays_unchanged():
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    i, j = z3.Ints("i j")
    formula = z3.And(i >= 0, i <= 1, a[i] == 2, z3.ForAll(j, a[j] >= 0))
    result = expand_bounded_observed_reads(formula, bridges(a, [(0,), (1,)]))
    assert result.expanded_reads == 0 and result.formula.eq(formula)


def test_composite_index_bounds_are_not_rewritten_circularly():
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    i = z3.Int("i")
    formula = z3.And(a[i] >= 0, a[i] <= 1, a[a[i]] == 2)
    result = expand_bounded_observed_reads(formula, bridges(a, [(0,), (1,)]))
    assert result.expanded_reads == 0 and result.formula.eq(formula)


def test_array_extensional_equality_is_preserved():
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    b = z3.Array("b", z3.IntSort(), z3.IntSort())
    i = z3.Int("i")
    formula = z3.And(i >= 0, i <= 1, a[i] == 7, a == b, b[99] == 9)
    result = expand_bounded_observed_reads(formula, bridges(a, [(0,), (1,)]))
    assert result.expanded_reads == 1
    equivalent(formula, result.formula)


def test_nested_quasigroup_reads_project_all_public_cells_and_cost():
    q = z3.Array("q", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    coordinates = [(i, j) for i in range(2) for j in range(2)]
    observations = bridges(q, coordinates)
    aliases = dict(zip(coordinates, [alias for alias, _ in observations]))
    constraints = [bound for _, cell in observations for bound in (cell >= 0, cell <= 1)]
    constraints += [z3.Distinct(q[i][0], q[i][1]) for i in range(2)]
    constraints += [z3.Distinct(q[0][i], q[1][i]) for i in range(2)]
    constraints += [q[q[i][j]][q[j][i]] == 0 for i, j in coordinates]
    constraints.append(q[0][0] == 0)
    # Preserve an additional signed cost relation throughout projection.
    cost = z3.Int("observed_signed_cost")
    cost_term = -(q[q[0][1]][q[1][0]] + q[0][1] + 1)
    complete = z3.And(*constraints, cost == cost_term)
    expanded = expand_bounded_observed_reads(complete, observations)
    assert expanded.expanded_reads == 4
    equivalent(complete, expanded.formula)

    result = candidate_projection(constraints, observations, cost_bridge=(cost, cost_term),
                                  guarded_bool_budget_ms=0)
    assert result.optimization.bounded_observed_reads == 4
    assert result.optimization.bounded_observed_table_cells == 4
    assert result.optimization.eliminated_array_roots == ("q",)
    assert not any(c.sort().kind() == z3.Z3_ARRAY_SORT for c in free_constants([result.formula]))

    def cell(i, j):
        return z3.If(i == 0, z3.If(j == 0, aliases[0, 0], aliases[0, 1]),
                     z3.If(j == 0, aliases[1, 0], aliases[1, 1]))

    expected = [bound for a in aliases.values() for bound in (a >= 0, a <= 1)]
    expected += [z3.Distinct(aliases[i, 0], aliases[i, 1]) for i in range(2)]
    expected += [z3.Distinct(aliases[0, i], aliases[1, i]) for i in range(2)]
    expected += [cell(aliases[i, j], aliases[j, i]) == 0 for i, j in coordinates]
    expected.append(aliases[0, 0] == 0)
    expected += [cost == -(cell(aliases[0, 1], aliases[1, 0]) + aliases[0, 1] + 1)]
    equivalent(result.formula, z3.And(*expected))
    solver = z3.Solver()
    solver.add(result.formula)
    assert solver.check() == z3.sat
    solver.add(cost != -2)
    assert solver.check() == z3.unsat


def test_outside_array_values_remain_legal_without_bounds():
    q = z3.Array("q", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    obs = bridges(q, [(0, 0), (0, 1), (1, 0), (1, 1)])
    formula = z3.And(q[0][0] == 5, q[q[0][0]][q[0][0]] == 0)
    result = expand_bounded_observed_reads(formula, obs)
    assert result.expanded_reads == 0 and result.formula.eq(formula)
    solver = z3.Solver()
    solver.add(result.formula)
    assert solver.check() == z3.sat


def test_repeated_nested_reads_keep_a_shared_expression_dag():
    # An n*n output with n*n dynamic lookups should not manufacture a new
    # n*n decision table at every lookup. This measures the result DAG rather
    # than requiring a particular helper implementation or Store ordering.
    n = 16
    q = z3.Array("shared_q", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    coordinates = [(i, j) for i in range(n) for j in range(n)]
    observations = bridges(q, coordinates)
    bounds = [bound for _, cell in observations for bound in (cell >= 0, cell < n)]
    reads = [q[q[i][j]][q[j][i]] == z3.Int(f"wanted_{i}_{j}") for i, j in coordinates]
    source = z3.And(*(bounds + reads))
    result = expand_bounded_observed_reads(source, observations)
    assert result.expanded_reads == n * n
    assert result.materialized_cells == n * n

    def dag_size(term):
        pending = [term]
        visited = set()
        while pending:
            current = pending.pop()
            if current.get_id() not in visited:
                visited.add(current.get_id())
                pending.extend(current.children())
        return len(visited)

    assert dag_size(result.formula) < 4 * dag_size(source)


def test_real_valued_table_cost_preserves_a_nondefault_z3_context():
    ctx = z3.Context()
    a = z3.Array("prices", z3.IntSort(ctx), z3.RealSort(ctx))
    i = z3.Int("choice", ctx)
    observed_i = z3.Int("observed_choice", ctx)
    price0, price1, cost = [z3.Real(name, ctx) for name in ("price0", "price1", "signed_cost")]
    constraints = [i >= 0, i <= 1, a[0] == z3.RealVal('-5/2', ctx),
                   a[1] == z3.RealVal('13/4', ctx)]
    result = candidate_projection(constraints,
        [(observed_i, i), (price0, a[0]), (price1, a[1])],
        cost_bridge=(cost, -a[i]), guarded_bool_budget_ms=0)
    expected = z3.And(observed_i >= 0, observed_i <= 1,
        price0 == z3.RealVal('-5/2', ctx), price1 == z3.RealVal('13/4', ctx),
        cost == z3.If(observed_i == 0, z3.RealVal('5/2', ctx), z3.RealVal('-13/4', ctx)))
    assert result.optimization.eliminated_array_roots == ("prices",)
    equivalent(result.formula, expected)
