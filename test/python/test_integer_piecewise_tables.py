import pytest
import z3

from tools.semantic_checks.integer_piecewise_tables import normalize_integer_piecewise_tables


def normalized(term):
    report = normalize_integer_piecewise_tables(term)
    solver = z3.Solver()
    solver.add(term != report.formula)
    assert solver.check() == z3.unsat
    return report.formula


@pytest.mark.parametrize('op', ['lt', 'le', 'gt', 'ge', 'eq', 'ne'])
@pytest.mark.parametrize('reverse', [False, True])
def test_integer_comparison_every_direction(op, reverse):
    x = z3.Int('x')
    left, right = (z3.IntVal(-3), x) if reverse else (x, z3.IntVal(-3))
    condition = {'lt': lambda: left < right, 'le': lambda: left <= right,
                 'gt': lambda: left > right, 'ge': lambda: left >= right,
                 'eq': lambda: left == right, 'ne': lambda: left != right}[op]()
    normalized(z3.If(condition, -700, 900))


def test_threshold_tree_equals_point_lookup_with_both_tails():
    x = z3.Int('x')
    balanced = z3.If(x < 1, -8, z3.If(x < 3, z3.If(x == 1, 7, 9), 80))
    lookup = z3.If(x == 2, 9, z3.If(x == 1, 7, z3.If(x <= 0, -8, 80)))
    assert normalized(balanced).eq(normalized(lookup))


@pytest.mark.parametrize('tail', ['left', 'right'])
def test_mismatched_infinite_tail_does_not_match(tail):
    x = z3.Int('x')
    original = z3.If(x < 0, -4, z3.If(x <= 2, 7, 9))
    wrong = z3.If(x < 0, -5 if tail == 'left' else -4,
                  z3.If(x <= 2, 7, 10 if tail == 'right' else 9))
    a, b = normalized(original), normalized(wrong)
    assert not a.eq(b)
    solver = z3.Solver()
    solver.add(a != b)
    assert solver.check() == z3.sat


def test_sparse_points_do_not_fill_holes():
    x = z3.Int('x')
    sparse = z3.If(z3.Or(x == -10, x == 10), 6, 0)
    dense = z3.If(z3.And(x >= -10, x <= 10), 6, 0)
    a, b = normalized(sparse), normalized(dense)
    solver = z3.Solver()
    solver.add(x == 0, a != b)
    assert solver.check() == z3.sat


def test_overlapping_branches_preserve_first_match():
    x = z3.Int('x')
    a = z3.If(x >= 2, 5, z3.If(x >= 0, 4, 3))
    b = z3.If(x < 0, 3, z3.If(x < 2, 4, 5))
    assert normalized(a).eq(normalized(b))


def test_disjoint_and_overlapping_boolean_connectives():
    x = z3.Int('x')
    a = z3.And(z3.Or(x < -3, x > 5), z3.Not(x == 8), z3.Implies(x >= 7, x != 9))
    normalized(z3.If(a, 1, 0))


def test_arithmetic_composition_and_literal_comparison():
    x = z3.Int('x')
    a = z3.If(x < 0, 2, 3)
    b = z3.If(x == 0, -7, 5)
    normalized(z3.If((a * b + 3 - a) <= -10, -b, a + b))


def test_multiple_symbolic_indices_are_not_identified():
    x, y = z3.Ints('x y')
    a = z3.If(x < 0, 7, 8) + z3.If(y < 0, 2, 3)
    b = z3.If(x < 0, 9, 11)
    assert not normalized(a).eq(normalized(b))
    solver = z3.Solver()
    solver.add(x < 0, y >= 0, normalized(a) != normalized(b))
    assert solver.check() == z3.sat


def test_compound_integer_index_is_retained():
    x, y = z3.Ints('x y')
    normalized(z3.If(x * y < -100, 1, z3.If(x * y == 9, 3, 4)))


def test_variable_array_cell_index_is_retained():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i = z3.Int('i')
    normalized(z3.If(a[i] >= 3, 80, z3.If(a[i] == -1, -8, 0)))


def test_quantifier_body_is_not_traversed():
    x = z3.Int('x')
    term = z3.ForAll(x, z3.If(x < 0, 8, 9) > 5)
    result = normalize_integer_piecewise_tables(term)
    assert result.formula.eq(term)
    assert result.table_rewrites == 0


def test_real_threshold_is_not_rounded_to_integer():
    x = z3.Real('x')
    term = z3.If(x < z3.RealVal('1/2'), 4, 7)
    assert normalize_integer_piecewise_tables(term).formula.eq(term)


def test_huge_endpoints_are_exact_and_not_enumerated():
    x = z3.Int('x')
    k = 10 ** 100
    term = z3.If(x < -k, 1, z3.If(x <= k, 2, 3))
    result = normalize_integer_piecewise_tables(term)
    assert result.emitted_regions == 3
    normalized(term)


def test_no_context_domain_is_assumed_or_removed():
    x = z3.Int('x')
    term = z3.Implies(z3.And(x >= 0, x <= 3), z3.If(x < 1, 2, 3) == 3)
    out = normalized(term)
    assert z3.is_true(z3.simplify(z3.substitute(out, (x, z3.IntVal(-100)))))


def test_bool_valued_partition_and_reification():
    x = z3.Int('x')
    flag = z3.Bool('flag')
    normalized(flag == z3.If(x < 0, x == -3, z3.Or(x == 5, x > 7)))


def test_distinct_literal_tables_is_pointwise_exact():
    x = z3.Int('x')
    normalized(z3.Distinct(z3.If(x >= 0, 1, 2), z3.If(x == 5, 1, 3), z3.IntVal(2)))


def test_unsupported_uninterpreted_function_preserves_arguments():
    x = z3.Int('x')
    f = z3.Function('f', z3.IntSort(), z3.IntSort())
    normalized(f(z3.If(x < 0, 3, 4)))


def test_shared_dag_stays_linear_to_visit():
    x = z3.Int('x')
    node = z3.If(x < 0, 1, 2)
    for _ in range(120):
        node = node + node
    result = normalize_integer_piecewise_tables(node)
    assert result.visited_nodes < 130
    normalized(node)


def test_context_is_preserved():
    ctx = z3.Context()
    x = z3.Int('x', ctx=ctx)
    term = z3.If(x < 0, z3.IntVal(4, ctx), z3.IntVal(7, ctx))
    out = normalize_integer_piecewise_tables(term).formula
    assert out.ctx == ctx
    solver = z3.Solver(ctx=ctx)
    solver.add(term != out)
    assert solver.check() == z3.unsat


def test_emitted_form_is_idempotent():
    x = z3.Int('x')
    term = z3.If(z3.Or(x <= -7, x >= 4), 2, z3.If(x == 0, 8, 3))
    once = normalized(term)
    assert once.eq(normalized(once))
