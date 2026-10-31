import pytest
import z3

from tools.semantic_checks.integer_table_sums import normalize_integer_table_sums


def checked(term):
    report = normalize_integer_table_sums(term)
    solver = z3.Solver(ctx=term.ctx)
    solver.add(term != report.formula)
    assert solver.check() == z3.unsat
    return report


def tables(x):
    positive = z3.If(x < 1, 7, z3.If(x < 4, 11, 5))
    negative = z3.If(x >= 4, -5, z3.If(x >= 1, -11, -7))
    return positive, negative


def test_two_independent_groups_cancel_full_negative_and_positive_tails():
    x, y = z3.Ints('x y')
    a, b = tables(x)
    c, d = tables(y)
    report = checked(a + c + b + d)
    assert z3.is_int_value(report.formula) and report.formula.as_long() == 0
    assert report.combined_groups >= 2


@pytest.mark.parametrize('coefficient', [-7, -1, 1, 3, 10**50])
def test_coefficients_and_shared_occurrence_multiplicity(coefficient):
    x, opaque = z3.Ints('x opaque')
    a, b = tables(x)
    value = coefficient * (a + a) + 2 * coefficient * b + opaque
    assert checked(value).formula.eq(opaque)


@pytest.mark.parametrize('tail', ['negative', 'positive'])
def test_mismatched_infinite_tail_never_cancels(tail):
    x = z3.Int('x')
    a, _ = tables(x)
    b = z3.If(x < 1, -8 if tail == 'negative' else -7,
              z3.If(x < 4, -11, -6 if tail == 'positive' else -5))
    out = checked(a + b).formula
    solver = z3.Solver()
    solver.add(x == (-100 if tail == 'negative' else 100), out != 0)
    assert solver.check() == z3.sat


def test_same_shape_different_indices_do_not_cancel():
    x, y = z3.Ints('x y')
    a, _ = tables(x)
    _, b = tables(y)
    out = checked(a + b).formula
    solver = z3.Solver()
    solver.add(x == 0, y == 2, out != 0)
    assert solver.check() == z3.sat


def test_unrelated_opaque_terms_are_retained():
    x, y = z3.Ints('x y')
    a, b = tables(x)
    f = z3.Function('f', z3.IntSort(), z3.IntSort())
    out = checked(a + f(y) + b + y * y).formula
    solver = z3.Solver()
    solver.add(out != f(y) + y * y)
    assert solver.check() == z3.unsat


def test_exact_compound_index_is_supported():
    x, y, opaque = z3.Ints('x y opaque')
    a, b = tables(x * y + 2)
    assert checked(a + opaque + b).formula.eq(opaque)


def test_exact_dynamic_array_cell_index_is_supported():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, opaque = z3.Ints('i opaque')
    left, right = tables(a[i])
    assert checked(left + opaque + right).formula.eq(opaque)


def test_different_array_cells_not_identified():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, j = z3.Ints('i j')
    left, _ = tables(a[i])
    _, right = tables(a[j])
    out = checked(left + right).formula
    solver = z3.Solver()
    solver.add(i != j, a[i] == 0, a[j] == 2, out != 0)
    assert solver.check() == z3.sat


def test_conditional_unknown_boolean_not_a_constant_table():
    x = z3.Int('x')
    p = z3.Bool('p')
    left, right = tables(x)
    checked(z3.If(p, left, 4) + right)


def test_table_product_same_index_and_opaque_nonlinear_product():
    x, y = z3.Ints('x y')
    a, _ = tables(x)
    b = z3.If(x < 1, -49, z3.If(x < 4, -121, -25))
    out = checked(a * a + b + x * y).formula
    solver = z3.Solver()
    solver.add(out != x * y)
    assert solver.check() == z3.unsat


def test_product_different_indices_remains_exact():
    x, y = z3.Ints('x y')
    a, _ = tables(x)
    b, _ = tables(y)
    out = checked(a * b - a * a).formula
    solver = z3.Solver()
    solver.add(x == 0, y == 2, out != 0)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('kind', ['negative', 'subtraction', 'multiply', 'ite', 'zero'])
def test_constant_summands(kind):
    x, opaque = z3.Ints('x opaque')
    a, b = tables(x)
    constants = dict(negative=-z3.IntVal(3), subtraction=z3.IntVal(9)-4,
                     multiply=z3.IntVal(-3)*5, ite=z3.If(z3.BoolVal(True), 6, 8),
                     zero=z3.IntVal(0))
    c = constants[kind]
    out = checked(a + opaque + b + c).formula
    solver = z3.Solver()
    solver.add(out != opaque + c)
    assert solver.check() == z3.unsat


def test_binder_is_opaque():
    x = z3.Int('x')
    a, b = tables(x)
    formula = z3.ForAll(x, a + b == 0)
    report = normalize_integer_table_sums(formula)
    assert report.formula.eq(formula) and report.visited_nodes == 1


def test_binder_inside_opaque_arithmetic_term_remains_unchanged():
    x, y = z3.Ints('x y')
    a, b = tables(x)
    bound = z3.ForAll(y, z3.And(y == y, y + 0 == y))
    opaque = z3.If(bound, x, x + 1)
    result = checked(a + opaque + b).formula
    assert result.eq(opaque)


def test_real_arithmetic_not_integer_coerced():
    x = z3.Real('x')
    f = z3.If(x < z3.RealVal('1/2'), 7, 11) + z3.If(x < 0, -7, -11)
    checked(f)


def test_shared_dag_150_levels_preserves_multiplicity():
    x, y = z3.Ints('x y')
    a, b = tables(x)
    term = a + z3.If(y < 0, 3, 4)
    for _ in range(150):
        term = term + term
    opposite = (2**150) * (b + z3.If(y < 0, -3, -4))
    report = checked(term + opposite)
    assert z3.simplify(report.formula).as_long() == 0
    assert report.visited_nodes < 220


def test_serialized_negative_thresholds():
    f = z3.parse_smt2_string('''(declare-const x Int)(declare-const cost Int)
      (assert (= cost (+ (ite (< x (- 3)) 7 9)
                         (ite (>= x (- 3)) (- 9) (- 7)))))''')[0]
    out = checked(f).formula
    solver = z3.Solver()
    solver.add(out, z3.Int('cost') != 0)
    assert solver.check() == z3.unsat


def test_nondefault_context_and_fresh_constants():
    ctx = z3.Context()
    x, y = z3.Ints('x y', ctx)
    a, b = tables(x)
    result = checked(a + b + y)
    assert result.formula.ctx == ctx and result.formula.eq(y)


def test_after_exact_ite_hoisting_common_cross_index_sum_cancels():
    x, y = z3.Ints('x y')
    a, b = tables(x)
    c, d = tables(y)
    # This is the exact shape produced after a separate qualified ITE hoist.
    f = a + c + b + d + z3.If(x < 1, 0, z3.If(x < 4, 2, 3))
    expected = z3.If(x < 1, 0, z3.If(x < 4, 2, 3))
    out = checked(f).formula
    solver = z3.Solver()
    solver.add(out != expected)
    assert solver.check() == z3.unsat


def test_unsupported_division_is_not_reinterpreted():
    x, y = z3.Ints('x y')
    a, b = tables(x)
    checked(a + b + y / x)


def test_idempotence():
    x, y = z3.Ints('x y')
    a, b = tables(x)
    out = checked(a + b + z3.If(y < 0, 7, 9)).formula
    assert normalize_integer_table_sums(out).formula.eq(out)
