"""Exact array-index normalization after ordinary macro expansion."""
import pytest
import z3

from tools.semantic_checks.closed_array_indices import normalize_closed_int_array_indices
from tools.semantic_checks.projection import free_constants, optimize_observation_projection


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.set(timeout=5000)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_25_ordinary_macro_calls_and_ground_window_indices_project_all_200_cells():
    terms = ' '.join(f'(ite (= (select a {index}) tag) 1 0)' for index in range(200))
    script = [
        '(declare-const sequence (Array Int Int))',
        f'(define-fun count ((a (Array Int Int)) (tag Int)) Int (+ {terms}))',
        '(define-fun window ((a (Array Int Int)) (start Int) (tag Int)) Int '
        '(+ (ite (= (select a start) tag) 1 0) (ite (= (select a (+ 1 start)) tag) 1 0)))',
    ]
    for tag in range(25):
        script.extend((f'(assert (>= (count sequence {tag}) 1))',
                       f'(assert (<= (window sequence {tag} {tag}) 1))'))
    context = z3.Context()
    body = z3.And(*z3.parse_smt2_string('\n'.join(script), ctx=context))
    sequence = z3.Array('sequence', z3.IntSort(context), z3.IntSort(context))
    cells = [z3.Int(f'cell_{index}', ctx=context) for index in range(200)]
    bridges = [(alias, sequence[index]) for index, alias in enumerate(cells)]
    complete = z3.And(body, *[alias == term for alias, term in bridges])
    normalized = normalize_closed_int_array_indices(complete)
    assert normalized.rewritten_index_positions == 25
    equivalent(complete, normalized.formula)
    projected = optimize_observation_projection(complete, bridges, guarded_bool_budget_ms=0)
    assert projected.eliminated_array_roots == ('sequence',)
    assert projected.retained_array_roots == ()
    assert not any(term.sort().kind() == z3.Z3_ARRAY_SORT for term in free_constants([projected.body]))
    expected = z3.And(*[
        condition for tag in range(25) for condition in (
            z3.Sum([z3.If(value == tag, 1, 0) for value in cells]) >= 1,
            z3.If(cells[tag] == tag, 1, 0) + z3.If(cells[tag + 1] == tag, 1, 0) <= 1,
        )
    ])
    equivalent(projected.body, expected)


@pytest.mark.parametrize('index', [
    lambda: z3.IntVal(-9) + 2,
    lambda: z3.IntVal(2 ** 100) + 7,
    lambda: z3.IntVal(-7) / 3,
    lambda: z3.IntVal(-7) % 3,
])
def test_negative_wide_and_native_integer_arithmetic_is_exact(index):
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    original_index = index()
    expected_index = z3.simplify(original_index)
    assert z3.is_int_value(expected_index)
    original = z3.Select(array, original_index) == 19
    result = normalize_closed_int_array_indices(original)
    assert result.rewritten_index_positions == 1
    assert result.formula.eq(z3.Select(array, expected_index) == 19)
    equivalent(original, result.formula)


def test_store_and_read_aliases_normalize_without_losing_out_of_range_cells():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    stored = z3.Store(array, z3.IntVal(-3) - 4, 9)
    original = z3.And(z3.Select(stored, z3.IntVal(-10) + 3) == 9,
                      z3.Select(array, z3.IntVal(1000) + 1) == 8)
    result = normalize_closed_int_array_indices(original)
    assert result.rewritten_index_positions == 3
    expected = z3.And(z3.Select(z3.Store(array, -7, 9), -7) == 9,
                      z3.Select(array, 1001) == 8)
    assert result.formula.eq(expected)
    equivalent(original, result.formula)


def test_symbolic_function_and_zero_divisor_indices_are_preserved():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    x = z3.Int('x')
    unknown = z3.Function('unknown', z3.IntSort(), z3.IntSort())
    indices = [x + 1, unknown(3), z3.IntVal(9) / 0, z3.IntVal(9) % 0]
    original = z3.And(*[z3.Select(array, index) == 5 for index in indices])
    result = normalize_closed_int_array_indices(original)
    assert result.rewritten_index_positions == 0
    assert result.formula.eq(original)
    alias = z3.Int('alias')
    projected = optimize_observation_projection(z3.And(original, alias == array[3]), [(alias, array[3])])
    assert projected.eliminated_array_roots == ()
    assert projected.retained_array_roots == ('array',)


def test_shared_index_arithmetic_outside_array_positions_is_not_rewritten():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    x = z3.Int('x')
    shared = z3.IntVal(1) + 2
    arithmetic_constraint = x == shared
    original = z3.And(arithmetic_constraint, z3.Select(array, shared) == x)
    result = normalize_closed_int_array_indices(original)
    assert result.rewritten_index_positions == 1
    assert result.formula.arg(0).eq(arithmetic_constraint)
    assert result.formula.arg(1).eq(z3.Select(array, 3) == x)
    equivalent(original, result.formula)


def test_closed_observation_indices_match_normalized_body_cells():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    first, second = z3.Ints('first second')
    read = array[z3.IntVal(1) + 2]
    original = z3.And(read >= 0, first == read, second == array[3])
    projected = optimize_observation_projection(original, [(first, read), (second, array[3])])
    assert projected.eliminated_array_roots == ('array',)
    assert projected.retained_array_roots == ()
    equivalent(projected.body, z3.And(first >= 0, first == second))


def test_quantifier_binders_patterns_and_annotations_remain_intact():
    array = z3.Array('array', z3.IntSort(), z3.IntSort())
    x = z3.Int('x')
    pattern = z3.Function('pattern', z3.IntSort(), z3.IntSort())
    original = z3.ForAll([x], z3.Implies(array[z3.IntVal(1) + 2] == x,
                                        array[x + 1] == pattern(x)),
                        patterns=[pattern(x)], weight=3, qid='array-index-quantifier', skid='same-binder')
    result = normalize_closed_int_array_indices(original)
    assert result.rewritten_index_positions == 1
    updated = result.formula
    assert updated.is_forall() and updated.num_vars() == original.num_vars()
    assert updated.var_name(0) == original.var_name(0)
    assert updated.var_sort(0).eq(original.var_sort(0))
    assert updated.weight() == original.weight()
    assert updated.qid() == original.qid() and updated.skolem_id() == original.skolem_id()
    assert updated.num_patterns() == original.num_patterns()
    assert updated.pattern(0).eq(original.pattern(0))
    assert updated.body().arg(1).eq(original.body().arg(1))
    equivalent(original, updated)


def test_whole_array_equality_still_blocks_array_elimination():
    left = z3.Array('left', z3.IntSort(), z3.IntSort())
    right = z3.Array('right', z3.IntSort(), z3.IntSort())
    alias = z3.Int('alias')
    original = z3.And(left == right, alias == left[z3.IntVal(1) + 2])
    projected = optimize_observation_projection(original, [(alias, left[3])])
    assert not projected.eliminated_array_roots
    assert any(term.sort().kind() == z3.Z3_ARRAY_SORT for term in free_constants([projected.body]))
