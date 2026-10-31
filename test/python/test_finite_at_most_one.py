"""Differential tests for the isolated finite pairwise-cardinality rewrite.

These are intended for the root agent's remote qualification. This task did
not execute them locally.
"""
import itertools

import pytest
z3 = pytest.importorskip("z3")

from tools.semantic_checks.finite_at_most_one import (
    rewrite_finite_pairwise_at_most_one,
)
from tools.semantic_checks.finite_quantifiers import expand_finite_int_quantifiers


def _formula(index_count, *, lower=0, reverse_bounds=False, reverse_order=False,
             second_upper=None, second_lower=None, include_order=True,
             extra_guard=None, outer_bool=False, fresh_collision=False,
             fresh_collision_names=(), free_function_name=None,
             second_root=False, second_pair=False, different_second_sort=False,
             leaf_sort="Int", binder_order=("row_a", "row_b", "index_a", "index_b"), ctx=None):
    ctx = ctx or z3.Context()
    row_a, row_b, index_a, index_b = [
        z3.Int(name, ctx=ctx)
        for name in ("row_a", "row_b", "index_a", "index_b")
    ]
    variables = {"row_a": row_a, "row_b": row_b,
                 "index_a": index_a, "index_b": index_b}
    element_sort = z3.IntSort(ctx=ctx) if leaf_sort == "Int" else z3.BoolSort(ctx=ctx)
    other_element_sort = (z3.BoolSort(ctx=ctx) if different_second_sort
                          and leaf_sort == "Int" else
                          z3.IntSort(ctx=ctx) if different_second_sort else element_sort)
    a = z3.Array("ArrayRoot", z3.IntSort(ctx=ctx),
                 z3.ArraySort(z3.IntSort(ctx=ctx), element_sort))
    b = z3.Array("OtherRoot", z3.IntSort(ctx=ctx),
                 z3.ArraySort(z3.IntSort(ctx=ctx), other_element_sort))
    upper = lower + index_count
    second_upper = upper if second_upper is None else second_upper
    guard = [row_a >= 0, row_a < 3, row_b >= 0, row_b < 3,
             row_a < row_b]
    if reverse_bounds:
        guard.extend([lower <= index_a, upper > index_a, second_upper > index_b])
        if include_order:
            guard.append(index_b > index_a if reverse_order else index_a < index_b)
    else:
        guard.extend([index_a >= lower, index_a < upper, index_b < second_upper])
        if include_order:
            guard.append(index_b > index_a if reverse_order else index_a < index_b)
    if second_lower is not None:
        guard.append(index_b >= second_lower)
    if outer_bool:
        guard.append(z3.Bool("outer_enabled", ctx=ctx))
    if fresh_collision:
        collision = z3.Int("pair_left!0", ctx=ctx)
        guard.append(collision == 7)
    for offset, collision_name in enumerate(fresh_collision_names):
        collision = z3.Int(collision_name, ctx=ctx)
        guard.append(collision == offset + 10)
    if free_function_name is not None:
        free_function = z3.Function(
            free_function_name, z3.IntSort(ctx=ctx), z3.BoolSort(ctx=ctx))
        guard.append(free_function(row_a))
    if extra_guard is not None:
        guard.append(extra_guard(row_a, row_b, index_a, index_b))
    first = (z3.Select(z3.Select(a, row_a), index_a)
             != z3.Select(z3.Select(a, row_b), index_a))
    second_array = b if (second_root or different_second_sort) else a
    second_row = row_a if second_pair else row_b
    second = (z3.Select(z3.Select(second_array, row_a), index_b)
              != z3.Select(z3.Select(second_array, second_row), index_b))
    body = z3.Implies(z3.And(*guard), z3.Or(first, second))
    return z3.ForAll([variables[name] for name in binder_order], body)


def _qf_expansion(formula):
    result = expand_finite_int_quantifiers(
        formula, max_enumerated_tuples=1000, max_emitted_instances=1000,
        max_ast_nodes=100000,
    )
    assert not z3.is_quantifier(result.formula)
    assert not result.stats.budget_exhausted
    assert result.stats.skipped_quantifiers == 0
    return result.formula


def _assert_equivalent_by_differential(original, rewritten):
    lhs = _qf_expansion(original)
    rhs = _qf_expansion(rewritten)
    assert lhs.ctx == rhs.ctx
    solver = z3.Solver(ctx=lhs.ctx)
    solver.set(timeout=5000)
    solver.add(z3.Xor(lhs, rhs))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("index_count", [0, 1, 2, 3])
def test_pairwise_form_matches_sum_for_small_finite_domains(index_count):
    original = _formula(index_count)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    assert result.index_lower == 0
    assert result.index_upper == index_count
    _assert_equivalent_by_differential(original, result.formula)


@pytest.mark.parametrize("lower", [-4, 3])
def test_nonzero_and_negative_finite_lower_bounds(lower):
    original = _formula(3, lower=lower)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    assert result.index_lower == lower
    assert result.index_upper == lower + 3
    _assert_equivalent_by_differential(original, result.formula)


def test_reversed_bounds_and_equivalent_order_comparison_are_supported():
    original = _formula(3, lower=-2, reverse_bounds=True, reverse_order=True)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    assert result.index_lower == -2
    assert result.index_upper == 1
    _assert_equivalent_by_differential(original, result.formula)


def _free_uninterpreted_constant_ids(expression):
    stack = [expression]
    seen = set()
    result = set()
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        if z3.is_var(node):
            continue
        if z3.is_quantifier(node):
            stack.append(node.body())
        elif z3.is_app(node):
            if (node.num_args() == 0
                    and node.decl().kind() == z3.Z3_OP_UNINTERPRETED):
                result.add(node_id)
            stack.extend(node.children())
    return result


def _uninterpreted_decl_ids(expression):
    stack = [expression]
    seen = set()
    result = set()
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        if z3.is_var(node):
            continue
        if z3.is_quantifier(node):
            stack.append(node.body())
        elif z3.is_app(node):
            if node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                result.add(node.decl().get_id())
            stack.extend(node.children())
    return result


def test_outer_free_boolean_guard_is_preserved():
    original = _formula(3, outer_bool=True)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    before = _free_uninterpreted_constant_ids(original)
    after = _free_uninterpreted_constant_ids(result.formula)
    assert z3.Bool("outer_enabled", ctx=original.ctx).get_id() in before
    assert before.issubset(after)
    _assert_equivalent_by_differential(original, result.formula)


def test_fresh_row_constants_do_not_capture_existing_free_symbol_names():
    original = _formula(3, fresh_collision=True)
    collision = z3.Int("pair_left!0", ctx=original.ctx)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    assert collision.get_id() in _free_uninterpreted_constant_ids(result.formula)
    _assert_equivalent_by_differential(original, result.formula)


def test_multiple_consecutive_fresh_name_collisions_remain_free():
    names = (
        "pair_left!0", "pair_left!1", "pair_left!2",
        "pair_right!0", "pair_right!1",
    )
    original = _formula(3, fresh_collision_names=names)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    after = _free_uninterpreted_constant_ids(result.formula)
    assert all(z3.Int(name, ctx=original.ctx).get_id() in after for name in names)
    _assert_equivalent_by_differential(original, result.formula)


def test_free_function_declaration_name_is_reserved_from_binders():
    function_name = "pair_left!0"
    original = _formula(3, free_function_name=function_name)
    function_decl = z3.Function(
        function_name, z3.IntSort(ctx=original.ctx), z3.BoolSort(ctx=original.ctx))
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    assert function_decl.get_id() in _uninterpreted_decl_ids(result.formula)
    _assert_equivalent_by_differential(original, result.formula)


def test_boolean_array_elements_are_supported_by_the_same_exact_rule():
    original = _formula(3, leaf_sort="Bool")
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    _assert_equivalent_by_differential(original, result.formula)


def test_different_array_element_sorts_are_rejected():
    original = _formula(3, different_second_sort=True)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert not result.rewritten
    assert result.formula.eq(original)


def test_rewrite_uses_bound_indices_not_binder_names_or_order():
    original = _formula(3, binder_order=("index_b", "row_a", "index_a", "row_b"))
    result = rewrite_finite_pairwise_at_most_one(original)
    assert result.rewritten, result.reason
    _assert_equivalent_by_differential(original, result.formula)


@pytest.mark.parametrize("index_count", [0, 1, 2, 3])
def test_at_most_one_combinatorial_witness_matrix(index_count):
    # Guard the core finite-set lemma independently of solver behavior.
    for values in itertools.product((False, True), repeat=index_count):
        pairwise = all(not (values[i] and values[j])
                       for i in range(index_count)
                       for j in range(i + 1, index_count))
        counted = sum(values) <= 1
        assert pairwise == counted


@pytest.mark.parametrize(
    "kwargs",
    [
        {"extra_guard": lambda a, b, i, j: i != 1},
        {"extra_guard": lambda a, b, i, j: z3.Or(i == 0, i == 2)},
        {"second_root": True},
        {"second_pair": True},
        {"second_upper": 4},
        {"second_lower": 0},
        {"include_order": False},
    ],
)
def test_unsupported_index_or_read_shapes_are_preserved(kwargs):
    original = _formula(3, **kwargs)
    result = rewrite_finite_pairwise_at_most_one(original)
    assert not result.rewritten
    assert result.formula.eq(original)
    assert result.reason


@pytest.mark.parametrize(
    "limits",
    [
        {"max_week_terms": 2},
        {"max_generated_nodes": 1},
    ],
)
def test_budget_refusal_returns_the_original_formula(limits):
    original = _formula(3)
    result = rewrite_finite_pairwise_at_most_one(original, **limits)
    assert not result.rewritten
    assert result.formula.eq(original)
    assert "budget" in result.reason


def test_nested_quantifier_is_refused():
    original = _formula(2)
    p = z3.Int("nested_p", ctx=original.ctx)
    nested = z3.ForAll([p], p == p)
    # Place the nested quantifier into an additional guard conjunct.
    body = original.body()
    guard = z3.And(body.arg(0), nested)
    wrapped = z3.ForAll(
        [z3.Int("row_a0", ctx=original.ctx), z3.Int("row_b0", ctx=original.ctx),
         z3.Int("index_a0", ctx=original.ctx), z3.Int("index_b0", ctx=original.ctx)],
        z3.Implies(guard, body.arg(1)),
    )
    result = rewrite_finite_pairwise_at_most_one(wrapped)
    assert not result.rewritten
    assert result.formula.eq(wrapped)


def test_outer_debruijn_reference_is_refused_without_capture():
    ctx = z3.Context()
    outer = z3.Int("outer", ctx=ctx)
    inner = _formula(
        2, ctx=ctx,
        extra_guard=lambda a, b, i, j: outer >= 0,
    )
    referenced = z3.ForAll([outer], inner)
    inner_quantifier = referenced.body()
    result = rewrite_finite_pairwise_at_most_one(inner_quantifier)
    assert not result.rewritten
    assert result.formula.eq(inner_quantifier)
