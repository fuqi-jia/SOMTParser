"""Exact AST differentials and counted work for the no-index-change fast path."""
from pathlib import Path
import json
import os
import time

import pytest
import z3

from tools.semantic_checks import closed_array_indices as candidate

EVIDENCE = Path(os.environ["PROJECTION_EVIDENCE"]) if os.environ.get("PROJECTION_EVIDENCE") else None
if EVIDENCE is not None:
    EVIDENCE.mkdir(exist_ok=True)


def record(name, data):
    if EVIDENCE is not None:
        (EVIDENCE / (name + ".json")).write_text(json.dumps(data, indent=2) + "\n")


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def measured(module, body, monkeypatch):
    original_wrap = z3.z3._to_expr_ref
    original_arg = z3.Z3_get_app_arg
    counts = dict(python_expression_wrappings=0, native_child_accesses=0)

    def wrap(*args, **kwargs):
        counts["python_expression_wrappings"] += 1
        return original_wrap(*args, **kwargs)

    def argument(*args, **kwargs):
        counts["native_child_accesses"] += 1
        return original_arg(*args, **kwargs)

    with monkeypatch.context() as scope:
        scope.setattr(z3.z3, "_to_expr_ref", wrap)
        scope.setattr(z3, "Z3_get_app_arg", argument)
        scope.setattr(z3.z3, "Z3_get_app_arg", argument)
        started = time.perf_counter()
        result = module.normalize_closed_int_array_indices(body)
        counts["wall_seconds"] = time.perf_counter() - started
    return result, counts


@pytest.mark.parametrize("size", [32, 256, 2100])
def test_scalar_bool_int_real_dag_has_one_native_scan_and_no_child_wrappers(size, monkeypatch):
    values = [z3.Int(f"scalar_{size}_{i}") for i in range(size)]
    flags = [z3.Bool(f"flag_{size}_{i}") for i in range(size)]
    shared = z3.Sum(values)
    body = z3.And(*[z3.And(flag == (value >= 0), z3.Implies(flag, shared >= value))
                    for value, flag in zip(values, flags)], z3.ToReal(shared) / 3 >= -2)
    new, new_counts = measured(candidate, body, monkeypatch)
    assert new.formula is body
    assert new.rewritten_index_positions == 0
    equivalent(new.formula, body)
    assert new_counts["python_expression_wrappings"] == 0
    record(f"scalar-dag-{size}", dict(size=size, candidate=new_counts,
        source_ast_preserved=True, complete_relation_xor="unsat"))


def test_2100_nested_array_cells_with_numeral_indices_preserve_exact_ast(monkeypatch):
    board = z3.Array("board35x60", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    body = z3.And(*[z3.And(board[r][c] >= 0, board[r][c] <= 1)
                    for r in range(35) for c in range(60)])
    new, new_counts = measured(candidate, body, monkeypatch)
    assert new.formula is body
    assert new.rewritten_index_positions == 0
    equivalent(new.formula, body)
    assert new_counts["python_expression_wrappings"] == 0
    record("nested-array-2100", dict(cells=2100, candidate=new_counts,
        source_ast_preserved=True, complete_relation_xor="unsat"))


@pytest.mark.parametrize("operator", ["add", "sub", "mul", "negative", "div", "mod", "rem"])
def test_every_supported_arithmetic_operator_uses_original_exact_rewriter(operator):
    # Use SMT input for rem so no host-language remainder convention enters.
    expressions = {"add": "(+ 1 2)", "sub": "(- 1 9)", "mul": "(* 3 7)",
                   "negative": "(- 8)", "div": "(div (- 7) 3)",
                   "mod": "(mod (- 7) 3)", "rem": "(rem (- 7) 3)"}
    body = z3.And(*z3.parse_smt2_string("(declare-const a (Array Int Int))"
        f"(assert (= (select a {expressions[operator]}) 17))"))
    assert candidate._may_have_closed_arithmetic_index(body)
    new = candidate.normalize_closed_int_array_indices(body)
    assert new.rewritten_index_positions == 1
    equivalent(new.formula, body)


@pytest.mark.parametrize("mode", ["symbolic", "zero-divisor", "function", "real", "bitvector"])
def test_nonclosed_and_noninteger_indices_are_never_changed(mode):
    if mode == "real":
        array = z3.Array("real_index", z3.RealSort(), z3.IntSort())
        index = z3.RealVal(1) + z3.RealVal("1/3")
    elif mode == "bitvector":
        array = z3.Array("bv_index", z3.BitVecSort(8), z3.IntSort())
        index = z3.BitVecVal(1, 8) + z3.BitVecVal(2, 8)
    else:
        array = z3.Array("nonclosed_index", z3.IntSort(), z3.IntSort())
        index = {"symbolic": z3.Int("dynamic") + 1, "zero-divisor": z3.IntVal(7) / 0,
                 "function": z3.Function("index_fn", z3.IntSort(), z3.IntSort())(3)}[mode]
    body = array[index] == 17
    new = candidate.normalize_closed_int_array_indices(body)
    assert new.rewritten_index_positions == 0
    assert new.formula.eq(body)


def test_nested_indices_store_value_and_unrelated_arithmetic_preserve_positions():
    a, b = [z3.Array(name, z3.IntSort(), z3.IntSort())
            for name in ("nested_index_a", "nested_index_b")]
    shared = z3.IntVal(3) + 4
    # Even though a's outer index is not arithmetic, b's inner index is; the
    # native scan must visit it and activate the exact fallback.
    body = z3.And(a[b[shared]] == 8, z3.Store(a, shared, shared)[7] == shared)
    assert candidate._may_have_closed_arithmetic_index(body)
    new = candidate.normalize_closed_int_array_indices(body)
    expected = z3.And(a[b[7]] == 8, z3.Store(a, 7, shared)[7] == shared)
    assert new.rewritten_index_positions == 2
    assert new.formula.eq(expected)
    equivalent(body, new.formula)


def test_nondefault_context_quantifier_body_and_annotations_remain_unchanged():
    ctx = z3.Context()
    a = z3.Array("ctx_a", z3.IntSort(ctx), z3.IntSort(ctx))
    bound = z3.Int("bound", ctx)
    pattern = z3.Function("ctx_pattern", z3.IntSort(ctx), z3.IntSort(ctx))
    for index in [z3.IntVal(4, ctx), z3.IntVal(1, ctx) + 3]:
        body = z3.ForAll([bound], z3.Implies(a[index] == bound, a[bound] == pattern(bound)),
                        patterns=[pattern(bound)], weight=7, qid="native-scan", skid="original-binder")
        new = candidate.normalize_closed_int_array_indices(body)
        assert new.rewritten_index_positions == (0 if z3.is_int_value(index) else 1)
        assert new.formula.qid() == body.qid()
        assert new.formula.skolem_id() == body.skolem_id()
        assert new.formula.weight() == 7
        assert new.formula.pattern(0).eq(body.pattern(0))
        equivalent(body, new.formula)


def test_shared_subterm_beneath_all_boolean_connectives_is_fully_traversed():
    a = z3.Array("connective_array", z3.IntSort(), z3.IntSort())
    x = z3.Int("connective_x")
    atom = a[z3.IntVal(1) + 2] == x
    flag = z3.Bool("connective_flag")
    body = z3.And(z3.Not(atom), z3.Or(flag, atom), z3.Implies(flag, atom),
                  z3.If(flag, atom, z3.Not(atom)))
    new = candidate.normalize_closed_int_array_indices(body)
    assert new.rewritten_index_positions == 1
    equivalent(body, new.formula)


def test_native_multidomain_array_indices_remain_independent():
    array = z3.Array("multidomain", z3.IntSort(), z3.RealSort(), z3.IntSort())
    integer_index = z3.IntVal(2) + 3
    real_index = z3.RealVal(2) + z3.RealVal("1/2")
    body = z3.Select(z3.Store(array, integer_index, real_index, 9), integer_index, real_index) == 9
    new = candidate.normalize_closed_int_array_indices(body)
    assert new.rewritten_index_positions == 2
    assert new.formula.eq(z3.Select(z3.Store(array, 5, real_index, 9), 5, real_index) == 9)
    equivalent(body, new.formula)
