import pytest

z3 = pytest.importorskip("z3")

from tools.semantic_checks.guarded_bool_definitions import (  # noqa: E402
    eliminate_guarded_bool_definitions,
)
from tools.semantic_checks.projection import existential_projection  # noqa: E402


def _group(sequence, bit, integer):
    return [
        z3.If(bit, 1, 0) == integer,
        integer >= 0,
        integer <= 1,
        z3.Implies(sequence == 0, integer == 1),
        z3.Implies(sequence == 1, integer == 0),
        z3.Implies(sequence == 2, integer == 1),
    ]


def _check_xor_unsat(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_exact_guarded_bool_and_int_pair_is_eliminated_with_extra_use():
    sequence = z3.Int("sequence")
    bit = z3.Bool("setup")
    integer = z3.Int("IV")
    extra = z3.Int("extra")
    clauses = [sequence >= 0, sequence <= 2, *_group(sequence, bit, integer),
               z3.Implies(bit, extra == 9)]
    body = z3.And(*clauses)
    progress = []
    result = eliminate_guarded_bool_definitions(
        body, progress_callback=progress.append)
    assert result.group_count == 1
    assert result.removed_clause_count == 6
    assert not result.fallback_reason
    assert any(event["phase"] == "groups.recognized" for event in progress)
    assert result.proof_kind == "structural"
    assert any(event["phase"] == "structural_proof.done" for event in progress)
    assert not any("query" in event["phase"] for event in progress)
    assert not any(z3.eq(c, bit) or z3.eq(c, integer)
                   for c in result.body.children())
    original_projection = existential_projection(body, [sequence, extra])
    optimized_projection = existential_projection(result.body, [sequence, extra])
    _check_xor_unsat(original_projection, optimized_projection)


def test_independent_guard_groups_are_proved_separately_and_preserve_projection():
    sequence = z3.Int("multi_sequence")
    clauses = [sequence >= 0, sequence <= 2]
    visible = [sequence]
    for suffix, truth_values in (("a", {0, 2}), ("b", {1})):
        bit = z3.Bool(f"multi_setup_{suffix}")
        integer = z3.Int(f"multi_IV_{suffix}")
        clauses.extend((z3.If(bit, 1, 0) == integer,
                        integer >= 0, integer <= 1))
        clauses.extend(
            z3.Implies(sequence == value,
                        integer == (1 if value in truth_values else 0))
            for value in range(3))
    body = z3.And(*clauses)

    result = eliminate_guarded_bool_definitions(body)

    assert result.group_count == 2
    assert not result.fallback_reason
    assert result.proof_phase == "complete"
    _projection_xor_is_unsat(body, result.body, visible)


def test_incomplete_guard_coverage_falls_back():
    sequence = z3.Int("gap_sequence")
    bit = z3.Bool("gap_setup")
    integer = z3.Int("gap_IV")
    body = z3.And(
        sequence >= 0, sequence <= 2,
        z3.If(bit, 1, 0) == integer,
        z3.Implies(sequence == 0, integer == 1),
        z3.Implies(sequence == 1, integer == 0),
        integer >= 0, integer <= 1,
    )
    result = eliminate_guarded_bool_definitions(body)
    assert result.group_count == 0
    assert result.body.eq(body)


def test_conflicting_guard_table_falls_back():
    sequence = z3.Int("conflict_sequence")
    bit = z3.Bool("conflict_setup")
    integer = z3.Int("conflict_IV")
    body = z3.And(
        sequence >= 0, sequence <= 1,
        z3.If(bit, 1, 0) == integer,
        z3.Implies(sequence == 0, integer == 1),
        z3.Implies(sequence == 0, integer == 0),
        z3.Implies(sequence == 1, integer == 0),
        integer >= 0, integer <= 1,
    )
    result = eliminate_guarded_bool_definitions(body)
    assert result.group_count == 0
    assert result.body.eq(body)


def test_inconsistent_bounds_fall_back_instead_of_vacuous_proof():
    sequence = z3.Int("empty_sequence")
    bit = z3.Bool("empty_setup")
    integer = z3.Int("empty_IV")
    body = z3.And(
        sequence >= 2, sequence <= 1,
        *_group(sequence, bit, integer),
    )
    result = eliminate_guarded_bool_definitions(body)
    assert result.group_count == 0
    assert result.body.eq(body)


def test_int_bounds_that_restrict_a_table_bit_prevent_elimination():
    sequence = z3.Int("restricted_sequence")
    bit = z3.Bool("restricted_setup")
    integer = z3.Int("restricted_IV")
    body = z3.And(
        sequence >= 0, sequence <= 2,
        z3.If(bit, 1, 0) == integer,
        z3.Implies(sequence == 0, integer == 1),
        z3.Implies(sequence == 1, integer == 0),
        z3.Implies(sequence == 2, integer == 1),
        integer >= 0, integer <= 0)

    result = eliminate_guarded_bool_definitions(body)

    assert result.group_count == 0
    assert result.body.eq(body)
    assert result.proof_kind == "structural"
    assert "not universally true" in result.fallback_reason


def test_same_spelling_different_sort_constants_keep_distinct_bounds():
    sequence = z3.Int("same_spelling_sequence")
    bit = z3.Bool("same_spelling_setup")
    integer = z3.Int("same_spelling_aux")
    real = z3.Real("same_spelling_aux")
    real_bound = real >= 10
    body = z3.And(sequence >= 0, sequence <= 2,
                  *_group(sequence, bit, integer), real_bound)

    result = eliminate_guarded_bool_definitions(body)

    assert result.group_count == 1
    assert result.proof_kind == "structural"
    assert any(clause.eq(real_bound) for clause in result.body.children())
    _projection_xor_is_unsat(body, result.body, [sequence, real])


def test_zero_proof_budget_is_exact_noop():
    sequence = z3.Int("budget_sequence")
    bit = z3.Bool("budget_setup")
    integer = z3.Int("budget_IV")
    body = z3.And(sequence >= 0, sequence <= 2,
                  *_group(sequence, bit, integer))
    result = eliminate_guarded_bool_definitions(body, budget_ms=0)
    assert result.group_count == 0
    assert result.body.eq(body)


def _projection_xor_is_unsat(left, right, visible):
    left_projection = existential_projection(left, visible)
    right_projection = existential_projection(right, visible)
    _check_xor_unsat(left_projection, right_projection)


def test_observable_bridge_survives_auxiliary_substitution():
    sequence = z3.Int("bridge_sequence")
    bit = z3.Bool("bridge_setup")
    integer = z3.Int("bridge_IV")
    observed = z3.Bool("bridge_observed")
    extra = z3.Int("bridge_extra")
    body = z3.And(
        sequence >= 0, sequence <= 2, *_group(sequence, bit, integer),
        observed == bit, z3.Implies(bit, extra == 9))

    result = eliminate_guarded_bool_definitions(body)
    assert result.group_count == 1
    observed_bridge = next(
        c for c in result.body.children()
        if z3.is_eq(c) and any(z3.eq(term, observed) for term in c.children()))
    assert "bridge_observed" in str(observed_bridge)
    assert "bridge_sequence" in str(observed_bridge)
    _projection_xor_is_unsat(body, result.body, [sequence, observed, extra])


def test_chained_guard_groups_fall_back_without_changing_projection():
    sequence = z3.Int("chain_sequence")
    bit_a, bit_b = z3.Bools("chain_setup_a chain_setup_b")
    iv_a, iv_b = z3.Ints("chain_IV_a chain_IV_b")
    body = z3.And(
        sequence >= 0, sequence <= 1,
        z3.If(bit_a, 1, 0) == iv_a,
        z3.Implies(iv_b == 0, iv_a == 1),
        z3.Implies(iv_b == 1, iv_a == 0),
        iv_a >= 0, iv_a <= 1,
        z3.If(bit_b, 1, 0) == iv_b,
        z3.Implies(sequence == 0, iv_b == 1),
        z3.Implies(sequence == 1, iv_b == 0),
        iv_b >= 0, iv_b <= 1)

    result = eliminate_guarded_bool_definitions(body)
    assert result.group_count == 0
    assert "depend on eliminated auxiliaries" in result.fallback_reason
    assert result.body.eq(body)
    _projection_xor_is_unsat(body, result.body, [sequence])


def test_cyclic_guard_groups_fall_back_without_changing_projection():
    bit_a, bit_b = z3.Bools("cycle_setup_a cycle_setup_b")
    iv_a, iv_b = z3.Ints("cycle_IV_a cycle_IV_b")
    body = z3.And(
        z3.If(bit_a, 1, 0) == iv_a,
        z3.Implies(iv_b == 0, iv_a == 1),
        z3.Implies(iv_b == 1, iv_a == 0),
        iv_a >= 0, iv_a <= 1,
        z3.If(bit_b, 1, 0) == iv_b,
        z3.Implies(iv_a == 0, iv_b == 1),
        z3.Implies(iv_a == 1, iv_b == 0),
        iv_b >= 0, iv_b <= 1)

    result = eliminate_guarded_bool_definitions(body)
    assert result.group_count == 0
    assert "depend on eliminated auxiliaries" in result.fallback_reason
    assert result.body.eq(body)
    _projection_xor_is_unsat(body, result.body, [])


def test_projection_reports_configured_guard_proof_budget():
    sequence = z3.Int("configured_budget_sequence")
    bit = z3.Bool("configured_budget_setup")
    integer = z3.Int("configured_budget_IV")
    body = z3.And(sequence >= 0, sequence <= 2,
                  *_group(sequence, bit, integer))
    from tools.semantic_checks.projection import optimize_observation_projection

    result = optimize_observation_projection(
        body, [], guarded_bool_budget_ms=0)
    assert result.guarded_bool_budget_ms == 0
    assert result.guarded_bool_groups == 0
    assert result.guarded_bool_fallback_reason == "disabled or non-conjunctive body"
