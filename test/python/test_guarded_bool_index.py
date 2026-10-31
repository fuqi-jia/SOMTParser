"""Shared guard atoms retain complete existential relation semantics."""
import pytest

z3 = pytest.importorskip("z3")

from tools.semantic_checks import guarded_bool_definitions as checker  # noqa: E402
from tools.semantic_checks.projection import existential_projection  # noqa: E402


def _assert_same_projection(left, right, visible):
    solver = z3.Solver(ctx=left.ctx)
    solver.add(z3.Xor(existential_projection(left, visible),
                     existential_projection(right, visible)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("reverse", [False, True])
def test_repeated_guard_atoms_and_duplicate_rows_preserve_all_groups(reverse):
    context = z3.Context()
    sequence = z3.Int("shared_sequence", ctx=context)
    visible = [sequence]
    clauses = [sequence >= -2, sequence <= 2]
    guards = {
        value: (z3.IntVal(value, ctx=context) == sequence if reverse
                else sequence == value)
        for value in range(-2, 3)
    }
    for group in range(4):
        bit = z3.Bool(f"shared_bit_{group}", ctx=context)
        integer = z3.Int(f"shared_integer_{group}", ctx=context)
        observation = z3.Int(f"observed_{group}", ctx=context)
        visible.append(observation)
        clauses.extend([z3.If(bit, 1, 0) == integer, integer >= 0,
                        integer <= 1, observation == integer])
        # Every group reuses the exact antecedent ASTs, while each outcome
        # recurs across several rows. Equal duplicate clauses remain legal.
        for value, guard in guards.items():
            outcome = (value + group) % 2
            equality = (z3.IntVal(outcome, ctx=context) == integer if reverse
                        else integer == outcome)
            row = z3.Implies(guard, equality)
            clauses.extend([row, row])
    body = z3.And(*clauses)
    result = checker.eliminate_guarded_bool_definitions(body)
    assert result.group_count == 4
    assert result.removed_clause_count == 4 * 8  # Five unique rows, bridge and two bounds.
    _assert_same_projection(body, result.body, visible)


def test_cached_noninteger_atoms_remain_constraints_and_do_not_complete_a_table():
    sequence = z3.Int("typed_sequence")
    real_sequence = z3.Real("typed_sequence")
    bit = z3.Bool("typed_bit")
    integer = z3.Int("typed_integer")
    real_integer = z3.Real("typed_integer")
    missing_int_guard = z3.Implies(real_sequence == 1, integer == 0)
    unrelated_outcome = z3.Implies(sequence == 1, real_integer == 0)
    body = z3.And(
        sequence >= 0, sequence <= 1, z3.If(bit, 1, 0) == integer,
        integer >= 0, integer <= 1,
        z3.Implies(sequence == 0, integer == 1),
        missing_int_guard, missing_int_guard,
        unrelated_outcome, unrelated_outcome)
    result = checker.eliminate_guarded_bool_definitions(body)
    assert result.group_count == 0
    assert result.body.eq(body)


def test_conflicting_group_does_not_poison_a_shared_guard_in_a_valid_group():
    sequence = z3.Int("mixed_sequence")
    shared_guards = [sequence == value for value in range(2)]
    clauses = [sequence >= 0, sequence <= 1]
    visible = [sequence]
    for group in range(2):
        bit = z3.Bool(f"mixed_bit_{group}")
        integer = z3.Int(f"mixed_integer_{group}")
        observed = z3.Int(f"mixed_observed_{group}")
        visible.append(observed)
        clauses.extend([z3.If(bit, 1, 0) == integer, integer >= 0,
                        integer <= 1, observed == integer,
                        z3.Implies(shared_guards[0], integer == 0),
                        z3.Implies(shared_guards[1], integer == 1)])
        if group == 1:
            clauses.append(z3.Implies(shared_guards[0], integer == 1))
    body = z3.And(*clauses)
    result = checker.eliminate_guarded_bool_definitions(body)
    assert result.group_count == 1
    _assert_same_projection(body, result.body, visible)


def test_recognition_caches_do_not_cross_contexts_or_calls():
    for truth_value in [0, 1, 0]:
        context = z3.Context()
        sequence = z3.Int("context_sequence", ctx=context)
        bit = z3.Bool("context_bit", ctx=context)
        integer = z3.Int("context_integer", ctx=context)
        observed = z3.Int("context_observed", ctx=context)
        body = z3.And(sequence >= 0, sequence <= 0,
                      z3.If(bit, 1, 0) == integer,
                      integer >= 0, integer <= 1,
                      z3.Implies(sequence == 0, integer == truth_value),
                      observed == integer)
        result = checker.eliminate_guarded_bool_definitions(body)
        assert result.group_count == 1
        _assert_same_projection(body, result.body, [sequence, observed])


@pytest.mark.parametrize("expire_at", ["clause_scan.done", "structural_proof.start"])
def test_expired_budget_rolls_back_the_entire_formula(monkeypatch, expire_at):
    sequence = z3.Int("deadline_sequence")
    bit = z3.Bool("deadline_bit")
    integer = z3.Int("deadline_integer")
    body = z3.And(sequence >= 0, sequence <= 1,
                  z3.If(bit, 1, 0) == integer, integer >= 0, integer <= 1,
                  z3.Implies(sequence == 0, integer == 1),
                  z3.Implies(sequence == 1, integer == 0))
    clock = [0.0]
    monkeypatch.setattr(checker.time, "monotonic", lambda: clock[0])

    def progress(event):
        if event["phase"] == expire_at:
            clock[0] = 0.1

    result = checker.eliminate_guarded_bool_definitions(
        body, budget_ms=50, progress_callback=progress)
    assert result.group_count == 0
    assert result.removed_clause_count == 0
    assert result.body.eq(body)
    assert "budget exhausted" in result.fallback_reason
