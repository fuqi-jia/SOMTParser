"""Finite-trace semantics of shared hierarchy frontiers and length pruning."""
from itertools import product

import pytest
import somtparser as sp
import z3


def encode(tmp_path, body, network, horizon, depth=1, goal="(and)", initial=""):
    domain = ("(define (domain d) (:requirements :adl :hierarchy :htn-method-pre-eff) "
              "(:predicates (done) (ready)) " + body + ")")
    problem = tmp_path / "problem.hddl"
    problem.write_text("(define (problem p) (:domain d) (:htn " + network + ") "
                       "(:init " + initial + ") (:goal " + goal + "))")
    result = sp.translate(source=domain, language="hddl", data=[str(problem)], profile="bmc",
                          options={"plan_horizon": str(horizon), "decomposition_depth": str(depth)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=context))
    return context, solver


@pytest.mark.parametrize("horizon", [0, 1, 2, 3])
def test_shared_alternatives_match_independent_concatenated_trace_language(tmp_path, horizon):
    body = ("(:task t) (:method empty :task (t)) "
            "(:method one :task (t) :subtasks (a)) "
            "(:method two :task (t) :ordered-subtasks (and (a) (b))) "
            "(:action a :effect (and)) (:action b :effect (and))")
    context, solver = encode(tmp_path, body, ":ordered-subtasks (and (t) (t) (t))", horizon)
    # Independent source language: each occurrence contributes epsilon, a, or ab.
    words = {sum(parts, ()) for parts in product([(), ("a",), ("a", "b")], repeat=3)}
    expected = {word + ("noop",) * (horizon-len(word)) for word in words if len(word) <= horizon}
    declared = set()
    pending = list(solver.assertions())
    seen = set()
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if z3.is_const(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            declared.add(term.decl().name())
        pending.extend(term.children())
    for trace in product(["a", "b", "noop"], repeat=horizon):
        names = [f"__pddl_noop@{step}" if action == "noop" else f"do_{action}@{step}"
                 for step, action in enumerate(trace)]
        # Actions eliminated from every bounded frontier have no target symbol;
        # declaring a fresh Boolean would create a counterfeit trace witness.
        if any(name not in declared for name in names):
            assert trace not in expected, trace
            continue
        solver.push()
        solver.add(*[z3.Bool(name, ctx=context) for name in names])
        assert str(solver.check()) == ("sat" if trace in expected else "unsat"), trace
        solver.pop()


@pytest.mark.parametrize("depth,expected", [(1,"unsat"), (2,"sat"), (3,"sat")])
def test_nested_shared_cache_preserves_decomposition_depth(tmp_path, depth, expected):
    body = ("(:task t) (:task child) (:method wrapper :task (t) :subtasks (child)) "
            "(:method leaf :task (child) :subtasks (a)) (:action a :effect (done))")
    _, solver = encode(tmp_path, body, ":ordered-subtasks (and (t) (t))", 2, depth=depth, goal="(done)")
    assert str(solver.check()) == expected


@pytest.mark.parametrize("ready,expected", [(False,"unsat"), (True,"sat")])
def test_zero_primitive_method_events_remain_in_frontiers(tmp_path, ready, expected):
    body = ("(:task t) (:method state :task (t) :precondition (ready) :effect (done))")
    _, solver = encode(tmp_path, body, ":ordered-subtasks (and (t) (t) (t))", 0,
                       goal="(done)", initial="(ready)" if ready else "")
    assert str(solver.check()) == expected


def test_overlong_cartesian_branches_are_cut_before_materialization(tmp_path):
    # 2^24 combinations but only epsilon or one primitive fit the unchanged
    # horizon. There is no timing assertion and no reduction of either bound.
    body = ("(:task t) (:method empty :task (t)) "
            "(:method one :task (t) :subtasks (a)) (:action a :effect (done))")
    tasks = " ".join("(t)" for _ in range(24))
    _, solver = encode(tmp_path, body, ":ordered-subtasks (and " + tasks + ")", 1, goal="(done)")
    assert str(solver.check()) == "sat"
