"""Object binding filters preserve method-state and lexical-scope semantics."""

import pytest
import somtparser as sp
import z3


def translate(tmp_path, condition, arguments="a b", initial="", prepare=False):
    domain = ("(define (domain d) "
              "(:requirements :hierarchy :typing :method-preconditions :equality "
              " :negative-preconditions :disjunctive-preconditions "
              " :existential-preconditions) "
              "(:types item) (:constants a b - item) (:predicates (ready ?x - item) (done)) "
              "(:task gate :parameters (?x ?y - item)) "
              "(:method m :parameters (?x ?y - item) :task (gate ?x ?y) "
              f":precondition {condition} :ordered-subtasks (finish)) "
              "(:action finish :parameters () :effect (done)) "
              "(:action prepare :parameters () :effect (ready a)))")
    tasks = f"(and (prepare) (gate {arguments}))" if prepare else f"(gate {arguments})"
    problem = ("(define (problem p) (:domain d) "
               f"(:htn :ordered-subtasks {tasks}) (:init {initial}) (:goal (done)))")
    path = tmp_path / "problem.hddl"
    path.write_text(problem)
    return sp.translate(source=domain, data=[str(path)], language="hddl", profile="bmc",
                        options={"plan_horizon": "2" if prepare else "1",
                                 "decomposition_depth": "1"})


def status(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=context))
    return solver.check()


@pytest.mark.parametrize("condition,arguments,initial,expected", [
    ("(= ?x ?y)", "a a", "", z3.sat),
    ("(= ?x ?y)", "a b", "", z3.unsat),
    ("(not (= ?x ?y))", "a b", "", z3.sat),
    ("(not (= ?x ?y))", "a a", "", z3.unsat),
    ("(and (= ?x ?y) (ready ?x))", "a a", "(ready a)", z3.sat),
    ("(and (= ?x ?y) (ready ?x))", "a a", "", z3.unsat),
    ("(or (= ?x ?y) (ready ?x))", "a b", "(ready a)", z3.sat),
    ("(not (and (= ?x ?y) (ready ?x)))", "a b", "", z3.sat),
    ("(exists (?x - item) (= ?x ?y))", "a b", "", z3.sat),
])
def test_only_mandatory_unquantified_equalities_filter_bindings(
    tmp_path, condition, arguments, initial, expected
):
    assert status(translate(tmp_path, condition, arguments, initial)) == expected


def test_dynamic_condition_is_checked_after_the_preceding_action(tmp_path):
    result = translate(tmp_path, "(and (= ?x ?y) (ready ?x))", "a a", prepare=True)
    assert status(result) == z3.sat


def test_false_equality_does_not_hide_an_invalid_state_condition(tmp_path):
    result = translate(tmp_path, "(and (= ?x ?y) (undeclared))", "a b")
    assert not result.ok
    assert any("undeclared" in d.message for d in result.diagnostic_items)


def test_false_head_equality_precedes_local_cartesian_expansion(tmp_path):
    objects = " ".join(f"c{i}" for i in range(32))
    domain = ("(define (domain d) "
              "(:requirements :hierarchy :method-preconditions :equality) "
              f"(:constants a b {objects}) (:predicates (done)) "
              "(:task t :parameters (?x ?y)) "
              "(:method impossible :parameters (?x ?y ?u ?v ?w ?r ?s ?q) "
              ":task (t ?x ?y) :precondition (= ?x ?y) :subtasks (finish)) "
              "(:method possible :parameters (?x ?y) "
              ":task (t ?x ?y) :subtasks (finish)) "
              "(:action finish :parameters () :effect (done)))")
    problem = ("(define (problem p) (:domain d) "
               "(:htn :subtasks (t a b)) (:init) (:goal (done)))")
    path = tmp_path / "wide.hddl"
    path.write_text(problem)
    result = sp.translate(source=domain, data=[str(path)], language="hddl", profile="bmc",
                          options={"plan_horizon": "1", "decomposition_depth": "1"})
    assert status(result) == z3.sat
