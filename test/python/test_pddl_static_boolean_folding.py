"""Whole bounded relations remain exact after folding static Bool conditions."""
from fractions import Fraction
from itertools import product

import pytest
import somtparser as sp
import z3
from z3.z3util import get_vars


DOMAIN = """(define (domain d)
 (:requirements :adl :action-costs)
 (:types item empty)
 (:constants a b - item)
 (:predicates (static ?x - item) (ready) (done) (flag))
 (:functions (total-cost) - number)
 (:action a
  :precondition (and (static a) (= a a) (not (= a b))
                     (or (static b) (ready)) (not (flag)))
  :effect (and
   (when (static a) (done))
   (when (not (static b)) (not (done)))
   (when (and (= a b) (ready)) (flag))
   (when (ready) (flag))
   (not (ready))
   (when (= a a) (increase (total-cost) 1.5))
   (when (= a b) (increase (total-cost) 99))))
 (:action b
  :precondition (imply (static b) (not (ready)))
  :effect (and (ready) (when (flag) (not (flag)))
               (increase (total-cost) 0.25))))"""

GOAL = """(and
 (forall (?x - item) (or (= ?x a) (= ?x b)))
 (forall (?x - empty) (static a))
 (not (exists (?x - empty) (static b)))
 (imply (= a b) (ready)))"""


def encode(tmp_path, initial, horizon, domain=DOMAIN, goal=GOAL):
    path = tmp_path / "problem.pddl"
    costs = "(= (total-cost) 2) " if "(:functions" in domain else ""
    metric = " (:metric minimize (total-cost))" if costs else ""
    path.write_text("(define (problem p) (:domain d) (:init (static a) "
                    + costs + " ".join(f"({name})" for name in sorted(initial))
                    + ") (:goal " + goal + ")" + metric + ")")
    return sp.translate(source=domain, data=[str(path)], language="pddl", profile="bmc",
                        options={"plan_horizon": str(horizon)})


def independent_relation(result, initial, horizon, mutation=None):
    """Enumerate source traces, including all intermediate states and costs."""
    alternatives = []
    for trace in product(("a", "b", "noop"), repeat=horizon):
        ready, done, flag = (name in initial for name in ("ready", "done", "flag"))
        states = [(ready, done, flag)]
        costs = [Fraction(2)]
        padded = False
        valid = True
        for action in trace:
            if padded and action != "noop":
                valid = False
                break
            if action == "a":
                if not ready or flag:
                    valid = False
                    break
                # The static true add and delete both fire: addition wins.
                # Its dynamic guard observes ready before the simultaneous delete.
                ready, done, flag = False, mutation != "delete-wins", mutation != "new-state-guard"
                costs.append(costs[-1] + (Fraction(201, 2) if mutation == "false-cost-guard" else Fraction(3, 2)))
            elif action == "b":
                ready, flag = True, False
                costs.append(costs[-1] + Fraction(1, 4))
            else:
                padded = True
                costs.append(costs[-1])
            states.append((ready, done, flag))
        if not valid:
            continue
        terms = []
        for step, state in enumerate(states):
            for name, value in zip(("ready", "done", "flag"), state):
                symbol = f"{name}@{step}"
                if result.parser.is_declared_variable(symbol):
                    terms.append(z3.Bool(symbol) == value)
            terms.append(z3.Real(f"__pddl_total_cost@{step}") == z3.RealVal(str(costs[step])))
        for step, selected in enumerate(trace):
            for action in ("a", "b", "noop"):
                symbol = f"__pddl_noop@{step}" if action == "noop" else f"do_{action}@{step}"
                declared = result.parser.is_declared_variable(symbol)
                # Reachability may omit choices, but never an enabled source trace.
                if action == selected:
                    assert declared, (initial, trace, symbol)
                if declared:
                    terms.append(z3.Bool(symbol) == (action == selected))
        alternatives.append(z3.And(*terms))
    return z3.Or(*alternatives)


def parsed_relation(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    actual = z3.And(*target.assertions())
    auxiliaries = [value for value in get_vars(actual)
                   if str(value.decl().name()).startswith("__pddl_choice_prefix@")]
    # Exactly-one prefix witnesses are target-only and have unique extensions.
    if auxiliaries:
        actual = z3.Exists(auxiliaries, actual)
    return target, actual


@pytest.mark.parametrize("bits", list(product((False, True), repeat=3)))
@pytest.mark.parametrize("horizon", (0, 1, 2))
def test_complete_feasible_cost_relation_matches_independent_source_traces(tmp_path, bits, horizon):
    initial = {name for name, value in zip(("ready", "done", "flag"), bits) if value}
    result = encode(tmp_path, initial, horizon)
    target, actual = parsed_relation(result)
    reference = independent_relation(result, initial, horizon)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, reference))
    assert solver.check() == z3.unsat, (bits, horizon)
    assert len(target.objectives()) == 1
    objective = z3.Solver()
    objective.add(reference, target.objectives()[0] != z3.Real(f"__pddl_total_cost@{horizon}"))
    assert objective.check() == z3.unsat


@pytest.mark.parametrize("mutation", ("delete-wins", "new-state-guard", "false-cost-guard"))
def test_independent_relation_detects_effect_and_cost_mutations(tmp_path, mutation):
    initial = {"ready"}
    result = encode(tmp_path, initial, 1)
    _, actual = parsed_relation(result)
    wrong = independent_relation(result, initial, 1, mutation)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, wrong))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("condition,effect,goal", [
    ("(and (= a b) (undeclared))", "(done)", "(and)"),
    ("(or (= a a) (undeclared))", "(done)", "(and)"),
    ("(imply (= a b) (undeclared))", "(done)", "(and)"),
    ("(and)", "(when (= a b) (undeclared))", "(and)"),
    ("(and)", "(forall (?x - empty) (undeclared))", "(and)"),
    ("(and)", "(done)", "(or (= a a) (undeclared))"),
])
def test_static_absorption_never_hides_invalid_source(tmp_path, condition, effect, goal):
    domain = ("(define (domain d) (:requirements :adl) (:types item empty) "
              "(:constants a b - item) (:predicates (static ?x - item) (done)) "
              f"(:action act :precondition {condition} :effect {effect}))")
    result = encode(tmp_path, set(), 1, domain, goal)
    assert not result.ok
    assert any("undeclared" in diagnostic.message for diagnostic in result.diagnostic_items)


@pytest.mark.parametrize("condition,enabled", [
    ("(forall (?x - item) (= ?x a))", False),
    ("(exists (?x - empty) (= ?x a))", False),
    ("(forall (?x - item) (or (= ?x a) (= ?x b)))", True),
])
def test_hierarchy_selected_constant_condition_keeps_the_complete_relation(tmp_path, condition, enabled):
    # The hierarchy retains this primitive even when its quantified condition
    # is false. That exercises skipping effects after a false grounded condition.
    domain = ("(define (domain d) (:requirements :adl :hierarchy) "
              "(:types item empty) (:constants a b - item) (:predicates (done)) "
              f"(:action act :precondition {condition} :effect (done)))")
    path = tmp_path / "problem.hddl"
    path.write_text("(define (problem p) (:domain d) (:htn :subtasks (act)) "
                    "(:init) (:goal (and)))")
    result = sp.translate(source=domain, data=[str(path)], language="hddl", profile="bmc",
                          options={"plan_horizon": "1", "decomposition_depth": "1"})
    _, actual = parsed_relation(result)
    if enabled:
        assert result.parser.is_declared_variable("do_act@0")
        reference = z3.And(z3.Bool("do_act@0"), z3.Not(z3.Bool("__pddl_noop@0")),
                           z3.Not(z3.Bool("done@0")), z3.Bool("done@1"))
    else:
        reference = z3.BoolVal(False)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, reference))
    assert solver.check() == z3.unsat
