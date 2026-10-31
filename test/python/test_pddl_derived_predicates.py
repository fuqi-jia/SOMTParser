"""Derived-state observations versus independent finite graph/trace semantics."""
from itertools import product

import pytest
import somtparser as sp
from somtparser import _somtparser as native
import z3


def translate(tmp_path, domain, initial="", horizon=0, goal="(and)", objects=""):
    problem = tmp_path / "problem.pddl"
    problem.write_text(f"(define (problem p) (:domain d) (:objects {objects}) "
                       f"(:init {initial}) (:goal {goal}))")
    return sp.translate(source=domain, data=[str(problem)], language="pddl", profile="bmc",
                        options={"plan_horizon": str(horizon)})


def solver(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    answer = z3.Solver()
    answer.add(z3.parse_smt2_string(result.to_smt2()))
    return answer


def closure(edges):
    # Source semantics: graph reachability, including self reachability exactly
    # when a nonempty directed cycle exists. No HIR rule replay is involved.
    answer = set(edges)
    for middle in "ab":
        for left in "ab":
            for right in "ab":
                if (left, middle) in answer and (middle, right) in answer:
                    answer.add((left, right))
    return answer


GRAPH = """(define (domain d) (:requirements :adl :derived-predicates)
 (:types node) (:constants a b - node)
 (:predicates (edge ?x ?y - node) (reach ?x ?y - node) (marked ?x ?y - node))
 (:derived (reach ?x ?y - node)
   (or (edge ?x ?y) (exists (?z - node) (and (edge ?x ?z) (reach ?z ?y))))))"""


@pytest.mark.parametrize("bits", list(product([False, True], repeat=4)))
def test_complete_transitive_closure_relation(tmp_path, bits):
    pairs = list(product("ab", repeat=2))
    edges = {pair for pair, bit in zip(pairs, bits) if bit}
    initial = " ".join(f"(edge {a} {b})" for a, b in edges)
    result = translate(tmp_path, GRAPH, initial)
    s = solver(result)
    assert s.check() == z3.sat
    expected = closure(edges)
    wrong = [z3.Bool(f"reach_{a}_{b}@0") != ((a, b) in expected) for a, b in pairs]
    wrong += [z3.Bool(f"edge_{a}_{b}@0") != ((a, b) in edges) for a, b in pairs]
    s.add(z3.Or(*wrong))
    assert s.check() == z3.unsat


@pytest.mark.parametrize("initial_bits", list(product([False, True], repeat=2)))
def test_all_two_step_traces_recompute_closure_and_old_state_guards(tmp_path, initial_bits):
    domain = GRAPH[:-1] + """
      (:action add :parameters (?x ?y - node) :effect (edge ?x ?y))
      (:action del :parameters (?x ?y - node) :effect (not (edge ?x ?y)))
      (:action tag :parameters (?x ?y - node) :precondition (reach ?x ?y)
        :effect (and (not (edge ?x ?y)) (when (reach ?x ?y) (marked ?x ?y)))))"""
    pairs = [("a", "b"), ("b", "a")]
    initial = {pair for pair, bit in zip(pairs, initial_bits) if bit}
    result = translate(tmp_path, domain, " ".join(f"(edge {a} {b})" for a, b in initial), horizon=2)
    s = solver(result)
    choices = [f"{a}_{x}_{y}" for a in ("add", "del", "tag") for x, y in pairs] + ["noop"]
    for trace in product(choices, repeat=2):
        states = [(set(initial), set())]
        padded, valid = False, True
        for action in trace:
            edges, marked = map(set, states[-1])
            if padded and action != "noop":
                valid = False
                break
            if action == "noop":
                padded = True
            else:
                name, a, b = action.split("_")
                if name == "tag" and (a, b) not in closure(edges):
                    valid = False
                    break
                if name == "add":
                    edges.add((a, b))
                else:
                    edges.discard((a, b))
                    if name == "tag":
                        marked.add((a, b))
            states.append((edges, marked))
        s.push()
        s.add(*[z3.Bool(f"__pddl_noop@{i}" if action == "noop" else f"do_{action}@{i}")
                for i, action in enumerate(trace)])
        assert s.check() == (z3.sat if valid else z3.unsat), trace
        if valid:
            wrong = []
            for step, (edges, marked) in enumerate(states):
                reach = closure(edges)
                for a, b in product("ab", repeat=2):
                    for name, truth in (("edge", edges), ("reach", reach), ("marked", marked)):
                        wrong.append(z3.Bool(f"{name}_{a}_{b}@{step}") != ((a, b) in truth))
            s.add(z3.Or(*wrong))
            assert s.check() == z3.unsat, trace
        s.pop()


@pytest.mark.parametrize("seed,blocked", list(product([False, True], repeat=2)))
def test_mutual_recursion_and_negative_basic_conditions(tmp_path, seed, blocked):
    domain = """(define (domain d) (:requirements :adl :derived-predicates)
      (:predicates (seed) (blocked) (p) (q))
      (:derived (p) (q)) (:derived (q) (not (not (p))))
      (:derived (p) (and (seed) (not (blocked)))))"""
    s = solver(translate(tmp_path, domain, ("(seed) " if seed else "") + ("(blocked)" if blocked else "")))
    assert s.check() == z3.sat
    s.add(z3.Or(z3.Bool("p@0") != (seed and not blocked), z3.Bool("q@0") != (seed and not blocked)))
    assert s.check() == z3.unsat


def test_typed_head_can_restrict_rule_universe(tmp_path):
    domain = """(define (domain d) (:requirements :typing :derived-predicates)
      (:types small - object) (:constants a - small b - object)
      (:predicates (base ?x) (p ?x)) (:derived (p ?x - small) (base ?x)))"""
    s = solver(translate(tmp_path, domain, "(base a) (base b)"))
    assert s.check() == z3.sat
    s.add(z3.Or(z3.Not(z3.Bool("p_a@0")), z3.Bool("p_b@0")))
    assert s.check() == z3.unsat


@pytest.mark.parametrize("rule", [
    "(:derived (p ?x ?x) (base ?x))",
    "(:derived (p ?x ?y) (base ?x))",
    "(:derived (p ?x ?y) (and (base ?x) (base ?z)))",
    "(:derived (p ?x ?y) (not (p ?x ?y)))",
    "(:derived (p ?x ?y) (imply (p ?x ?y) (and (base ?x) (base ?y))))",
    "(:derived (p ?x ?y) (or (and) (not (p ?x ?y))))",
    "(:derived (p ?x ?y) (and (base ?x ?y) (base ?x)))",
    "(:derived (unknown ?x ?y) (and (base ?x) (base ?y)))",
    "(:derived (p ?x - object ?y - node) (and (base ?x) (base ?y)))",
    "(:derived (p ?x - missing ?y - node) (and (base ?x) (base ?y)))",
    "(:derived (p a ?y) (base ?y))",
    "(:derived (p ?x ?y) (and (base ?x) (forall (?y - node) (base ?y))))",
])
@pytest.mark.parametrize("inhabited", [False, True])
def test_invalid_rules_rejected_even_for_empty_types(tmp_path, rule, inhabited):
    domain = f"""(define (domain d) (:requirements :adl :derived-predicates)
      (:types node) {"(:constants a - node)" if inhabited else ""}
      (:predicates (base ?x - node) (p ?x ?y - node)) {rule})"""
    result = translate(tmp_path, domain)
    assert not result.ok


@pytest.mark.parametrize("effect", ["(p ?x)", "(not (p ?x))", "(when (and) (p ?x))",
                                      "(forall (?y - node) (not (p ?y)))"])
def test_derived_effect_rejected_before_empty_grounding(tmp_path, effect):
    domain = f"""(define (domain d) (:requirements :adl :derived-predicates)
      (:types node) (:predicates (base ?x - node) (p ?x - node))
      (:derived (p ?x) (base ?x))
      (:action bad :parameters (?x - node) :effect {effect}))"""
    assert not translate(tmp_path, domain).ok


@pytest.mark.parametrize("initial", ["(p)", "(not (p))"])
def test_derived_initial_assignments_rejected(tmp_path, initial):
    domain = """(define (domain d) (:requirements :derived-predicates)
      (:predicates (base) (p)) (:derived (p) (base)))"""
    assert not translate(tmp_path, domain, initial).ok


@pytest.mark.parametrize("seed", [False, True])
def test_native_closure_api_projects_exact_relation(tmp_path, seed):
    model = native.HirModel()
    boolean = native.HirSort.boolean()
    b, p, q = [model.declare(n, boolean) for n in ("base", "p", "q")]
    result = native.planning_derived_closure(model, [p, q], [(0, b), (0, q), (1, p)])
    assert result["rounds"] == 2
    assert result["base_dependencies"] == [{"base"}, {"base"}]
    for atom, value in zip([p, q], result["values"]):
        model.constrain(native._hir_op("eq", [atom, value]))
    actual = model.translate()
    assert actual.ok, [d.message for d in actual.diagnostic_items]
    s = solver(actual)
    s.add(z3.Bool("base") == seed)
    assert s.check() == z3.sat
    s.add(z3.Or(z3.Bool("p") != seed, z3.Bool("q") != seed))
    assert s.check() == z3.unsat


def test_invalid_native_closure_is_atomic():
    model = native.HirModel()
    p = model.declare("p", native.HirSort.boolean())
    before = model.translate().to_smt2()
    with pytest.raises(ValueError):
        native.planning_derived_closure(model, [p], [(0, native._hir_op("not", [p]))])
    assert model.translate().to_smt2() == before
