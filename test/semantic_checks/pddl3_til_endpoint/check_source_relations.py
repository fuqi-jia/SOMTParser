"""Whole public SMT relation and signed metric against original TIL-only PDDL.

The oracle interprets source names and exact rational timestamps independently.
It does not import the frontend or a HIR implementation, sample assignments,
optimize the metric, or truncate the observation sequence at makespan.
Run on the qualification server after test_pddl3_til_endpoint OUTPUT_DIR.
No worker resource limits or solver timeout are installed here.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import re
import sys
import time

import z3
from z3.z3util import get_vars


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(text):
    roots, stack = [], []
    for token in re.findall(r"[^\s()]+|[()]", re.sub(r";[^\n]*", "", text).lower()):
        if token == "(":
            node = []
            (stack[-1] if stack else roots).append(node)
            stack.append(node)
        elif token == ")":
            assert stack, "unbalanced source"
            stack.pop()
        else:
            assert stack, "atom outside source list"
            stack[-1].append(token)
    assert not stack and len(roots) == 1
    return roots[0]


def condition(formula, state):
    if not formula:
        return True
    op, *args = formula
    if op == "and":
        return all(condition(arg, state) for arg in args)
    if op == "not":
        assert len(args) == 1
        return not condition(args[0], state)
    assert op in {"g", "p"} and not args
    return state[op]


def modal(formula, states, times):
    op, *args = formula
    if op == "and":
        return all(modal(arg, states, times) for arg in args)
    if op == "at":
        assert len(args) == 2 and args[0] == "end"
        return condition(args[1], states[-1])
    if op == "sometime":
        return any(condition(args[0], state) for state in states)
    if op == "always":
        return all(condition(args[0], state) for state in states)
    assert op == "hold-after" and len(args) == 2
    bound = Fraction(args[0])
    # AI2009 Figure 1: existential, with a final-state fallback when t_n <= t.
    if times[-1] <= bound:
        return condition(args[1], states[-1])
    return any(t > bound and condition(args[1], state)
               for t, state in zip(times, states))


def strip_preferences(formula, records, trajectory):
    if formula[0] == "preference":
        assert len(formula) == 3
        records.append((formula[1], formula[2], trajectory))
        return ["and"]
    if formula[0] == "and":
        return ["and"] + [strip_preferences(arg, records, trajectory)
                          for arg in formula[1:]]
    return formula


def metric(expr, makespan, violations):
    if isinstance(expr, str):
        return makespan if expr == "total-time" else Fraction(expr)
    op, *args = expr
    if op == "is-violated":
        assert len(args) == 1
        return Fraction(violations[args[0]])
    values = [metric(arg, makespan, violations) for arg in args]
    if op == "+":
        return sum(values, Fraction(0))
    if op == "*":
        result = Fraction(1)
        for value in values:
            result *= value
        return result
    assert op == "-" and len(values) in (1, 2)
    return -values[0] if len(values) == 1 else values[0] - values[1]


def interpret(domain_text, problem_text):
    domain, problem = parse(domain_text), parse(problem_text)
    assert domain[:2] == ["define", ["domain", "til-endpoint"]]
    assert not any(section[0] in {":action", ":durative-action"} for section in domain[2:])
    declarations = [section for section in domain[2:] if section[0] == ":predicates"]
    assert declarations == [[":predicates", ["g"], ["p"]]]
    sections = {}
    for section in problem[2:]:
        assert section[0] not in sections
        sections[section[0]] = section[1:]
    assert sections[":domain"] == ["til-endpoint"]
    initial = {"g": False, "p": False}
    events = []
    for atom in sections[":init"]:
        if atom[0] == "at":
            assert len(atom) == 3
            when = Fraction(atom[1])
            literal = atom[2]
            positive = literal[0] != "not"
            target = literal if positive else literal[1]
            assert when > 0 and target in [["g"], ["p"]]
            events.append((when, target[0], positive))
        else:
            assert atom in [["g"], ["p"]]
            initial[atom[0]] = True
    assert events and len({event[0] for event in events}) == len(events)
    events.sort()
    states, times = [initial], [Fraction(0)]
    for when, atom, value in events:
        state = dict(states[-1])
        state[atom] = value
        states.append(state)
        times.append(when)
    preferences = []
    hard_goal = strip_preferences(sections[":goal"][0], preferences, False)
    hard_constraints = strip_preferences(sections[":constraints"][0], preferences, True)
    assert condition(hard_goal, states[-1])
    # PDDL2.2: choose the earliest boundary at/after the last action (zero here)
    # whose complete hard goal remains true through all subsequent TILs.
    makespan = next(t for i, t in enumerate(times)
                    if all(condition(hard_goal, state) for state in states[i:]))
    violations = Counter()
    for name, body, trajectory in preferences:
        satisfied = modal(body, states, times) if trajectory else condition(body, states[-1])
        violations[name] += int(not satisfied)
    direction, expression = sections[":metric"]
    value = metric(expression, makespan, violations)
    assert direction in {"minimize", "maximize"}
    signed = value if direction == "minimize" else -value
    return dict(states=states, times=times, makespan=makespan,
                violations=dict(violations), valid=modal(hard_constraints, states, times),
                signed=signed, metric=value, direction=direction)


def check_query(query, path):
    solver = z3.Solver()
    solver.set(timeout=0)
    solver.add(query)
    path.write_text(solver.to_smt2())
    answer = solver.check()
    detail = str(solver.model()) if answer == z3.sat else solver.reason_unknown() if answer == z3.unknown else None
    return str(answer), detail


def verify(output):
    source_root = Path(__file__).resolve().parent
    cases = json.loads((source_root / "cases.json").read_text())
    assert len(cases) == 18 and len({case["name"] for case in cases}) == 18
    rows, controls = [], []
    for case in cases:
        name = case["name"]
        assert case["horizon"] == 0
        domain = source_root / case["domain"]
        problem = source_root / case["problem"]
        assert digest(domain) == case["domain_sha256"]
        assert digest(problem) == case["problem_sha256"]
        assert (output / (name + ".domain.pddl")).read_bytes() == domain.read_bytes()
        assert (output / (name + ".problem.pddl")).read_bytes() == problem.read_bytes()
        source = interpret(domain.read_text(), problem.read_text())
        assert source["makespan"] == 0  # The goal g remains true, even after p is deleted.
        aliases_rows = [line.split("\t") for line in (output / (name + ".tsv")).read_text().splitlines()]
        aliases = dict(aliases_rows)
        assert len(aliases) == len(aliases_rows)
        expected_labels = {f"state[{i}]::({atom})" for i in range(len(source["states"])) for atom in ("g", "p")}
        assert set(aliases) == expected_labels, (name, set(aliases) ^ expected_labels)
        target = output / (name + ".smt2")
        module = z3.Optimize()
        module.from_file(str(target))
        assert len(module.objectives()) == 1
        signed = z3.Real("__independent_til_endpoint_signed_metric")
        actual = z3.And(*module.assertions(), signed == module.objectives()[0])
        observed = set(aliases.values()) | {str(signed)}
        expected = []
        for i, state in enumerate(source["states"]):
            for atom, value in state.items():
                expected.append(z3.Bool(aliases[f"state[{i}]::({atom})"]) == value)
        # Observe every happening, too: the equivalence cannot hide discarded
        # late TILs behind existential schedule projection or fixed substitutions.
        for i, when in enumerate(source["times"][1:]):
            active = z3.Bool(f"__pddl_happening_{i}_active")
            time_term = z3.Real(f"__pddl_happening_{i}_time")
            observed.update([str(active), str(time_term)])
            expected.extend([active, time_term == z3.RealVal(str(when))])
        expected.append(signed == z3.RealVal(str(source["signed"])))
        hidden = [term for term in get_vars(actual) if str(term) not in observed]
        projected = z3.Exists(hidden, actual) if hidden else actual
        oracle = z3.And(*expected) if source["valid"] else z3.BoolVal(False)
        (output / "til-endpoint-current.json").write_text(json.dumps(
            dict(case=name, phase="full-relation-and-signed-metric", started_unix=time.time(), limits=None)) + "\n")
        answer, detail = check_query(z3.Xor(projected, oracle), output / (name + ".relation-query.smt2"))
        row = dict(case=name, whole_optimize_loaded=True, full_relation_and_signed_metric=answer,
                   source_valid=source["valid"], source_makespan=str(source["makespan"]),
                   observation_end=str(source["times"][-1]), preference_violations=source["violations"],
                   signed_metric=str(source["signed"]), metric_direction=source["direction"],
                   target_sha256=digest(target), source_sha256=case["problem_sha256"],
                   source_state_observables=len(aliases), explicit_happening_observables=2*(len(source["times"])-1))
        if detail:
            row["diagnostic"] = detail
        rows.append(row)
        (output / "til-endpoint-oracles.partial.json").write_text(json.dumps(rows, indent=2) + "\n")
        assert answer == "unsat", row
        # A deliberately wrong endpoint/metric interpretation must disagree
        # with the complete translated relation, rather than merely load.
        mutants = {
            "rise_sometime_soft": ("truncate-soft-observation-at-makespan", Fraction(7)),
            "rise_at_end_hard": ("replace-makespan-by-last-til-time", Fraction(10)),
            "fall_combined_max": ("treat-hold-after-as-always-after", Fraction(-17)),
        }
        if name in mutants:
            label, wrong_signed = mutants[name]
            assert source["valid"] and source["signed"] != wrong_signed
            mutant = z3.And(*expected[:-1], signed == z3.RealVal(str(wrong_signed)))
            bad_answer, witness = check_query(z3.Xor(projected, mutant),
                                       output / (name + ".negative-query.smt2"))
            control = dict(case=name, mutation=label, expected="sat", actual=bad_answer, witness=witness)
            controls.append(control)
            (output / "til-endpoint-negative-controls.partial.json").write_text(json.dumps(controls, indent=2) + "\n")
            assert bad_answer == "sat", control
    assert len(controls) == 3
    result = dict(passed=True, full_relation_cases=len(rows), cases=rows, limits=None,
                  negative_controls=controls,
                  solver_timeout_ms=0, sampling=False, objective_optimized=False,
                  scope="complete zero-action source states, mandatory TIL happenings and signed public objective; no full temporal qualification claim")
    (output / "til-endpoint-oracles.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    verify(Path(sys.argv[1]))
