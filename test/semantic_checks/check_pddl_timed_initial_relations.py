"""Independent finite happening interpreter and complete fixed-schedule relation.

Every source state observable and the signed objective is checked. Action
controls fix their explicit source schedule to start=1, end=1+duration; the
separate API oracle checks the symbolic makespan relation for all goal values.
No source converter, HIR helper, floating arithmetic, sampling or solver limit.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import hashlib
import itertools
import json
import re
import sys
import z3
from z3.z3util import get_vars

root = Path(sys.argv[1])


def parse(text):
    tokens = iter(re.findall(r"\(|\)|[^\s()]+", text.lower()))

    def one(token):
        if token != "(":
            assert token != ")"
            return token
        result = []
        for token in tokens:
            if token == ")":
                return result
            result.append(one(token))
        raise AssertionError("unfinished source")

    result = one(next(tokens))
    assert next(tokens, None) is None
    return result


def typed(values):
    result, waiting = [], []
    i = 0
    while i < len(values):
        if values[i] == "-":
            result.extend((v, values[i + 1]) for v in waiting)
            waiting = []
            i += 2
        else:
            waiting.append(values[i])
            i += 1
    return result + [(v, "object") for v in waiting]


def atom(value):
    assert isinstance(value, list) and all(isinstance(v, str) for v in value)
    return "(" + " ".join(value) + ")"


def literal(value):
    return (atom(value[1]), False) if value[0] == "not" else (atom(value), True)


def truth(value, state):
    if not value:
        return True
    if value[0] == "and":
        return all(truth(v, state) for v in value[1:])
    if value[0] == "not":
        return not truth(value[1], state)
    if value == ["d"]:
        return "(p)" in state
    return atom(value) in state


def reads(value):
    if not value:
        return set()
    if value[0] == "and":
        return set().union(*(reads(v) for v in value[1:]))
    if value[0] == "not":
        return reads(value[1])
    return {"(p)" if value == ["d"] else atom(value)}


def conjuncts(value):
    return value[1:] if value and value[0] == "and" else [value] if value else []


def reference(domain, problem):
    declarations = {row[0]: row[1:] for row in domain[2:] if row[0] != ":derived"}
    constants = typed(declarations[":constants"])
    atoms = []
    for predicate in declarations[":predicates"]:
        arguments = typed(predicate[1:])
        universes = [[name for name, kind in constants if sort == "object" or kind == sort]
                     for _, sort in arguments]
        atoms.extend(atom([predicate[0], *args]) for args in itertools.product(*universes))
    fields = {row[0]: row[1:] for row in problem[2:]}
    events, initial, til_count = defaultdict(list), set(), 0
    # Each record has independent owner/read/add/delete sets. Simultaneous
    # literal assignments and real endpoints share exactly the source mutex.
    for value in fields[":init"]:
        if value[0] == "at" and isinstance(value[2], list):
            key, polarity = literal(value[2])
            events[Fraction(value[1])].append((f"til{til_count}", set(),
                {key} if polarity else set(), set() if polarity else {key}, []))
            til_count += 1
        else:
            key, polarity = literal(value)
            if polarity:
                initial.add(key)
    action = next((row for row in domain[2:] if row[0] == ":durative-action"), None)
    invariant, last, schedule = [], Fraction(0), None
    if action:
        fields_a = dict(zip(action[2::2], action[3::2]))
        start = Fraction(1)
        duration = Fraction(fields_a[":duration"][2])
        end = start + duration
        schedule, last = (start, end), end
        conditions, changes = {"start": [], "end": []}, {"start": [], "end": []}
        for condition in conjuncts(fields_a[":condition"]):
            if condition[:2] == ["over", "all"]:
                invariant.append(condition[2])
            else:
                assert condition[0] == "at"
                conditions[condition[1]].append(condition[2])
        for effect in conjuncts(fields_a[":effect"]):
            assert effect[0] == "at"
            changes[effect[1]].append(literal(effect[2]))
        for endpoint, time in [("start", start), ("end", end)]:
            events[time].append((endpoint, set().union(*(reads(c) for c in conditions[endpoint])),
                {key for key, value in changes[endpoint] if value},
                {key for key, value in changes[endpoint] if not value}, conditions[endpoint]))
    times = sorted(events)
    states, valid = [initial], True
    for time in times:
        records = events[time]
        before = states[-1]
        for _, _, _, _, conditions in records:
            valid &= all(truth(condition, before) for condition in conditions)
        for left, right in itertools.combinations(records, 2):
            _, lr, la, ld, _ = left
            _, rr, ra, rd, _ = right
            valid &= not bool((lr & (ra | rd)) | (rr & (la | ld)) | (la & rd) | (ra & ld))
        adds = set().union(*(row[2] for row in records))
        deletes = set().union(*(row[3] for row in records))
        after = (before - deletes) | adds
        states.append(after)
        if schedule and schedule[0] <= time < schedule[1]:
            valid &= all(truth(condition, after) for condition in invariant)
    count = til_count + (2 if schedule else 0)
    states += [states[-1]] * (count - len(times))
    goal = fields[":goal"][0]
    goals = [truth(goal, state) for state in states]
    valid &= goals[-1]
    makespan = None
    for index, time in enumerate([Fraction(0)] + times):
        if time >= last and all(goals[index:]):
            makespan = time
            break
    valid &= makespan is not None
    return dict(atoms=set(atoms), states=states, valid=valid, makespan=makespan,
                schedule=schedule, maximize=fields[":metric"][0] == "maximize")


rows = []
ledger = [line.split("\t") for line in (root / "source-controls.tsv").read_text().splitlines()]
assert len(ledger) == 35 and len({row[0] for row in ledger}) == 35
assert all(expected == actual for _, expected, actual in ledger)
assert sum(row[1] == "1" for row in ledger) == 23
for path in sorted(root.glob("*.domain.pddl")):
    name = path.name[:-len(".domain.pddl")]
    domain = parse(path.read_text())
    problem = parse((root / (name + ".problem.pddl")).read_text())
    expected = reference(domain, problem)
    parsed = z3.Optimize()
    parsed.from_file(str(root / (name + ".smt2")))
    assert len(parsed.objectives()) == 1, name
    raw_aliases = [line.split("\t") for line in (root / (name + ".tsv")).read_text().splitlines()]
    aliases = dict(raw_aliases)
    assert len(aliases) == len(raw_aliases), (name, "duplicate source mapping")
    expected_labels = {f"state[{step}]::{item}" for step in range(len(expected["states"]))
                       for item in expected["atoms"] | {"(x)"}}
    if expected["schedule"]:
        expected_labels.update({"plan[0]::start", "plan[0]::end", "choice[0]::(a)"})
    assert set(aliases) == expected_labels, (name, "incomplete source projection",
        sorted(expected_labels - set(aliases)), sorted(set(aliases) - expected_labels))
    objective = z3.Real("__independent_signed_makespan")
    actual = z3.And(*parsed.assertions(), objective == parsed.objectives()[0])
    expected_terms, observed = [], {str(objective)}
    schedule_terms = []
    for label, target in aliases.items():
        observed.add(target)
        if label.startswith("state["):
            index, source_atom = re.fullmatch(r"state\[(\d+)\]::(.*)", label).groups()
            index = int(index)
            assert index < len(expected["states"]), (name, label)
            if source_atom == "(x)":
                expected_terms.append(z3.Real(target) == 0)
            else:
                assert source_atom in expected["atoms"], (name, label)
                expected_terms.append(z3.Bool(target) == truth(parse(source_atom), expected["states"][index]))
        elif label.startswith("plan[0]::"):
            assert expected["schedule"]
            endpoint = label.split("::")[1]
            value = expected["schedule"][["start", "end"].index(endpoint)]
            constraint = z3.Real(target) == z3.RealVal(str(value))
            expected_terms.append(constraint)
            schedule_terms.append(constraint)
        elif label == "choice[0]::(a)":
            constraint = z3.Bool(target)
            expected_terms.append(constraint)
            schedule_terms.append(constraint)
        else:
            raise AssertionError((name, "unaccounted source observable", label))
    # A rational schedule has an exact canonical witness. Fixing that witness
    # removes irrelevant nonlinear existential arithmetic from this finite
    # control without changing any of its source schedules or state choices.
    replacements = []
    if expected["schedule"]:
        for endpoint, value in zip(["start", "end"], expected["schedule"]):
            base = "__pddl_occurrence_0_" + endpoint
            replacements.extend([(z3.Int(base + "_numerator"), z3.IntVal(value.numerator)),
                                 (z3.Int(base + "_denominator"), z3.IntVal(value.denominator))])
    if replacements:
        actual = z3.substitute(actual, *replacements)
    actual = z3.simplify(z3.And(actual, *schedule_terms))
    auxiliary = [v for v in get_vars(actual) if str(v) not in observed]
    projected = z3.Exists(auxiliary, actual) if auxiliary else actual
    if expected["valid"]:
        signed = expected["makespan"] * (-1 if expected["maximize"] else 1)
        expected_terms.append(objective == z3.RealVal(str(signed)))
        oracle = z3.And(*expected_terms)
    else:
        oracle = z3.BoolVal(False)
    solver = z3.Solver()
    solver.add(z3.Xor(projected, oracle))
    answer = solver.check()
    row = dict(case=name, full_relation=str(answer), source_schedule="fixed exact endpoints" if expected["schedule"] else "empty action plan",
               source_satisfiable=expected["valid"], source_observables=len(aliases), auxiliary_variables=len(auxiliary),
               stable_makespan=str(expected["makespan"]), objective_direction="max" if expected["maximize"] else "min",
               target_sha256=hashlib.sha256((root / (name + ".smt2")).read_bytes()).hexdigest())
    if answer != z3.unsat:
        row["counterexample"] = str(solver.model()) if answer == z3.sat else solver.reason_unknown()
    rows.append(row)
    assert answer == z3.unsat, row
assert len(rows) == 23, len(rows)
result = dict(passed=True, full_relation_cases=len(rows), cases=rows, limits=None,
              source_controls=len(ledger), source_rejections=sum(row[1] == "0" for row in ledger),
              scope="complete source states and signed objective at the declared fixed schedules; symbolic makespan separately checked by API controls")
(root / "pddl-timed-initial-source-oracles.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
