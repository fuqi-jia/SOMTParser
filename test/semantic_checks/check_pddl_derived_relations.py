"""Independent complete finite-state relation for emitted PDDL derived controls."""
from pathlib import Path
from itertools import product
import hashlib
import json
import sys
import z3
from z3.z3util import get_vars

root = Path(sys.argv[1])
pairs = list(product("ab", repeat=2))


def reach(edges):
    result = set(edges)
    for middle in "ab":
        for left, right in pairs:
            if (left, middle) in result and (middle, right) in result:
                result.add((left, right))
    return result


rows = []
names = ([f"graph{i}" for i in range(16)] + [f"trace{i}" for i in [0, 2, 4, 6]]
         + [f"mutual{i}" for i in range(4)] + ["typed", "empty"] + [f"numeric{i}" for i in range(4)]
         + ["namespace0", "namespace1"])
for name in names:
    path = root / (name + ".smt2")
    actual = z3.And(*z3.parse_smt2_file(str(path)))
    aliases = dict(line.split("\t") for line in (root / (name + ".tsv")).read_text().splitlines())
    observed = set(aliases.values())
    used = set()

    def atom(label):
        used.add(label)
        return z3.Bool(aliases[label])

    def state(step, edges, marked):
        facts = []
        for predicate, truth in [("edge", edges), ("reach", reach(edges)), ("marked", marked)]:
            for a, b in pairs:
                facts.append(atom(f"state[{step}]::({predicate} {a} {b})") == ((a, b) in truth))
        return z3.And(*facts)

    if name.startswith(("graph", "trace")):
        index = int(name[5:])
        edges = {pair for bit, pair in enumerate(pairs) if (index >> bit) & 1}
        expected = state(0, edges, set())
        if name.startswith("trace"):
            decisions = [(action, a, b) for action in ("add", "del", "tag", "markdel") for a, b in pairs]
            choices = [atom(f"choice[0]::({action} {a} {b})") for action, a, b in decisions]
            noop = z3.Bool("__pddl_noop@0")
            observed.add(str(noop))
            choices.append(noop)
            branches = []
            for i, decision in enumerate(decisions + [None]):
                after, marked = set(edges), set()
                if decision is not None:
                    action, a, b = decision
                    if action == "tag" and (a, b) not in reach(edges):
                        continue
                    if action == "add":
                        after.add((a, b))
                    else:
                        after.discard((a, b))
                        if action in ["tag", "markdel"] and (a, b) in reach(edges):
                            marked.add((a, b))
                branches.append(z3.And(*[choice == (j == i) for j, choice in enumerate(choices)],
                                       state(1, after, marked)))
            expected = z3.And(expected, z3.Or(*branches))
    elif name.startswith("mutual"):
        index = int(name[6:])
        truth = bool(index & 1) and not bool(index & 2)
        expected = z3.And(*[atom(f"state[0]::({p})") == value for p, value in
                           [("seed", bool(index & 1)), ("blocked", bool(index & 2)), ("p", truth), ("q", truth)]])
    elif name == "typed":
        expected = z3.And(*[atom(f"state[0]::({p} {a})") == truth for p, a, truth in
                           [("base", "a", True), ("base", "b", True), ("p", "a", True), ("p", "b", False)]])
    elif name.startswith("namespace"):
        initialized = name == "namespace0"
        facts = []
        for p, initial in [("p", -1), ("q", 1)]:
            label = f"numeric::({p})"
            used.update([f"state[0]::{label}", f"state[0]::defined({label})"])
            numeric = z3.Real(aliases[f"state[0]::{label}"])
            defined = z3.Bool(aliases[f"state[0]::defined({label})"])
            facts += [numeric == (initial if initialized else 0), defined == initialized,
                      atom(f"state[0]::({p})") == initialized]
        expected = z3.And(*facts)
    elif name == "empty":
        expected = z3.BoolVal(True)
    else:
        index = int(name[7:])
        used.update(["state[0]::(x)", "state[0]::defined((x))"])
        x = z3.Real(aliases["state[0]::(x)"])
        defined = z3.Bool(aliases["state[0]::defined((x))"])
        expected = z3.And(x == (-1 if index == 0 else 1 if index == 1 else 0),
                          defined == (index < 2),
                          atom("state[0]::(p)") == (index == 0), atom("state[0]::(q)") == (index == 0))
    assert used == set(aliases), (name, sorted(set(aliases) - used), sorted(used - set(aliases)))
    auxiliaries = [v for v in get_vars(actual) if str(v) not in observed]
    projected = z3.Exists(auxiliaries, actual) if auxiliaries else actual
    solve = z3.Solver()
    solve.add(z3.Xor(projected, expected))
    answer = solve.check()
    row = dict(case=name, full_relation=str(answer), source_observables=len(aliases),
               auxiliary_variables=len(auxiliaries), target_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    if answer != z3.unsat:
        row["counterexample"] = str(solve.model()) if answer == z3.sat else solve.reason_unknown()
    rows.append(row)
    assert answer == z3.unsat, row
(root / "pddl-derived-source-oracles.json").write_text(json.dumps(
    dict(passed=True, cases=rows, full_relation_cases=len(rows), limits=None,
         scope="complete source-derived finite controls; not official benchmark accuracy or unbounded plan length"), indent=2) + "\n")
print(json.dumps(rows))
