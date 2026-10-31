"""Complete bounded source relation, including signed metric, for 15 controls.

Expectations are hand-derived from pinned original PDDL, not from target models
or the frontend/HIR implementation. Every source numeric value, definedness bit,
mapped proposition and action choice is observable. Only target auxiliaries are
existentially projected. The comparison is symmetric difference, with no point
sampling, optimization or worker resource limit. Run on the qualification server
after test_pddl_numeric OUTPUT_DIR; it also accepts an independent audit directory.
"""
from pathlib import Path
import hashlib
import json
import sys
import time

import z3
from z3.z3util import get_vars


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def real(value):
    return z3.RealVal(str(value))


def query(expression, path, wanted):
    solver = z3.Solver()
    solver.set(timeout=0)
    solver.add(expression)
    path.write_text(solver.to_smt2())
    started = time.time()
    answer = solver.check()
    row = dict(answer=str(answer), expected=wanted, elapsed=time.time() - started,
               query_sha256=digest(path), passed=str(answer) == wanted)
    if answer == z3.sat:
        row["witness"] = str(solver.model())
    elif answer == z3.unknown:
        row["reason_unknown"] = solver.reason_unknown()
    write_json(path.with_suffix(".result.json"), row)
    return row


def check_qf_constants(expression):
    pending, seen = [expression], set()
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        assert not z3.is_quantifier(term), "unexpected quantified numeric fixture target"
        if z3.is_app(term):
            if term.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                assert term.num_args() == 0, "unexpected nonconstant target function"
            pending.extend(term.children())


def specification(case, aliases):
    """Return exact initial/next-state observations, independent of target SMT."""
    horizon = case["horizon"]
    assert horizon in (0, 1)
    fluents = case["fluents"]
    expected_labels = {f"state[{step}]::{label}" for step in range(horizon + 1)
                       for fluent in fluents for label in (fluent, f"defined({fluent})")}
    if horizon:
        expected_labels.update({"state[0]::(done)", "state[1]::(done)",
                                f"choice[0]::{case['action']}"})
    # For the zero-step controls, done is an unused closed-world false atom,
    # absent from the emitted source projection; there is no action choice.
    assert set(aliases) == expected_labels, (case["name"], set(aliases) ^ expected_labels)
    terms = {}
    for label, target in aliases.items():
        is_bool = label.startswith("choice[") or "::defined(" in label or label.endswith("::(done)")
        terms[label] = z3.Bool(target) if is_bool else z3.Real(target)
    parts = {}
    for step in range(horizon + 1):
        values = case["initial"] if step == 0 else case["final"]
        # For an inconsistent source the final table is intentionally absent:
        # no fabricated successor or default-filled counterexample is used.
        if values is None:
            continue
        assert set(values) == set(fluents)
        for fluent in fluents:
            value = values[fluent]
            value_label = f"state[{step}]::{fluent}"
            defined_label = f"state[{step}]::defined({fluent})"
            parts[defined_label] = terms[defined_label] == (value is not None)
            # The source projection uses canonical zero for an undefined
            # partial numeric cell; its definedness remains observable.
            parts[value_label] = terms[value_label] == real(0 if value is None else value)
    if horizon:
        parts["state[0]::(done)"] = z3.Not(terms["state[0]::(done)"])
        parts["state[1]::(done)"] = terms["state[1]::(done)"]
        parts[f"choice[0]::{case['action']}"] = terms[f"choice[0]::{case['action']}"]
    if case["satisfiable"]:
        assert set(parts) == set(aliases)
    return terms, parts


def verify(root, output):
    source_root = Path(__file__).resolve().parent / "pddl_numeric_relations"
    cases_path = source_root / "cases.json"
    cases = json.loads(cases_path.read_text())
    assert len(cases) == 15 and len({row["name"] for row in cases}) == 15
    assert sum(row["satisfiable"] for row in cases) == 7
    output.mkdir(parents=True, exist_ok=False)
    report = dict(passed=False, complete=False, solver=z3.get_version_string(),
                  oracle_sha256=digest(Path(__file__)), cases_manifest_sha256=digest(cases_path),
                  relation="complete bounded source observations and signed objective",
                  source_controls=15, no_sampling=True, solver_timeout_ms=0,
                  worker_limits=None, cases=[], negative_controls=[],
                  limitations="Fixed original bounded source controls; not an unbounded planning or corpus-accuracy claim.")
    report_path = output / "pddl-numeric-complete-relations.json"
    cache = {}
    try:
        for case in cases:
            name = case["name"]
            write_json(output / "current.json", dict(case=name, phase="complete-relation", started=time.time()))
            for kind in ("domain", "problem"):
                original = source_root / "fixtures" / (name + f".{kind}.pddl")
                actual = root / (name + f".{kind}.pddl")
                assert digest(original) == case[kind + "_sha256"]
                assert actual.read_bytes() == original.read_bytes(), (name, kind, "source changed")
            alias_path = root / (name + ".tsv")
            rows = [line.split("\t") for line in alias_path.read_text().splitlines()]
            assert all(len(row) == 2 for row in rows)
            aliases = dict(rows)
            assert len(aliases) == len(rows) == len(set(aliases.values()))
            terms, parts = specification(case, aliases)
            target_path = root / (name + ".smt2")
            module = z3.Optimize()
            module.from_file(str(target_path))
            assert len(module.objectives()) == int(case["metric_direction"] is not None), name
            actual = z3.And(*module.assertions())
            signed = None
            if case["metric_direction"] is not None:
                # Optimize.objectives() is normalized to minimization: maximize
                # therefore contributes the negated original source expression.
                signed = z3.Real("__independent_numeric_signed_metric")
                assert str(signed) not in aliases.values()
                assert all(str(v) != str(signed) for v in get_vars(actual))
                actual = z3.And(actual, signed == module.objectives()[0])
                if case["satisfiable"]:
                    assert case["signed_metric"] is not None
                    parts["signed_metric"] = signed == real(case["signed_metric"])
            check_qf_constants(actual)
            variables = get_vars(actual)
            by_name = {str(v): v for v in variables}
            assert len(by_name) == len(variables), "same name with incompatible target sorts"
            for term in terms.values():
                if str(term) in by_name:
                    assert term.sort().eq(by_name[str(term)].sort())
            observable = {term.get_id() for term in terms.values()}
            if signed is not None:
                observable.add(signed.get_id())
            hidden = [v for v in variables if v.get_id() not in observable]
            projected = z3.Exists(hidden, actual) if hidden else actual
            expected = z3.And(*parts.values()) if case["satisfiable"] else z3.BoolVal(False)
            # Save both full relations as well as the proof obligation. Neither
            # target nor source is specialized to a solver-produced assignment.
            for label, body in (("source", expected), ("target-projected", projected)):
                recorder = z3.Solver()
                recorder.add(body)
                (output / (name + "." + label + ".smt2")).write_text(recorder.to_smt2())
            comparison = query(z3.Xor(projected, expected), output / (name + ".xor.smt2"), "unsat")
            # Independent source feasibility prevents an accidentally empty
            # positive oracle from making a failed translation look equivalent.
            feasibility = query(expected, output / (name + ".source-feasibility.smt2"),
                                "sat" if case["satisfiable"] else "unsat")
            row = dict(case=name, source_sat=case["satisfiable"], horizon=case["horizon"],
                       source_reason=case["reason"], whole_module_parse=True,
                       observed_source_labels=sorted(aliases),
                       observed_numeric_values=sum(k.startswith("state[") and "::(" in k and not k.endswith("::(done)") for k in aliases),
                       observed_definedness=sum("::defined(" in k for k in aliases),
                       observed_choices=sum(k.startswith("choice[") for k in aliases),
                       signed_metric=case["signed_metric"], metric_direction=case["metric_direction"],
                       hidden_auxiliaries=[str(v) for v in hidden], full_relation_xor=comparison,
                       source_feasibility=feasibility, target_sha256=digest(target_path),
                       mapping_sha256=digest(alias_path), domain_sha256=case["domain_sha256"],
                       problem_sha256=case["problem_sha256"])
            report["cases"].append(row)
            write_json(report_path, report)
            assert comparison["passed"] and feasibility["passed"], name
            cache[name] = (projected, expected, terms, parts, signed)

        # Mutations intentionally leave final cells unchanged in the first three
        # controls; the old final-cell check could not establish their absence.
        projected, expected, terms, parts, signed = cache["swap"]
        mutations = [
            ("missing_initial_value", z3.Exists([terms["state[0]::(x)"]], expected)),
            ("missing_initial_definedness", z3.Exists([terms["state[0]::defined((x))"]], expected)),
            ("missing_action_choice", z3.Exists([terms["choice[0]::(step)"]], expected)),
            ("wrong_maximize_sign", z3.And(*[value for key, value in parts.items() if key != "signed_metric"], signed == real("1"))),
            ("extra_restriction", z3.And(expected, terms["state[0]::(x)"] > real("2"))),
        ]
        for name, mutant in mutations:
            result = query(z3.Xor(projected, mutant), output / ("negative-" + name + ".smt2"), "sat")
            report["negative_controls"].append(dict(name=name, case="swap", **result))
            write_json(report_path, report)
            assert result["passed"], name
        projected, expected, terms, parts, signed = cache["initialize"]
        result = query(z3.Xor(projected, z3.Exists([terms["state[0]::(x)"]], expected)),
                       output / "negative-undefined_value_totalization.smt2", "sat")
        report["negative_controls"].append(dict(name="undefined_value_totalization", case="initialize", **result))
        assert result["passed"]
        report.update(passed=True, complete=True)
    except BaseException as error:
        report.update(passed=False, complete=True, error=repr(error))
        write_json(report_path, report)
        raise
    write_json(report_path, report)
    # Fresh runner compatibility only. Preserve a historical weak-oracle report
    # if auditing an already qualified output directory.
    legacy_path = root / "pddl-numeric-source-oracles.json"
    if not legacy_path.exists():
        write_json(legacy_path, report)
    print(json.dumps(dict(passed=True, cases=len(report["cases"]),
                          negative_controls=len(report["negative_controls"]), report=str(report_path))))


if __name__ == "__main__":
    assert len(sys.argv) in (2, 3), "usage: oracle OUTPUT_DIR [FRESH_AUDIT_DIR]"
    input_root = Path(sys.argv[1])
    verify(input_root, Path(sys.argv[2]) if len(sys.argv) == 3 else input_root / "numeric-complete-relation")
