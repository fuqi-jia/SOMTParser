"""Interpretation boundaries and independently checked solver semantics."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest
import somtparser as sp
from somtparser.natural_language import Candidate, ModelError, candidate_schema


EN = "Let x be an integer between 0 and 10.\nx is at least 3.\nMinimize x.\n"
ZH = "设x为整数，范围为0到10。\nx至少3。\n最小化x。\n"


def _solver_path(solver):
    """Find a solver BINARY, on PATH or beside the running interpreter.

    `shutil.which` alone was not enough, and the gap was invisible: the z3 pip
    package installs its executable into the venv's `bin`, which is on PATH
    only when the venv is activated. Invoking pytest by absolute path -- which
    is what the project's own recipe does -- leaves it off, so all 24 z3 cases
    and all 17 cvc5 cases skipped, and the suite reported 537 passed instead of
    561. A skip is not a pass, and a suite that cannot reach its solver reports
    neither; this is the same shape as the stale-`.so` trap in C1c, where the
    tests also ran green against something that was not there.

    Looked up beside `sys.executable` rather than by importing the module,
    because these cases deliberately drive a real binary over SMT-LIB text:
    that is what exercises the emitted script end to end, including the OMT
    commands the Python API would not go through.
    """
    found = shutil.which(solver)
    if found is not None:
        return found
    beside = Path(sys.executable).parent / solver
    return str(beside) if beside.exists() else None


def solve(result, solver="z3", values=False):
    assert result.ok, result.diagnostics
    executable = _solver_path(solver)
    if executable is None:
        pytest.skip(f"{solver} unavailable")
    script = result.to_smt2()
    if values:
        script = script.replace("(exit)", "(get-value (nl_s0))\n(exit)")
    args = [executable, "-in"] if solver == "z3" else [executable, "--lang=smt2"]
    run = subprocess.run(args, input=script, text=True, capture_output=True, timeout=10)
    assert run.returncode == 0, run.stdout + run.stderr
    assert "error" not in run.stdout.lower(), run.stdout
    return run.stdout.strip()


@pytest.mark.parametrize("source", [EN, ZH])
def test_bilingual_optimum(source):
    result = sp.translate_nl(source)
    assert "(minimize nl_s0)" in result.to_smt2()
    assert solve(result, values=True) == "sat\n((nl_s0 3))"
    assert result.interpret_solver_answer("sat")["optimality"] == "not-established"
    assert result.project_assignment({"nl_s0": 3}) == {"x": 3}
    report = result.report()
    assert report["intent_preservation"] == "not-proved"
    assert report["source_links"]["objectives"][0]["span"][1] <= len(source)


def test_lexicographic_priority():
    source = "Let x be an integer between 0 and 10.\nLet y be an integer between 0 and 10.\nx+y=10.\nMinimize x.\nMinimize y.\n"
    assert not sp.translate_nl(source).ok
    result = sp.translate_nl(source + "Optimize lexicographically.\n")
    assert solve(result, values=True) == "sat\n((nl_s0 0))"
    assert result.to_smt2().count("(minimize ") == 2


@pytest.mark.parametrize("solver", ["z3", "cvc5"])
@pytest.mark.parametrize("goal,expected", [("x >= 0", "valid"), ("x > 0", "invalid")])
def test_validity_polarity(goal, expected, solver):
    result = sp.translate_nl(
        f"Let x be an integer between 0 and 10.\nProve that {goal}.\n"
    )
    answer = solve(result, solver)
    assert result.interpret_solver_answer(answer)["status"] == expected
    assert result.interpret_solver_answer("unknown")["status"] == "unknown"


@pytest.mark.parametrize("solver", ["z3", "cvc5"])
@pytest.mark.parametrize(
    "formula,expected",
    [
        ("tdiv(-7,3) = -2", "sat"),
        ("tdiv(7,-3) = -2", "sat"),
        ("tdiv(-7,-3) = 2", "sat"),
        ("tdiv(7,0) = 0", "unsat"),
        ("not (tdiv(7,0) = 0)", "sat"),
        ("tdiv(7,0) != 0", "unsat"),
        ("ite(true, 4, tdiv(7,0)) = 4", "sat"),
        ("1/0 = 0", "unsat"),
        ("not (1/0 = 0)", "sat"),
        ("0.1 + 0.2 = 0.3", "sat"),
        ("1/3 + 2/3 = 1", "sat"),
    ],
)
def test_partiality_and_exact_arithmetic(formula, expected, solver):
    assert solve(sp.translate_nl(formula + ".\nFind a solution.\n"), solver) == expected


@pytest.mark.parametrize("solver", ["z3", "cvc5"])
@pytest.mark.parametrize(
    "quantifier,expected",
    [
        ("For every x in Empty, x = x", "sat"),
        ("There exists x in Empty such that x = x", "unsat"),
    ],
)
def test_empty_domain(quantifier, expected, solver):
    result = sp.translate_nl(
        f"Domain Empty is empty.\n{quantifier}.\nFind a solution.\n"
    )
    assert solve(result, solver) == expected


@pytest.mark.parametrize("solver", ["z3", "cvc5"])
@pytest.mark.parametrize(
    "quantifiers,expected",
    [
        ("For every x in D, There exists y in D such that x = y", "sat"),
        ("There exists y in D such that For every x in D, x = y", "unsat"),
    ],
)
def test_quantifier_order(quantifiers, expected, solver):
    assert (
        solve(
            sp.translate_nl(
                f"Domain D consists of A, B.\n{quantifiers}.\nFind a solution."
            ),
            solver,
        )
        == expected
    )


def test_chinese_predicate_and_projection():
    text = "域Person包含Alice、Bob。\n谓词likes的参数类型为Person、Person。\n设p为Person类型变量。\np等于Bob。\n对于每个r属于Person，存在h属于Person使得likes(r,h)。\n求一个解。"
    result = sp.translate_nl(text)
    assert solve(result) == "sat"
    assert result.project_assignment({"nl_s1": 1}) == {"p": "Bob"}
    with pytest.raises(ModelError):
        result.project_assignment({"nl_s1": 2})


@pytest.mark.parametrize(
    "source",
    [
        "Let x be an integer.\nx is fairly small.\nFind a solution.",
        "Let x be an integer.\nx >= 0.",
        "Let x be an integer.\nFind a solution.\nMinimize x.",
        "Let x be an integer between 10 and 0.\nFind a solution.",
        "Let true be a boolean.\nFind a solution.",
        "Let x be an integer.\nx.foo = 3.\nFind a solution.",
        "__import__('os').system('echo unsafe').\nFind a solution.",
        "Domain D consists of A.\nDomain E consists of B.\nA=B.\nFind a solution.",
        "Let x be an integer.\nx and true.\nFind a solution.",
    ],
)
def test_no_silent_interpretation(source):
    result = sp.translate_nl(source)
    assert not result.ok
    assert result.diagnostics
    with pytest.raises(ModelError):
        result.to_smt2()


def test_external_provider_requires_content_selection():
    calls = []

    def provider(request):
        calls.append(request)
        return sp.propose_nl(EN).model

    pending = sp.translate_nl(EN, provider=provider)
    assert not pending.ok and pending.acceptance == "pending"
    candidate = pending.candidate
    restored = Candidate.from_json(candidate.to_json())
    assert restored.digest == candidate.digest
    assert not sp.compile_candidate(restored, accept_digest="wrong").ok
    selected = sp.compile_candidate(restored, accept_digest=restored.digest)
    assert solve(selected, values=True) == "sat\n((nl_s0 3))"
    assert len(calls) == 1
    assert calls[0]["schema"] == candidate_schema()
    copied = restored.model
    copied["symbols"][0]["lower"] = 9
    assert restored.model["symbols"][0]["lower"] == 0
    changed = json.loads(candidate.to_json())
    changed["model"]["symbols"][0]["lower"] = 9
    with pytest.raises(ModelError, match="digest"):
        Candidate.from_json(json.dumps(changed))


def test_invalid_candidate_and_duplicate_fields():
    model = sp.propose_nl(EN).model
    model["constraints"][0]["span"] = [0, 999999]
    candidate = sp.propose_nl(EN, provider=lambda _: model)
    assert not candidate.valid
    assert not sp.compile_candidate(candidate, accept_digest=candidate.digest).ok
    with pytest.raises(ModelError, match="duplicate"):
        Candidate.from_json('{"schema":1,"schema":2}')


def test_cli_failure_emits_no_smt(tmp_path):
    source = tmp_path / "source.txt"
    source.write_text("Make everything better.\n", encoding="utf-8")
    run = subprocess.run(
        [sys.executable, "-m", "somtparser.natural_language", "translate", str(source)],
        text=True,
        capture_output=True,
    )
    assert run.returncode == 1 and run.stdout == "" and run.stderr


def test_cli_proposal_and_compile(tmp_path):
    source = tmp_path / "source.txt"
    source.write_text(ZH, encoding="utf-8")
    base = [sys.executable, "-m", "somtparser.natural_language"]
    proposed = subprocess.run(
        base + ["propose", str(source)], text=True, capture_output=True, check=True
    )
    candidate = Candidate.from_json(proposed.stdout)
    snapshot = tmp_path / "candidate.json"
    snapshot.write_text(proposed.stdout, encoding="utf-8")
    report = tmp_path / "report.json"
    compiled = subprocess.run(
        base
        + [
            "compile",
            str(snapshot),
            "--accept-digest",
            candidate.digest,
            "--report",
            str(report),
        ],
        text=True,
        capture_output=True,
        check=True,
    )
    assert "(minimize " in compiled.stdout
    assert json.loads(report.read_text())["interpretation"] == "explicit-selection"


@pytest.mark.parametrize("bad_model", [None, [], {"schema": "unsupported"}])
def test_invalid_provider_models_are_reportable(bad_model):
    candidate = sp.propose_nl(EN, provider=lambda _: bad_model)
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest)
    assert not result.ok
    assert result.report()["diagnostics"]


def test_ast_resource_limit():
    model = sp.propose_nl(EN).model
    term = {"var": "x"}
    for _ in range(70):
        term = {"op": "neg", "args": [term]}
    model["objectives"][0]["expr"] = term
    candidate = sp.propose_nl(EN, provider=lambda _: model)
    assert not candidate.valid
    assert "limit" in candidate.diagnostics[0]


def test_solver_dialect_cannot_erase_optimization():
    result = sp.translate_nl(EN, dialect=sp.OmtDialect.NONE)
    assert not result.ok
    with pytest.raises(ModelError):
        result.to_smt2()


def test_implication_and_exact_real_projection():
    source = "Let b be a boolean.\nLet x be a real.\nb.\nIf b, then x = 0.1.\nx != 0.1.\nFind a solution."
    result = sp.translate_nl(source)
    assert solve(result) == "unsat"
    from fractions import Fraction

    assert result.project_assignment({"nl_s0": True, "nl_s1": "1/10"}) == {
        "b": True,
        "x": Fraction(1, 10),
    }
    with pytest.raises(ModelError):
        result.project_assignment({"nl_s0": True, "nl_s1": 0.1})


EXAMPLES = Path(__file__).resolve().parents[2] / "examples" / "natural_language"


@pytest.mark.parametrize("path", sorted(EXAMPLES.glob("*/*.txt")), ids=lambda p: p.name)
def test_documented_fixtures(path):
    result = sp.translate_nl(path.read_text(encoding="utf-8"))
    assert result.ok == (path.parent.name == "ok"), result.diagnostics


SMT_EXAMPLES = (
    Path(__file__).resolve().parents[2] / "languages" / "smtlib2" / "instances"
)


@pytest.mark.parametrize(
    "path",
    sorted(SMT_EXAMPLES.glob("ok/*.smt2")) + sorted(SMT_EXAMPLES.glob("reject/*.smt2")),
    ids=lambda p: p.name,
)
def test_smt_objective_fixtures(path):
    result = sp.translate(
        source=path.read_text(), language="smtlib2", dialect=sp.OmtDialect.Z3
    )
    assert result.ok == (path.parent.name == "ok")


def test_expansion_resource_limit():
    model = sp.propose_nl(EN).model
    term = {"var": "x"}
    for _ in range(25):
        term = {"op": "tdiv", "args": [term, {"literal": 1, "sort": "Int"}]}
    model["objectives"][0]["expr"] = term
    candidate = sp.propose_nl(EN, provider=lambda _: model)
    assert not candidate.valid
    assert "resource limit" in candidate.diagnostics[0]


def test_bounded_profile_has_no_unconditional_validity_verdict():
    result = sp.translate_nl("Let x be an integer.\nProve that x=x.", profile="bv32")
    assert result.ok
    assert result.translation.report.fidelity.bounds
    assert result.interpret_solver_answer("unsat")["status"] == "unknown"


def test_keyword_prefix_does_not_become_an_objective():
    source = "Let Minimizex be a boolean.\nLet x be an integer.\nMinimizex.\nFind a solution."
    result = sp.translate_nl(source)
    assert solve(result) == "sat"
    assert result.candidate.model["objectives"] == []


def test_chinese_operator_inside_identifier_is_rejected():
    source = "设x为整数。\n设y为整数。\n设x等于y为布尔变量。\nx等于y。\n求一个解。"
    result = sp.translate_nl(source)
    assert not result.ok
    assert "reserved" in result.diagnostics[0]
