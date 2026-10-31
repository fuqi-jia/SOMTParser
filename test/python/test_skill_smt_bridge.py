"""Real public-API and solver checks for the direct-SMT skill, without LLM calls."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
SKILL = ROOT / "skills/somtparser-nl-smtlib"
BRIDGE = SKILL / "scripts/smt_bridge.py"


def invoke(*args):
    return subprocess.run([sys.executable, str(BRIDGE), *map(str, args)],
                          text=True, capture_output=True, env=os.environ.copy(), timeout=45)


def fixture(tmp_path, *, contradictory=False):
    source = tmp_path / "source.txt"
    source.write_text("Choose an integer x between 4 and 9. Minimize x.", encoding="utf-8")
    program = "(declare-const x Int)\n(assert (>= x 4))\n(assert (<= x 9))\n(minimize x)\n(check-sat)"
    if contradictory:
        source.write_text("An integer x is at least 4 and at most 2.", encoding="utf-8")
        program = "(declare-const x Int)\n(assert (>= x 4))\n(assert (<= x 2))\n(check-sat)"
    model = dict(schema="somt-nl-formal-v1", language="smtlib2", program=program,
                 decision="satisfiability" if contradictory else "optimization",
                 assumptions=[], unresolved=[], links=[dict(span=[0,len(source.read_text())],
                                                             fragment="(assert (>= x 4))")])
    path = tmp_path / "model.json"
    path.write_text(json.dumps(model))
    return source, path


def validate_export(tmp_path, *, contradictory=False):
    source, model = fixture(tmp_path, contradictory=contradictory)
    attempt, export = tmp_path / "attempt", tmp_path / "export"
    checked = invoke("validate", source, model, "--out", attempt)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    candidate = json.loads((attempt / "candidate.json").read_text())
    compiled = invoke("compile", attempt / "candidate.json", "--digest", candidate["digest"], "--out", export)
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    return export


def test_live_schema_and_context(tmp_path):
    source, _ = fixture(tmp_path)
    context = tmp_path / "context.json"
    context.write_text('{"x":"integer quantity"}')
    result = invoke("request", source, "--context", context)
    assert result.returncode == 0, result.stdout + result.stderr
    request = json.loads(result.stdout)
    assert request["source"] == source.read_text()
    assert request["context"] == {"x":"integer quantity"}
    assert request["schema"]["properties"]["language"]["const"] == "smtlib2"
    assert "context" not in request["schema"]["properties"]


def test_optimization_survives_export_and_whole_load(tmp_path):
    export = validate_export(tmp_path)
    result = invoke("check", export / "model.smt2", "--out", tmp_path / "check", "--solve")
    assert result.returncode == 0, result.stdout + result.stderr
    report = json.loads(result.stdout)
    assert report["load"] == "passed" and report["verdict"] == "sat"
    assert report["objectives"] == 1
    assert report["normalized_objective_values"][0]["value"] == "4"
    assert report["intent_preservation"] == "not-proved"


def test_source_contradiction_is_valid_unsat(tmp_path):
    export = validate_export(tmp_path, contradictory=True)
    result = invoke("check", export / "model.smt2", "--out", tmp_path / "check", "--solve")
    assert result.returncode == 0, result.stdout + result.stderr
    assert json.loads(result.stdout)["verdict"] == "unsat"


@pytest.mark.parametrize("failure", ["unresolved", "fragment"])
def test_validation_retains_real_failures(tmp_path, failure):
    source, path = fixture(tmp_path)
    model = json.loads(path.read_text())
    if failure == "unresolved":
        model["unresolved"] = ["Two source-supported domains remain possible."]
    else:
        model["links"][0]["fragment"] = "quotation instead of emitted formula"
    path.write_text(json.dumps(model))
    result = invoke("validate", source, path, "--out", tmp_path / "invalid")
    assert result.returncode == 2
    assert not json.loads((tmp_path / "invalid/validation.json").read_text())["valid"]


def test_wrong_digest_never_exports(tmp_path):
    source, path = fixture(tmp_path)
    assert invoke("validate", source, path, "--out", tmp_path / "attempt").returncode == 0
    result = invoke("compile", tmp_path / "attempt/candidate.json", "--digest", "wrong",
                    "--out", tmp_path / "bad-export")
    assert result.returncode == 2
    assert not (tmp_path / "bad-export/model.smt2").exists()


def test_unicode_links_require_explicit_repeated_occurrence(tmp_path):
    source, program = tmp_path / "source.txt", tmp_path / "program.smt2"
    source.write_text("中文x >= 4；x >= 4")
    program.write_text("(assert (>= x 4))")
    args = ("link", source, program, "--quote", "x >= 4", "--fragment", program.read_text())
    assert invoke(*args).returncode == 2
    result = invoke(*args, "--occurrence", 1)
    assert result.returncode == 0
    link = json.loads(result.stdout)
    assert link["span"] == [9,15]
    assert source.read_text()[slice(*link["span"])] == "x >= 4"


def test_duplicate_json_keys_are_not_silently_overwritten(tmp_path):
    source, path = fixture(tmp_path)
    path.write_text('{"program":"old","program":"new"}')
    result = invoke("validate", source, path, "--out", tmp_path / "bad")
    assert result.returncode == 2 and "duplicate" in result.stdout
    assert not (tmp_path / "bad/candidate.json").exists()


def test_malformed_target_is_not_a_load_pass(tmp_path):
    script = tmp_path / "bad.smt2"
    script.write_text("(assert (+ true 1))")
    result = invoke("check", script, "--out", tmp_path / "check")
    assert result.returncode == 2
    assert json.loads(result.stdout)["status"] == "check-error"


def test_bundle_loads_selected_references_and_tracks_changes(tmp_path):
    spec = importlib.util.spec_from_file_location("skill_bundle", SKILL / "scripts/skill_bundle.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    bundle = module.build_bundle(SKILL, "cp")
    assert "references/cp.md" in bundle["resources"]
    assert "references/linear-omt.md" not in bundle["resources"]
    assert "references/evaluation.md" not in bundle["resources"]
    assert module.build_bundle(SKILL, "cp")["sha256"] == bundle["sha256"]
    assert module.build_bundle(SKILL, "all")["sha256"] != bundle["sha256"]
