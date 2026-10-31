"""One result type and identical completed output with/without inspection data."""
import io
import json
from pathlib import Path

import pytest
import somtparser as sp

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "languages/minizinc/instances/ok/trivial.mzn"


@pytest.mark.parametrize("settings", [
    {"source": "var 1..5: x; constraint x > 2; solve minimize x;", "language": "minizinc", "dialect": "z3"},
    {"source": "var int: x; constraint x; solve satisfy;", "language": "minizinc"},
    {"source": "not a model", "language": "minizinc"},
    {"source": "(assert true)(check-sat)", "language": "smtlib2"},
    {"source": "p cnf 3 2\n1 -2 0\n3 0\n", "language": "dimacs", "options": {"packed": "1"}},
    {"source": "aag 0 0 0 0 0\n", "language": "aiger", "module": True},
    {"source": "(assert true)", "language": "unknown"},
    {"source": "(assert true)", "language": "smtlib2", "profile": "unknown"},
    {"source": "(assert true)", "language": "smtlib2", "dialect": "unknown"},
    {"source": "(declare-const x Int)(minimize x)", "language": "smtlib2", "dialect": "none"},
])
def test_details_changes_only_inspection_availability(settings):
    full = sp.translate(**settings, details=True)
    light = sp.translate(**settings, details=False)
    assert type(full) is type(light) is sp.Translation
    assert (full.smt2.encode(), full.diagnostics.encode(), full.exit_code) == (
        light.smt2.encode(), light.diagnostics.encode(), light.exit_code)
    assert full.report is not None
    assert light.report is None
    assert light.details is False
    assert not light.has_parser
    with pytest.raises(RuntimeError, match="details=False"):
        _ = light.parser
    with pytest.raises(RuntimeError, match="another dialect"):
        light.to_smt2(sp.OmtDialect.OptiMathSAT)


def test_report_path_still_writes_json_when_details_are_not_returned(tmp_path):
    report = tmp_path / "report.json"
    full = sp.translate(MODEL, report=report, dialect="z3")
    before = json.loads(report.read_bytes())
    light = sp.translate(MODEL, report=report, dialect="z3", details=False)
    after = json.loads(report.read_bytes())
    for key in ("translate_ms", "parse_ms", "typecheck_ms", "passes_ms", "lower_ms", "semantics_ms"):
        before["stats"].pop(key)
        after["stats"].pop(key)
    assert before == after
    assert light.report is None
    assert (full.smt2, full.diagnostics, full.exit_code) == (light.smt2, light.diagnostics, light.exit_code)


def test_streamed_output_and_stdin_are_identical(tmp_path):
    for stdin in (MODEL.read_text(), ""):
        outcomes = []
        channels = []
        for details in (True, False):
            output, diagnostics = io.StringIO(), io.StringIO()
            t = sp.translate("-", language="minizinc", stdin=io.StringIO(stdin),
                             output=output, diagnostics=diagnostics, details=details)
            outcomes.append((t.exit_code, t.smt2, t.diagnostics))
            channels.append((output.getvalue().encode(), diagnostics.getvalue().encode()))
        assert outcomes[0] == outcomes[1]
        assert channels[0] == channels[1]
    t = sp.translate(MODEL, dialect="z3", details=False, output=io.StringIO())
    with pytest.raises(RuntimeError, match="not retained"):
        t.to_smt2(sp.OmtDialect.Z3)


def test_io_fault_is_identical_in_both_modes(tmp_path):
    report = tmp_path / "missing" / "report.json"
    full = sp.translate(MODEL, report=report)
    light = sp.translate(MODEL, report=report, details=False)
    assert (full.exit_code, full.smt2, full.diagnostics) == (light.exit_code, light.smt2, light.diagnostics)
    assert full.exit_code == 3


def test_hir_builder_uses_the_identical_translation_type():
    builder = sp.HirBuilder()
    builder.declare("x", "Int", lower=0, upper=4)
    builder.constrain({"op": "ge", "args": [{"var": "x"}, {"literal": 2, "sort": "Int"}]})
    full = builder.translate(details=True)
    light = builder.translate(details=False)
    assert type(full) is type(light) is sp.Translation
    assert full.exit_code == light.exit_code == 0
    assert (full.smt2, full.diagnostics) == (light.smt2, light.diagnostics)
    assert full.report is not None and light.report is None
    assert full.parser is not None
    with pytest.raises(RuntimeError, match="details=False"):
        _ = light.parser
    assert light.to_smt2(sp.OmtDialect.Z3) == light.smt2


def test_deprecated_alias_calls_the_single_api(monkeypatch):
    calls = []
    translate = sp.translate
    def observed(*args, **kwargs):
        calls.append((args, kwargs))
        return translate(*args, **kwargs)
    monkeypatch.setattr(sp, "translate", observed)
    for details in (True, False):
        with pytest.warns(DeprecationWarning, match="use somtparser.translate"):
            old = sp.convert(MODEL, dialect="z3", details=details)
        new = translate(MODEL, dialect="z3", details=details)
        assert type(old) is type(new) is sp.Translation
        assert (old.smt2, old.diagnostics, old.exit_code) == (new.smt2, new.diagnostics, new.exit_code)
    assert len(calls) == 2
    assert not hasattr(sp, "ConvertResult")


def test_strict_preserves_structured_error_in_light_mode():
    for details in (True, False):
        with pytest.raises(sp.TranslationError) as error:
            sp.translate(source="var int: x; constraint x; solve satisfy;",
                         language="minizinc", strict=True, details=details)
        assert error.value.code == sp.ErrorCode.E_TYPE
        assert error.value.diagnostics[0].code == sp.ErrorCode.E_TYPE


def test_listing_one_translation_and_kernel_export(tmp_path):
    model = tmp_path / "partial.mzn"
    model.write_bytes(MODEL.read_bytes())
    m = sp.translate(model, language="minizinc", profile="default",
                     dialect="z3", report=tmp_path / "report.json")
    assert m.exit_code == 0, m.diagnostics
    p = sp.parse(m.smt2)
    target = tmp_path / "partial.oms.smt2"
    p.dump_smt2(str(target), sp.OmtDialect.OptiMathSAT)
    assert "(minimize x)" in target.read_text(encoding="utf-8")
