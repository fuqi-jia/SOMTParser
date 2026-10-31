"""Public conversion API: outcomes, reports, streams and module exports."""

import io
import json
import os
from pathlib import Path

import pytest
import somtparser as sp


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "languages/minizinc/instances/ok/trivial.mzn"
SMT = "(declare-const x Int)(assert (>= x 2))(minimize x)(check-sat)"


@pytest.mark.parametrize("dialect, objective", [
    ("gomt", "(define-objective "),
    ("smtlib-omt-2025", "(define-objective "),
    ("z3", "(minimize x)"),
    (sp.OmtDialect.Z3, "(minimize x)"),
    ("optimathsat", "(minimize x)"),
])
def test_named_parameters_capture_result_without_process_output(dialect, objective, capfd):
    result = sp.translate(source=SMT, language="smtlib2", dialect=dialect)
    assert isinstance(result, sp.Translation)
    assert result.exit_code == 0, result.diagnostics
    assert objective in result.smt2
    assert result.diagnostics == ""
    assert capfd.readouterr() == ("", "")


def test_path_detection_report_and_caller_owned_streams(tmp_path):
    expected = sp.translate(MODEL, dialect="z3")
    report = tmp_path / "report.json"
    output, diagnostics = io.StringIO(), io.StringIO()
    result = sp.translate(MODEL, dialect="z3", report=report,
                        output=output, diagnostics=diagnostics)
    assert result.exit_code == 0
    assert result.smt2 == result.diagnostics == ""
    assert not output.closed and not diagnostics.closed
    assert output.getvalue() == expected.smt2
    assert diagnostics.getvalue() == expected.diagnostics
    assert report.read_bytes().endswith(b"\n")
    metadata = json.loads(report.read_bytes())
    assert metadata["provenance"]["language_id"] == "minizinc"


@pytest.mark.parametrize("name, code", [("bad_syntax.mzn", "E_PARSE"),
                                         ("ill_sorted.mzn", "E_TYPE")])
def test_failure_has_no_smt_output_but_keeps_report(name, code, tmp_path, capfd):
    path = ROOT / "languages/minizinc/instances/reject" / name
    report = tmp_path / "failure.json"
    result = sp.translate(path, report=report)
    assert result.exit_code == 1
    assert result.smt2 == ""
    assert code in result.diagnostics
    assert path.name in result.diagnostics
    # Reports retain the legacy schema; error diagnostics are a separate
    # channel rather than newly injected fields in the JSON report.
    metadata = json.loads(report.read_bytes())
    assert "fidelity" in metadata and "stats" in metadata
    assert report.read_bytes().endswith(b"\n")
    assert capfd.readouterr() == ("", "")


@pytest.mark.parametrize("settings, message", [
    ({"dialect": "bogus"}, "unknown dialect 'bogus'\n"),
    ({"language": "bogus"}, "unknown language 'bogus'; known: "),
    ({"profile": "bogus"}, "unknown profile 'bogus'; known: "),
])
def test_invalid_settings_are_status_two(settings, message):
    result = sp.translate(MODEL, **settings)
    assert result.exit_code == 2
    assert result.smt2 == ""
    assert result.diagnostics.startswith(message)
    assert "E_UNSUPPORTED_CONSTRUCT" not in result.diagnostics
    assert "E_PASS_PIPELINE" not in result.diagnostics


def test_stdin_and_inline_source():
    text = MODEL.read_text()
    result = sp.translate("-", language="minizinc", stdin=io.StringIO(text))
    assert result.exit_code == 0, result.diagnostics
    inline = sp.translate(source=text, language="minizinc")
    assert result.smt2 == inline.smt2
    assert sp.translate("-", stdin=io.StringIO(text)).exit_code == 2
    empty = sp.translate("-", language="minizinc", stdin=io.StringIO())
    assert empty.exit_code == 1
    assert empty.diagnostics == "error: E_IO: stdin is empty\n"


def test_stdin_read_error_and_lazy_read():
    class FailedInput:
        def read(self, size):
            raise OSError("cannot read")

    failed = sp.translate("-", language="minizinc", stdin=FailedInput())
    assert failed.exit_code == 3
    assert failed.smt2 == ""
    assert failed.diagnostics == "error: cannot read stdin\n"
    assert sp.translate(MODEL, stdin=FailedInput()).exit_code == 0


def test_companion_data_and_frontend_options(tmp_path):
    model = tmp_path / "data.mzn"
    data = tmp_path / "data.dzn"
    model.write_text("int: n; var 0..n: x; solve minimize x;\n")
    data.write_text("n = 3;\n")
    result = sp.translate(model, data=[data], dialect="z3")
    assert result.exit_code == 0, result.diagnostics
    assert "(minimize x)" in result.smt2

    btor = ROOT / "languages/btor2/instances/ok/uninit.btor2"
    result = sp.translate(btor, profile="bmc", options={"bmc_depth": "2"})
    assert result.exit_code == 0, result.diagnostics
    assert "s@2" in result.smt2 or "(check-sat)" in result.smt2


def test_module_export_and_interface_report(tmp_path):
    report = tmp_path / "interface.json"
    result = sp.translate(source="aag 0 0 0 0 0\n", language="aiger",
                        module=True, report=report)
    assert result.exit_code == 0, result.diagnostics
    assert result.smt2.startswith("; SOMT module interface ")
    assert "(check-sat)" not in result.smt2
    interface = result.smt2.splitlines()[0].removeprefix("; SOMT module interface ")
    assert report.read_bytes() == interface.encode() + os.linesep.encode()
    for settings in ({"profile": "default"}, {"dialect": "gomt"}):
        invalid = sp.translate(source="aag 0 0 0 0 0\n", language="aiger",
                             module=True, **settings)
        assert invalid.exit_code == 2
        assert invalid.smt2 == ""
        assert invalid.diagnostics == "--module cannot be combined with --profile or --dialect\n"


def test_output_open_and_flush_failures(tmp_path):
    failed = sp.translate(MODEL, report=tmp_path / "missing" / "report.json")
    assert failed.exit_code == 3
    assert failed.smt2 == ""
    assert "cannot write report" in failed.diagnostics

    class FlushFailure(io.StringIO):
        def flush(self):
            raise OSError("full")

    class ShortWrite(io.StringIO):
        def write(self, text):
            return 0

    for sink in (FlushFailure(), ShortWrite()):
        for settings in ({}, {"source": "aag 0 0 0 0 0\n", "language": "aiger", "module": True}):
            result = sp.translate("" if settings else MODEL, output=sink, **settings)
            assert result.exit_code == 3
            assert result.smt2 == ""
            assert result.diagnostics == "error: cannot write SMT-LIB output\n"


@pytest.mark.skipif(not Path("/dev/full").exists(), reason="requires /dev/full")
def test_native_file_write_failures():
    output = open("/dev/full", "w", encoding="utf-8", newline="")
    try:
        result = sp.translate(MODEL, output=output)
        assert result.exit_code == 3
        assert result.diagnostics == "error: cannot write SMT-LIB output\n"
    finally:
        # A failed flush leaves Python's buffer pending; closing may fail too.
        try:
            output.close()
        except OSError:
            pass
    result = sp.translate(MODEL, report="/dev/full")
    assert result.exit_code == 3
    assert result.smt2 == ""


def test_streaming_preserves_utf8_across_chunks_and_captures_no_duplicate():
    symbol = "x" * 8180 + "变量" * 30
    source = f"(declare-const |{symbol}| Int)(assert (>= |{symbol}| 2))(check-sat)"
    expected = sp.translate(source=source, language="smtlib2")
    output = io.StringIO()
    streamed = sp.translate(source=source, language="smtlib2", output=output)
    assert expected.exit_code == streamed.exit_code == 0
    assert streamed.smt2 == ""
    assert output.getvalue().encode() == expected.smt2.encode()
    assert "变量" in output.getvalue()
    assert sp.translate(source=source, language="smtlib2").smt2 == expected.smt2


def test_diagnostic_stream_failure_and_missing_input():
    class BadDiagnostics(io.StringIO):
        def write(self, text):
            raise OSError("failed diagnostics")

    assert sp.translate(MODEL, dialect="bogus", diagnostics=BadDiagnostics()).exit_code == 3
    missing = sp.translate()
    assert missing.exit_code == 2
    assert missing.diagnostics == "an input path or source is required\n"
