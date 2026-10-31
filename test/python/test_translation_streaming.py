"""Streaming Translation output stays byte-equivalent and solver-readable."""
import pytest
from pathlib import Path

z3 = pytest.importorskip("z3")
import somtparser as sp


def _lexicographic_translation():
    source = "Choose integer x and y from 0 to 10, with x+y at most 10. Maximize x then y."
    model = {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "optimization",
        "declarations": [
            {"name": "x", "sort": "Int", "lower": 0, "upper": 10},
            {"name": "y", "sort": "Int", "lower": 0, "upper": 10},
        ],
        "functions": [],
        "constraints": [{
            "expr": {"op": "le", "args": [
                {"op": "add", "args": [{"var": "x"}, {"var": "y"}]},
                {"literal": 10, "sort": "Int"},
            ]},
            "span": [0, len(source)],
        }],
        "objectives": [
            {"sense": "maximize", "expr": {"var": "x"}, "span": [0, len(source)]},
            {"sense": "maximize", "expr": {"var": "y"}, "span": [0, len(source)]},
        ],
        "objective_order": "lexicographic",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }
    candidate = sp.propose_nl(source, language="hir", provider=lambda _request: model)
    assert candidate.valid, candidate.diagnostics
    translated = sp.compile_candidate(candidate, accept_digest=candidate.digest,
                                      dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostics]
    return translated.translation


def test_streamed_translation_matches_string_and_parses_as_multiobjective(tmp_path):
    translated = _lexicographic_translation()
    expected = translated.to_smt2(dialect=sp.OmtDialect.Z3)
    destination = tmp_path / "translated.smt2"
    translated.write_smt2(str(destination), dialect=sp.OmtDialect.Z3)
    actual = destination.read_text(encoding="utf-8")
    assert actual == expected

    # Parse the written artifact independently and check that both objective
    # commands precede query execution and have the expected lexicographic result.
    optimizer = z3.Optimize()
    optimizer.from_file(str(destination))
    assert len(optimizer.objectives()) == 2
    assert optimizer.check() == z3.sat
    assert optimizer.model()[z3.Int("x")].as_long() == 10
    assert optimizer.model()[z3.Int("y")].as_long() == 0


def test_stream_writer_reports_open_failure_and_refuses_failed_translation(tmp_path):
    translated = _lexicographic_translation()
    with pytest.raises(RuntimeError, match="open destination"):
        translated.write_smt2(str(tmp_path / "missing" / "out.smt2"))

    failed = sp.translate(source="not a model", language="unknown-language-id")
    assert not failed.ok
    destination = tmp_path / "preserve-me.smt2"
    destination.write_text("existing bytes\n", encoding="utf-8")
    with pytest.raises(RuntimeError, match="failed Translation"):
        failed.write_smt2(str(destination))
    assert destination.read_text(encoding="utf-8") == "existing bytes\n"


def test_optimathsat_stream_writer_retains_supported_lexicographic_goals(tmp_path):
    translated = _lexicographic_translation()
    destination = tmp_path / "optimathsat.smt2"
    translated.write_smt2(str(destination), dialect=sp.OmtDialect.OptiMathSAT)
    script = destination.read_text(encoding="utf-8")
    assert script == translated.to_smt2(dialect=sp.OmtDialect.OptiMathSAT)
    # Read the vendor export through the public parser, then independently
    # check the ordered optimum with Z3.
    reread = sp.parse(script).dump_smt2(dialect=sp.OmtDialect.Z3)
    optimizer = z3.Optimize()
    optimizer.from_string(reread)
    assert len(optimizer.objectives()) == 2
    assert optimizer.check() == z3.sat
    assert [optimizer.model()[z3.Int(name)].as_long() for name in ("x", "y")] == [10, 0]


def test_parser_dump_smt2_file_writer_matches_string_and_checks_open(tmp_path):
    parser = sp.parse("""(set-logic QF_LIA)
        (declare-const x Int)
        (assert (! (= x 0) :named x-is-zero))
    """)
    expected = parser.dump_smt2()
    destination = tmp_path / "parser.smt2"
    assert parser.dump_smt2(str(destination)) == str(destination)
    assert destination.read_text(encoding="utf-8") == expected
    assert ":named x-is-zero" in expected

    with pytest.raises(RuntimeError, match="open destination"):
        parser.dump_smt2(str(tmp_path / "missing" / "parser.smt2"))


@pytest.mark.skipif(not Path('/dev/full').exists(), reason='requires a failing Unix output device')
@pytest.mark.parametrize('writer', ['translation', 'parser'])
def test_stream_writer_reports_write_failure(writer):
    with pytest.raises(RuntimeError, match='writing'):
        if writer == 'translation':
            _lexicographic_translation().write_smt2('/dev/full', dialect=sp.OmtDialect.Z3)
        else:
            sp.parse('(set-logic QF_LIA) (assert true)').dump_smt2('/dev/full')
