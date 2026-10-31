"""The public WCNF path preserves exact weights while streaming packed clauses."""

import pytest
import somtparser as sp


def test_default_wcnf_keeps_the_expanded_parser_api():
    result = sp.translate(
        source="p wcnf 1 1 10\n1 1 0\n",
        language="wcnf",
    )
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert not result.uses_packed_smt_stream
    assert result.has_parser
    assert result.parser is not None


def test_streamed_translation_exposes_safe_parser_state_and_exact_weights():
    result = sp.translate(
        source=(
            "p wcnf 2 3 9007199254740994\n"
            "9007199254740994 1 0\n"
            "9007199254740993 -2 0\n"
            "h 0\n"
        ),
        language="wcnf",
        options={"packed": "1"},
    )
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.uses_packed_smt_stream
    assert not result.has_parser
    with pytest.raises(RuntimeError, match="no materialized Parser"):
        _ = result.parser
    assert result.to_smt2(sp.OmtDialect.Z3) == (
        "(declare-const x1 Bool)\n"
        "(declare-const x2 Bool)\n"
        "(assert (or x1))\n"
        "(assert-soft (or (not x2)) :weight 9007199254740993)\n"
        "(assert false)\n"
        "(check-sat)\n(exit)\n"
    )
    default_script = result.to_smt2()
    assert default_script == result.to_smt2(sp.OmtDialect.Gomt)
    restored = sp.parse(default_script)
    assert len(restored.soft_weights) == 1
    assert str(restored.soft_weights[0]) == "9007199254740993"


def test_public_wcnf_warns_and_expands_out_of_range_literal_domain():
    result = sp.translate(
        source="p wcnf 1 1\n1 2 0\n",
        language="wcnf",
        options={"packed": "1"},
    )
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert any("index 2 is used" in d.message for d in result.diagnostic_items)
    assert result.to_smt2(sp.OmtDialect.Z3) == (
        "(declare-const x1 Bool)\n"
        "(declare-const x2 Bool)\n"
        "(assert-soft (or x2) :weight 1)\n"
        "(check-sat)\n(exit)\n"
    )


def test_python_strict_still_raises_for_a_malformed_wcnf_input():
    with pytest.raises(sp.TranslationError):
        sp.translate(
            source="p wcnf 1 1\n1 nope 0\n",
            language="wcnf",
            strict=True,
            options={"packed": "1"},
        )


def test_arbitrary_precision_top_still_marks_equal_weight_clause_hard():
    result = sp.translate(
        source=(
            "p wcnf 2 2 9007199254740993\n"
            "9007199254740993 1 0\n"
            "9 2 0\n"
        ),
        language="wcnf",
        options={"packed": "1"},
    )
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.to_smt2(sp.OmtDialect.Z3) == (
        "(declare-const x1 Bool)\n"
        "(declare-const x2 Bool)\n"
        "(assert (or x1))\n"
        "(assert-soft (or x2) :weight 9)\n"
        "(check-sat)\n(exit)\n"
    )


@pytest.mark.parametrize("source, expected, cost", [
    ("p wcnf 0 1 10\n10 0\n", "unsat", None),
    ("p wcnf 0 2 10\n2 0\n3 0\n", "sat", 5),
    ("p wcnf 1 2 10\nh 1 0\n3 0\n", "sat", 3),
    ("p wcnf 0 1\n9007199254740993 0\n", "sat", 9007199254740993),
])
@pytest.mark.parametrize("dialect", [sp.OmtDialect.Z3, sp.OmtDialect.Gomt])
def test_empty_clauses_parse_and_preserve_feasibility_and_cost(source, expected, cost, dialect):
    z3 = pytest.importorskip("z3")
    result = sp.translate(source=source, language="wcnf", options={"packed": "1"})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Optimize()
    script = result.to_smt2(dialect)
    if dialect == sp.OmtDialect.Gomt:
        script = sp.parse(script).dump_smt2(dialect=sp.OmtDialect.Z3)
    solver.from_string(script)
    assert str(solver.check()) == expected
    if cost is not None:
        objectives = solver.objectives()
        assert len(objectives) == 1
        assert solver.model().eval(objectives[0], model_completion=True).as_long() == cost
