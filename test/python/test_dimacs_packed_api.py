"""Packed DIMACS must preserve the complete Boolean relation and vocabulary."""
import json

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def translate(source, packed=True):
    result = sp.translate(source=source, language="dimacs", options={"packed": str(int(packed))})
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream == packed
    assert result.has_parser != packed
    return result


@pytest.mark.parametrize("source,clauses,variables", [
    ("p cnf 4 3\n1 1\nc between literals\n-2 0 -1 3 0\n2 0\n",
     ((1, 1, -2), (-1, 3), (2,)), 4),
    ("p cnf 2 2\n0 1 0\n", ((), (1,)), 2),
    ("p cnf 0 1\n0\n", ((),), 0),
    ("p cnf 0 0\n", (), 0),
    ("p cnf 3 0\n", (), 3),
    ("p cnf 1 2\n1 0 -1 0\n", ((1,), (-1,)), 1),
    # Non-strict conversion retains all content despite header mismatches.
    ("p cnf 1 1\n1 -3 0\n3 0\n", ((1, -3), (3,)), 3),
])
@pytest.mark.parametrize("packed", [False, True])
def test_relation_matches_explicit_source_clauses(source, clauses, variables, packed):
    result = translate(source, packed)
    target = result.to_smt2(sp.OmtDialect.Z3)
    expected = z3.And(*[z3.Or(*[
        z3.Bool(f"x{literal}") if literal > 0 else z3.Not(z3.Bool(f"x{-literal}"))
        for literal in clause]) for clause in clauses])
    solver = z3.Solver()
    solver.add(z3.Xor(expected, z3.And(*z3.parse_smt2_string(target))))
    assert solver.check() == z3.unsat
    assert result.report.stats.num_objectives == 0
    assert target.count("(declare-") == variables
    if variables:
        assert f"x{variables} " in target


def test_file_input_and_inline_input_have_identical_packed_output(tmp_path):
    source = "c compact clauses\r\np cnf 3 2\r\n1 -2\r\n3 0 -3 0\r\n"
    path = tmp_path / "multiline.cnf"
    path.write_bytes(source.encode())
    result = sp.translate(str(path), language="dimacs", options={"packed": "1"})
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.to_smt2() == translate(source).to_smt2()


@pytest.mark.parametrize("packed", [False, True])
def test_counting_metadata_stays_attached_to_the_formula(packed):
    source = "c t pwmc\nc p weight 1 0.25 0\nc p show 1 3 0\np cnf 3 1\n1 -2 0\n"
    result = translate(source, packed)
    choices = json.loads(result.report.to_json())["choices"]
    assert any(item["strategy"] == "counting-weights" and "1=0.25" in item["rationale"]
               for item in choices)
    assert any(item["strategy"] == "counting-projection" and "2 variable" in item["rationale"]
               for item in choices)


@pytest.mark.parametrize("source,line", [
    ("p cnf 1 1\n1\nnope 0\n", 3),
    ("p cnf 1 1\n-9223372036854775808 0\n", 2),
    ("p cnf 1 1\n1\n", 2),
])
def test_invalid_clause_keeps_original_diagnostic_location(source, line):
    result = sp.translate(source=source, language="dimacs", options={"packed": "1"})
    assert not result.ok
    assert next(item for item in result.diagnostic_items if item.severity == sp.Severity.ERROR).line == line


def test_packed_option_requires_explicit_boolean_value():
    result = sp.translate(source="p cnf 0 0\n", language="dimacs", options={"packed": "yes"})
    assert not result.ok
    assert any("'packed'" in item.message for item in result.diagnostic_items)


def test_default_path_keeps_materialized_parser():
    result = sp.translate(source="p cnf 1 1\n1 0\n", language="dimacs")
    assert result.ok and result.has_parser and not result.uses_packed_smt_stream
