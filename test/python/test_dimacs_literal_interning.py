"""Semantic regression checks for the DIMACS immutable literal cache."""
import json

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _target(source):
    translated = sp.translate(source=source, language="dimacs")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    return translated, z3.And(*z3.parse_smt2_string(translated.to_smt2()))


def _equivalent(source_formula, translated_formula):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(source_formula, translated_formula))
    assert solver.check() == z3.unsat


def test_repeated_literals_preserve_cnf_and_header_vocabulary():
    source = ("p cnf 4 4\n"
              "1 1 -2 0\n"
              "1 -2 -1 0\n"
              "-1 2 0\n"
              "3 0\n")
    translated, target = _target(source)
    x1, x2, x3, x4 = [z3.Bool(f"x{i}") for i in range(1, 5)]
    expected = z3.And(z3.Or(x1, x1, z3.Not(x2)),
                      z3.Or(x1, z3.Not(x2), z3.Not(x1)),
                      z3.Or(z3.Not(x1), x2), x3)
    _equivalent(expected, target)
    assert "declare-fun x4 () Bool" in translated.to_smt2()


def test_empty_clause_and_contradictory_units_remain_unsatisfiable():
    for source in ("p cnf 2 1\n0\n", "p cnf 1 2\n1 0\n-1 0\n"):
        _, formula = _target(source)
        solver = z3.Solver()
        solver.add(formula)
        assert solver.check() == z3.unsat


def test_counting_weights_and_projection_metadata_are_preserved():
    source = ("c t pwmc\n"
              "c p weight 1 0.25 0\n"
              "c p show 1 3 0\n"
              "p cnf 3 1\n1 -2 0\n")
    translated = sp.translate(source=source, language="dimacs")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    choices = json.loads(translated.report.to_json())["choices"]
    assert any(c["strategy"] == "counting-weights" and "0.25" in c["rationale"]
               for c in choices)
    assert any(c["strategy"] == "counting-projection" and "2 variable" in c["rationale"]
               for c in choices)


def test_malformed_clause_diagnostic_keeps_original_line():
    translated = sp.translate(source="p cnf 1 1\n1\nx 0\n", language="dimacs")
    assert not translated.ok
    error = next(d for d in translated.diagnostic_items if d.severity == sp.Severity.ERROR)
    assert error.line == 3


def test_unrepresentable_negative_variable_index_is_a_parse_error_at_its_line():
    translated = sp.translate(
        source="p cnf 1 1\n-9223372036854775808 0\n", language="dimacs")
    assert not translated.ok
    error = next(d for d in translated.diagnostic_items if d.severity == sp.Severity.ERROR)
    assert error.line == 2
    assert "magnitude" in error.message
