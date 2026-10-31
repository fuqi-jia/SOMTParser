"""Semantic checks for MiniZinc JSON data against equivalent DZN input."""

import json
from pathlib import Path

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


_ROOT = Path(__file__).resolve().parents[2]
_FIXTURES = _ROOT / "languages/minizinc/instances/ok/multifile"
_MODEL = _FIXTURES / "json_equiv.mzn"


def _solver(data_file):
    result = sp.translate(path=str(_MODEL), data=[str(_FIXTURES / data_file)],
                         language="minizinc")
    assert result.ok, result.diagnostic_items[0].message if result.diagnostic_items else "translation failed"
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    return solver


@pytest.mark.parametrize("data_file", ["json_equiv.json", "json_equiv.dzn"])
def test_json_and_dzn_data_have_the_expected_concrete_values(data_file):
    solver = _solver(data_file)
    assert solver.check() == z3.sat
    model = solver.model()
    assert model.eval(z3.Int("x"), model_completion=True).as_long() == 8
    assert model.eval(z3.Int("y"), model_completion=True).as_long() == 3

    # Each value is forced by different input fields and array indices. These
    # checks fail if array flattening, set membership, or index lookup drops a
    # constraint while still leaving some arbitrary satisfying assignment.
    solver.add(z3.Or(z3.Int("x") != 8, z3.Int("y") != 3))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("change", [
    lambda data: data.update(allowed={"set": [9, 10]}),
    lambda data: data["memberships"].__setitem__(1, [5, 11]),
    lambda data: data["memberships"].__setitem__(0, [1, 2]),
    lambda data: data["cube"][1][1].__setitem__(1, 7),
    lambda data: data.update(chosen="blue"),
    lambda data: data.update(label="different text"),
])
def test_each_json_data_field_is_semantically_necessary(change, tmp_path):
    data = json.loads((_FIXTURES / "json_equiv.json").read_text(encoding="utf-8"))
    change(data)
    changed_file = tmp_path / "changed.json"
    changed_file.write_text(json.dumps(data), encoding="utf-8")
    result = sp.translate(path=str(_MODEL), data=[str(changed_file)],
                         language="minizinc")
    assert result.ok, result.diagnostic_items[0].message if result.diagnostic_items else "translation failed"
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat


def test_json_surrogate_pair_quote_and_backslash_are_preserved(tmp_path):
    model = _FIXTURES / "json_escaped_string.mzn"
    data = _FIXTURES / "json_escaped_string.json"
    result = sp.translate(path=str(model), data=[str(data)], language="minizinc")
    assert result.ok, result.diagnostic_items[0].message if result.diagnostic_items else "translation failed"
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat

    wrong = json.loads(data.read_text(encoding="utf-8"))
    wrong["escaped"] = "😀\"/"
    wrong_data = tmp_path / "json_escaped_string_wrong.json"
    wrong_data.write_text(json.dumps(wrong), encoding="utf-8")
    changed = sp.translate(path=str(model), data=[str(wrong_data)], language="minizinc")
    assert changed.ok, changed.diagnostic_items[0].message if changed.diagnostic_items else "translation failed"
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(changed.to_smt2()))
    assert solver.check() == z3.unsat


def test_mixed_json_set_ranges_preserve_holes_and_endpoints(tmp_path):
    data = tmp_path / "ranges.json"
    data.write_text(json.dumps({"allowed": {"set": [8, [9, 10], [-3, -1]]}}))
    result = sp.translate(
        source="set of int: allowed; var int: x; constraint x in allowed; solve satisfy;",
        language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    for value in range(-4, 12):
        solver.push()
        solver.add(z3.Int("x") == value)
        expected = z3.sat if value in {-3, -2, -1, 8, 9, 10} else z3.unsat
        assert solver.check() == expected, value
        solver.pop()


def test_fixed_integer_set_does_not_hide_invalid_element_type():
    result = sp.translate(
        source="set of int: empty = {}; constraint true in empty; solve satisfy;",
        language="minizinc")
    assert not result.ok
    assert any("integer element" in d.message for d in result.diagnostic_items)


def test_json_multifile_fixture_preserves_actual_coordinate_values_and_set_holes():
    result = sp.translate(path=str(_FIXTURES / "json_data.mzn"),
                          data=[str(_FIXTURES / "json_data.json")],
                          language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    expected = z3.And(z3.Int("x") == 2, z3.Int("z") == 6,
                     z3.Or(*[z3.Int("y") == v for v in (5, 7, 8, 9)]))
    assert solver.check() == z3.sat
    # Both directions are checked: omitted source constraints and invented
    # restrictions must each yield a counterexample to this equivalence.
    mismatch = z3.Solver()
    actual = z3.And(*solver.assertions())
    mismatch.add(z3.Xor(actual, expected))
    assert mismatch.check() == z3.unsat
