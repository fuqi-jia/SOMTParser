"""Exact named finite-set domains for MiniZinc parameter and decision arrays."""

import json

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


def _translate(source, data=()):
    result = sp.translate(source=source, language="minizinc", data=list(data))
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


@pytest.mark.parametrize("kind", ["dzn", "json"])
def test_named_set_array_accepts_supplied_dzn_and_json_values(kind, tmp_path):
    model = (
        "set of int: Ori = {1, 3};\n"
        "array[1..2] of set of Ori: rm_ori;\n"
        "constraint 1 in rm_ori[1];\n"
        "constraint 3 in rm_ori[2];\n"
        "solve satisfy;\n"
    )
    values = [{"set": [1, 3]}, {"set": [3]}]
    data_file = tmp_path / ("sets." + kind)
    if kind == "json":
        data_file.write_text(json.dumps({"rm_ori": values}), encoding="utf-8")
    else:
        data_file.write_text("rm_ori = [{1, 3}, {3}];\n", encoding="utf-8")

    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(_translate(model, [str(data_file)]).to_smt2()))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("kind", ["dzn", "json"])
def test_supplied_set_array_rejects_a_value_in_sparse_domain_hole(kind, tmp_path):
    model = (
        "set of int: Ori = {1, 3};\n"
        "array[1..1] of set of Ori: rm_ori;\n"
        "solve satisfy;\n"
    )
    data_file = tmp_path / ("outside." + kind)
    if kind == "json":
        data_file.write_text(
            json.dumps({"rm_ori": [{"set": [1, 2, 3]}]}), encoding="utf-8")
    else:
        data_file.write_text("rm_ori = [{1, 2, 3}];\n", encoding="utf-8")

    result = sp.translate(source=model, language="minizinc", data=[str(data_file)])
    assert not result.ok
    assert any("outside set element type 'Ori'" in d.message
               for d in result.diagnostic_items)


def test_sparse_named_decision_domain_forces_members_and_rejects_holes():
    model = (
        "set of int: D = {-2, 3};\n"
        "array[1..2] of var D: x;\n"
        "solve satisfy;\n"
    )
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(_translate(model).to_smt2()))
    assert solver.check() == z3.sat

    # Assignment to a value between the two allowed members is impossible;
    # a min/max-only encoding would incorrectly make this satisfiable.
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    solver.add(z3.Select(x, 1) == 0)
    assert solver.check() == z3.unsat


def test_singleton_named_domain_forces_assignment_against_its_negation():
    model = (
        "set of int: D = {3};\n"
        "var D: x;\n"
        "solve satisfy;\n"
    )
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(_translate(model).to_smt2()))
    x = z3.Int("x")
    assert solver.check() == z3.sat
    solver.add(x != 3)
    assert solver.check() == z3.unsat
