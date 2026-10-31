"""DZN EOF may delimit the final assignment without hiding malformed data."""

import pytest
import z3
import somtparser as sp


@pytest.mark.parametrize("model,data", [
    ("int:n; constraint n=7;", "n=7"),
    ("int:n; constraint n=7;", "n=7 % final comment ;"),
    ("int:n; constraint n=7;", "n=7 /* final comment ; */"),
    ('string:s; constraint s=";";', 's=";"'),
    ("array[1..2,1..2] of int:a; constraint a[2,2]=4;", "a=[|1,2|3,4|]"),
    ("enum E; E:e; constraint e=B;", "e=B; E={A,B}"),
    ("int:n; int:m; constraint n+m=9;", "n=7; m=2"),
    ("int:n; constraint n=7;", "n=7; % already delimited"),
    ("constraint true;", "% empty data file"),
])
def test_final_assignment_without_semicolon(tmp_path, model, data):
    path = tmp_path / "values.dzn"
    path.write_text(data)
    result = sp.translate(source=model + "solve satisfy;", language="minizinc", data=[str(path)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("data", [
    "n=7 m=2", "n=7; m=", "n=7; m=[2", "n=7; m=2 /* unclosed",
    'n=7; m="unclosed', "n=7; constraint false", "n=7; m=2)" ,
])
def test_eof_normalization_does_not_accept_malformed_data(tmp_path, data):
    path = tmp_path / "bad.dzn"
    path.write_text(data)
    result = sp.translate(source="int:n; int:m; solve satisfy;", language="minizinc", data=[str(path)])
    assert not result.ok
    assert result.diagnostic_items


def test_implicit_delimiters_remain_independent_between_data_files(tmp_path):
    paths = [tmp_path / "n.dzn", tmp_path / "m.dzn"]
    for path, data in zip(paths, ["n=7 % eof", "m=2"]):
        path.write_text(data)
    result = sp.translate(source="int:n; int:m; constraint n+m!=9; solve satisfy;",
                          language="minizinc", data=[str(path) for path in paths])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat
