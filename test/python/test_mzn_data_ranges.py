"""Official .dzn index sets use bare ranges, not only braced set literals."""
import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize("value,members", [
    ("1..3", [1, 2, 3]), ("-3..-1", [-3, -2, -1]),
    ("4..2", []), ("1..2 union {5,9}", [1, 2, 5, 9]),
    ("(1+1)..(2*2)", [2, 3, 4]),
])
def test_data_range_and_alias_preserve_exact_membership(tmp_path, value, members):
    path = tmp_path / "instance.dzn"
    path.write_text(f"S = {value}; T = S; n = 2 + 3;")
    source = "set of int: S; set of int: T; int: n; var int: x; constraint x in T; constraint n = 5; solve satisfy;"
    result = sp.translate(source=source, language="minizinc", data=[str(path)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    expected = z3.Or([z3.Int("x") == i for i in members])
    solver = z3.Solver(); solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_data_ranges_supply_multidimensional_index_sets(tmp_path):
    path = tmp_path / "jobs.dzn"
    path.write_text("JOBS = 1..2; MACHINES = -1..0; times = array2d(JOBS, MACHINES, [1,2,3,4]);")
    source = "set of int: JOBS; set of int: MACHINES; array[JOBS,MACHINES] of int: times; var int: z :: output = sum(j in JOBS,m in MACHINES)(times[j,m]); constraint z != 10; solve satisfy;"
    result = sp.translate(source=source, language="minizinc", data=[str(path)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert solver.check() == z3.unsat
