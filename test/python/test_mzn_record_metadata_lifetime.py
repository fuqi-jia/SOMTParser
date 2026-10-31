"""Record metadata stays alive exactly while its source values are reachable."""
import json

import pytest
import z3

import somtparser as sp


SCHEMA = """
type Duty = record(int: day, int: load);
type Staff = record(int: id, list of Duty: duties);
list of Staff: staff;
function int: capacity(Staff: person, int: day) =
  [d.load | d in person.duties where d.day = day][1];
"""
DATA = {"staff": [
    {"id": 1, "duties": [{"day": i + 1, "load": x}
                          for i, x in enumerate([2, 5, 11])]},
    {"id": 2, "duties": [{"day": i + 1, "load": x}
                          for i, x in enumerate([3, 7, 13])]},
]}


def translate(tmp_path, body):
    data = tmp_path / "staff.json"
    data.write_text(json.dumps(DATA))
    result = sp.translate(source=SCHEMA + body + "\nsolve satisfy;",
                          language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


@pytest.mark.parametrize("repetitions", [1, 1600])
def test_live_array_views_and_partial_reads_survive_record_expansion(tmp_path, repetitions):
    # The large form repeatedly enters record-valued generators and fixed
    # functions, as the official iHTC model does. The first dynamic array view
    # and its partial read remain live while those temporaries are discarded.
    actual = translate(tmp_path, fr"""
array[1..3] of int: loads = [d.load | d in staff[1].duties];
var int: day;
var int: proposed;
var bool: accepted;
constraint accepted = (loads[day] = proposed);
var int: total;
constraint total = sum(rep in 1..{repetitions}, person in staff)(
  capacity(person, 1 + rep mod 3));
var int: recovered;
constraint recovered = (loads[day] default -17);
constraint staff[1].id = 1 /\ staff[2].duties[3].load = 13;
""")
    day, proposed, total, recovered = z3.Ints("day proposed total recovered")
    values = [2, 5, 11]
    expected_total = sum([5, 12, 24][rep % 3] for rep in range(1, repetitions + 1))
    expected = z3.And(
        z3.Bool("accepted") == z3.Or(*[
            z3.And(day == i + 1, proposed == value) for i, value in enumerate(values)]),
        total == expected_total,
        recovered == z3.If(day == 1, 2, z3.If(day == 2, 5, z3.If(day == 3, 11, -17))),
    )
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_shadowed_record_lists_restore_live_outer_metadata(tmp_path):
    actual = translate(tmp_path, """
var int: selected;
var int: outer_total;
constraint selected = let {
  list of Staff: staff = [person | person in staff where person.id = 2]
} in sum(rep in 1..1600, person in staff)(capacity(person, 1));
constraint outer_total = sum(person in staff)(capacity(person, 1));
constraint length(staff[1].duties) = 3;
""")
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, z3.And(z3.Int("selected") == 4800,
                                    z3.Int("outer_total") == 5)))
    assert solver.check() == z3.unsat
