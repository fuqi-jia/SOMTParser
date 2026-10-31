"""Computed large tables preserve their finite relation and array domains."""
import itertools

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _translate(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert any(strategy in result.report.to_json() for strategy in (
        "table-shared-characteristic-array", "table-shared-functional-array"))
    target = result.to_smt2(sp.OmtDialect.Z3)
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(target))
    return solver, target


@pytest.mark.parametrize("boolean", [False, True])
@pytest.mark.parametrize("negate", [False, True])
@pytest.mark.parametrize("origin", [1, -2])
def test_computed_table_matches_explicit_membership(boolean, negate, origin):
    rows = [(False, True), (True, False)] if boolean else [(-3, 4), (2, -3)]
    payload = ",".join(str(v).lower() for row in rows for v in row)
    typ = "bool" if boolean else "int"
    source = f"""
      array[1..4] of {typ}: data = [{payload}];
      array[{origin}..{origin + 1}] of var {typ}: x;
      constraint {'not ' if negate else ''}table(x,
        array2d(-5..122, {origin}..{origin + 1},
          [data[1 + ((u - 1) mod 4)] | u in 1..256]));
      solve satisfy;
    """
    solver, _ = _translate(source)
    x = z3.Array("x", z3.IntSort(), z3.BoolSort() if boolean else z3.IntSort())
    domain = [False, True] if boolean else [-4, -3, 0, 2, 4, 5]
    for pair in itertools.product(domain, repeat=2):
        solver.push()
        solver.add(x[origin] == pair[0], x[origin + 1] == pair[1])
        assert (solver.check() == z3.sat) == ((pair in rows) != negate), pair
        solver.pop()


@pytest.mark.parametrize("negate", [False, True])
def test_partial_tuple_still_closes_before_negation(negate):
    solver, _ = _translate(f"""
      constraint {'not ' if negate else ''}table([1 div 0, 7],
        array2d(1..128, 1..2, [if u mod 2 = 1 then 0 else 7 endif | u in 1..256]));
      solve satisfy;
    """)
    assert solver.check() == (z3.sat if negate else z3.unsat)


def test_per_generator_tables_have_distinct_contents():
    solver, _ = _translate("""
      array[1..2,1..2] of var int: x;
      constraint forall(j in 1..2)(table([x[j,1],x[j,2]],
        array2d(1..128,1..2,[if u mod 2 = 1 then j else 3*j endif | u in 1..256])));
      solve satisfy;
    """)
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    expected = z3.And(x[0] == 1, x[1] == 3, x[2] == 2, x[3] == 6)
    solver.push()
    solver.add(z3.Not(expected))
    assert solver.check() == z3.unsat
    solver.pop()
    assert solver.check() == z3.sat


@pytest.mark.parametrize("columns", ["2..3", "1..3"])
def test_computed_table_preserves_column_validation(columns):
    source = f"""
      array[1..2] of var int: x;
      constraint table(x,array2d(1..128,{columns},[u | u in 1..256]));
      solve satisfy;
    """
    assert not sp.translate(source=source, language="minizinc").ok


def test_equal_computed_tables_share_definitions():
    def emit(repetitions):
        _, target = _translate(f"""
          array[1..{repetitions},1..2] of var int:x;
          constraint forall(j in 1..{repetitions})(table([x[j,1],x[j,2]],
            array2d(1..128,1..2,[u | u in 1..256])));
          solve satisfy;
        """)
        return target
    single, repeated = emit(1), emit(10)
    assert single.count("define-fun") == repeated.count("define-fun")
    assert len(repeated) < 2 * len(single)
