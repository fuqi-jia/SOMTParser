"""Explicit HiGHS warning recovery; strict MPS acceptance is unchanged."""
from pathlib import Path

import pytest
import z3
import somtparser as sp


def translate(source, recover=True):
    return sp.translate(source=source, language='mps',
        options={'highs_warning_recovery': '1' if recover else '0'})


def read(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    opt = z3.Optimize()
    opt.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    return opt


@pytest.mark.parametrize('first,expected', [('0', 9), ('2', 2)])
def test_first_nonzero_coefficients_follow_reference_probe(first, expected):
    source = f'''NAME T
ROWS
 N COST
 G R
COLUMNS
    X COST {first} R {first}
    X COST 9 R 9
RHS
    RHS R 1
ENDATA
'''
    opt = read(translate(source))
    objective = opt.objectives()[0]
    assert z3.simplify(z3.substitute(objective, (z3.Real('X'), z3.RealVal(1)))).as_fraction() == expected
    for value in (0, 1, 2):
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Real('X') == value)
        assert (solver.check() == z3.sat) == (expected * value >= 1)


def test_first_rhs_range_bounds_and_undefined_rows_are_reported():
    source = '''NAME T
ROWS
 N COST
 G R
COLUMNS
    X COST 1 R 1
    X MISSING 100
RHS
    B MISSING 100 R 2
    B R 99
RANGES
    B R 1
    B R 99 COST 5
BOUNDS
 UP B X 3
 UP B X 99
 UP B EXTRA 1
ENDATA
'''
    assert not translate(source, recover=False).ok
    result = translate(source)
    opt = read(result)
    assert any('highs-warning-recovery' == c.strategy for c in result.report.choices)
    assert len(result.report.warnings) >= 5
    for x in range(5):
        for extra in range(3):
            solver = z3.Solver()
            solver.add(*opt.assertions(), z3.Real('X') == x, z3.Real('EXTRA') == extra)
            assert (solver.check() == z3.sat) == (2 <= x <= 3 and 0 <= extra <= 1)


def test_negative_upper_bound_preserves_highs_zero_lower_default():
    source = '''NAME T
ROWS
 N COST
COLUMNS
    X COST -1
BOUNDS
 UP B X -1
ENDATA
'''
    assert read(translate(source)).check() == z3.unsat
    assert read(translate(source, recover=False)).check() == z3.sat


def test_original_warnings_preserves_first_objective_and_bounds_only_column():
    path = Path(__file__).resolve().parents[2] / 'languages/mps/instances/upstream/warnings.mps'
    source = path.read_text()
    assert not translate(source, recover=False).ok
    result = translate(source)
    opt = read(result)
    # Independent HiGHS 1.15.1 import: costs -1 for C0..C8, 0 for C10.
    replacements = [(z3.Real(f'C{i}'), z3.RealVal(1)) for i in (0, 6, 7, 8, 10)]
    replacements += [(z3.Int(f'C{i}'), z3.IntVal(1)) for i in range(1, 6)]
    assert z3.simplify(z3.substitute(opt.objectives()[0], *replacements)).as_fraction() == -9
    assert '(declare-fun C10 ' in result.to_smt2()
    assert opt.check() == z3.unsat


@pytest.mark.parametrize('name', ['nan0', 'nan1', 'nan2', 'garbage'])
def test_recovery_does_not_accept_nonfinite_or_malformed_records(name):
    path = Path(__file__).resolve().parents[2] / f'languages/mps/instances/upstream/{name}.mps'
    assert not translate(path.read_text()).ok
