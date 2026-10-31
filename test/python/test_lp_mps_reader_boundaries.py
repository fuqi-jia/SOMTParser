"""Reader boundary regressions, including explicit reader-dialect differences.

The corpus contains accepted dialect variants and labels named after keywords.
Check the retained constraints and optima, not just successful parsing.
"""
from pathlib import Path

import pytest
import z3
import somtparser as sp

ROOT = Path(__file__).resolve().parents[2]


def read(source, language):
    result = sp.translate(source=source, language=language)
    assert result.ok, [d.message for d in result.diagnostic_items]
    s = z3.Optimize()
    s.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    return result, s


@pytest.mark.parametrize('header', ['subject to', 'SUBJECT TO', 'such that', 'st', 's.t.'])
def test_inline_lp_constraint_header_preserves_objective_and_feasible_set(header):
    result, opt = read(f'Minimize a {header} a >= 1\n', 'lp')
    assert opt.check() == z3.sat
    assert opt.model().eval(opt.objectives()[0]).as_fraction() == 1
    assert any(c.strategy == 'gurobi-inline-constraint-header' for c in result.report.choices)
    for value in (-1, 0, 1, 2):
        s = z3.Solver()
        s.add(*opt.assertions(), z3.Real('a') == value)
        assert (s.check() == z3.sat) == (value >= 1)


def test_inline_header_with_objective_continuation_and_constraint_labels():
    _, opt = read('Minimize\nobj: a +\nb subject to bounds: a + b >= 1\nBounds\n'
                  'a <= 0.5\nEnd\n', 'lp')
    assert opt.check() == z3.sat
    assert opt.model().eval(opt.objectives()[0]).as_fraction() == 1


@pytest.mark.parametrize('label', ['end', 'bounds', 'subject', 'min', 'max', 'binary', 'st'])
def test_keyword_constraint_labels_do_not_end_or_switch_sections(label):
    _, opt = read(f'Minimize\n x\nSubject To\n {label}: x - 1 >= 2\nInteger\n x\nEnd\n', 'lp')
    assert opt.check() == z3.sat
    assert opt.model().eval(z3.Int('x')).as_long() == 3
    s = z3.Solver()
    s.add(*opt.assertions(), z3.Int('x') == 0)
    assert s.check() == z3.unsat


def test_partial_header_words_can_be_variable_names():
    _, opt = read('Minimize\nsubject + to\nSubject To\nsubject >= 1\nto >= 2\nEnd\n', 'lp')
    assert opt.check() == z3.sat
    assert opt.model().eval(opt.objectives()[0]).as_fraction() == 3


def test_original_lp_cases_and_inline_bounds_refusal():
    for name, optimum in [('1449b.lp', 1), ('1451.lp', 3)]:
        _, opt = read((ROOT/'languages/lp/instances/upstream'/name).read_text(), 'lp')
        assert opt.check() == z3.sat
        value = opt.model().eval(opt.objectives()[0])
        assert (value.as_long() if z3.is_int_value(value) else value.as_fraction()) == optimum
    for name in ['1448.lp', '1449a.lp', 'garbage.lp']:
        result = sp.translate(source=(ROOT/'languages/lp/instances/upstream'/name).read_text(), language='lp')
        assert not result.ok


def test_original_mps_inline_comments_preserve_complete_model():
    result, opt = read((ROOT/'languages/mps/instances/upstream/comment.mps').read_text(), 'mps')
    assert any(c.strategy == 'trailing-asterisk-comment' for c in result.report.choices)
    assert opt.check() == z3.sat
    assert opt.model().eval(opt.objectives()[0]).as_fraction() == -4
    for c0 in (-1, 0, 1, 2):
        for c1 in (-1, 0, 1, 2, 3):
            s = z3.Solver()
            s.add(*opt.assertions(), z3.Real('C0') == c0, z3.Real('C1') == c1)
            assert (s.check() == z3.sat) == (0 <= c0 <= 1 and c1 >= 0 and 1 <= c0+c1 <= 2)


@pytest.mark.parametrize('column,row', [('*X', 'R'), ('$X', 'R'), ('X*Y', 'R$Y'),
                                        ('X$Y', 'R*Y'), ('X', '*R'), ('X', '$R')])
def test_mps_comment_markers_in_names_are_not_dropped(column, row):
    _, opt = read(f'NAME T\nROWS\n N COST\n L {row}\nCOLUMNS\n'
                  f'    {column} COST 1 {row} 1\nRHS\n    B {row} 2\nENDATA\n', 'mps')
    assert opt.check() == z3.sat
    assert opt.model().eval(opt.objectives()[0]).as_fraction() == 0
    s = z3.Solver()
    s.add(*opt.assertions(), z3.Real(column) == 3)
    assert s.check() == z3.unsat


def test_undeclared_marked_row_with_coefficient_is_not_silently_a_comment():
    source = 'NAME T\nROWS\n N COST\nCOLUMNS\n    X COST 1 *UNKNOWN 2\nENDATA\n'
    result = sp.translate(source=source, language='mps')
    assert not result.ok


def test_numeric_lhs_names_match_reference_reader_only_when_selected():
    source = (ROOT/'languages/lp/instances/upstream/1451.lp').read_text()
    for mode, expected in [('constants', 3), ('variables', 2)]:
        result = sp.translate(source=source, language='lp', options={'lhs_numbers': mode})
        assert result.ok, [d.message for d in result.diagnostic_items]
        opt = z3.Optimize()
        opt.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
        assert opt.check() == z3.sat
        assert opt.model().eval(opt.objectives()[0]).as_long() == expected
        strategy = 'numeric-variable-names' if mode == 'variables' else 'mathematical-lhs-constants'
        assert any(c.strategy == strategy for c in result.report.choices)
        if mode == 'variables':
            # The numerical-looking source variable must remain an SMT symbol.
            assert opt.model().eval(z3.Real('1')).as_fraction() == 0


@pytest.mark.parametrize('header', ['bounds', 'Bounds', 'bound'])
@pytest.mark.parametrize('upper,expected', [('0', z3.unsat), ('3', z3.sat)])
def test_explicit_inline_bounds_preserves_row_bounds_and_objective(header, upper, expected):
    source = f'Minimize a subject to bounds: a >= 1 {header} a <= {upper}\n'
    assert not sp.translate(source=source, language='lp').ok
    result = sp.translate(source=source, language='lp', options={'inline_bounds': 'true'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert any(c.strategy == 'explicit-inline-bounds' for c in result.report.choices)
    optimizer = z3.Optimize()
    optimizer.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    assert optimizer.check() == expected
    if expected == z3.sat:
        assert optimizer.model().eval(optimizer.objectives()[0]).as_fraction() == 1
    for value in [-1, 0, 1, 2, 3, 4]:
        solver = z3.Solver()
        solver.add(*optimizer.assertions(), z3.Real('a') == value)
        assert (solver.check() == z3.sat) == (1 <= value <= int(upper))


def test_inline_bounds_keyword_in_lhs_is_not_a_section_boundary():
    result = sp.translate(source='Minimize a subject to r: a + bounds >= 1 bounds a <= 3\n',
                          language='lp', options={'inline_bounds': 'true'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    optimizer = z3.Optimize()
    optimizer.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    assert optimizer.check() == z3.sat
    assert optimizer.model().eval(optimizer.objectives()[0]).as_fraction() == 0
    for a, b in [(0, 0), (0, 1), (1, 0), (4, 0), (2, -1)]:
        solver = z3.Solver()
        solver.add(*optimizer.assertions(), z3.Real('a') == a, z3.Real('bounds') == b)
        assert (solver.check() == z3.sat) == (0 <= a <= 3 and b >= 0 and a + b >= 1)


def test_original_1449a_translates_only_under_explicit_inline_bounds_extension():
    path = ROOT / 'languages/lp/instances/upstream/1449a.lp'
    assert not sp.translate(str(path), language='lp').ok
    result = sp.translate(str(path), language='lp', options={'inline_bounds': 'true'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    optimizer = z3.Optimize()
    optimizer.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    assert optimizer.check() == z3.unsat
    assert len(optimizer.objectives()) == 1


def test_inline_bounds_option_rejects_typos_and_incomplete_rows():
    for option in ['yes', '1', 'sometimes']:
        assert not sp.translate(source='Minimize x\n', language='lp',
                                options={'inline_bounds': option}).ok
    for source in ['Minimize a subject to a >= bounds a <= 3',
                   'Minimize a subject to a >= bad bounds a <= 3',
                   'Minimize a subject to a >= 1 + bounds a <= 3']:
        result = sp.translate(source=source, language='lp', options={'inline_bounds': 'true'})
        assert not result.ok
        assert all(d.code != sp.ErrorCode.E_INTERNAL for d in result.diagnostic_items)


def test_inline_bounds_with_multiple_rows_and_continuation():
    source = 'Minimize a\nSubject to\nr1: a >= 1\nr2: a +\nb >= 2 Bounds a <= 3\nEnd\n'
    result = sp.translate(source=source, language='lp', options={'inline_bounds': 'true'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    optimizer = z3.Optimize()
    optimizer.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    for a, b in [(0, 2), (1, 0), (1, 1), (3, 0), (4, 0), (2, -1)]:
        solver = z3.Solver()
        solver.add(*optimizer.assertions(), z3.Real('a') == a, z3.Real('b') == b)
        assert (solver.check() == z3.sat) == (1 <= a <= 3 and b >= 0 and a + b >= 2)
