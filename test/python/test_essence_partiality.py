"""Relational undefinedness from Savile Row 1.11.1 manual, section 3.

Negating an undefined numeric comparison differs from an undefined inequality.
These solver checks distinguish local guards from the former global constraints.
"""
from pathlib import Path

import pytest
import z3
import somtparser as sp


def translate(declarations, constraint):
    result = sp.translate(source="language ESSENCE' 1.0\n" + declarations +
                          '\nsuch that ' + constraint, language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    return result


def solver(result):
    s = z3.Solver()
    s.from_string(result.to_smt2())
    return s


@pytest.mark.parametrize('expression,expected', [
    ('x / 0 = 1', False), ('x / 0 != 1', False),
    ('!(x / 0 = 1)', True), ('!(x / 0 != 1)', True),
    ('(x / 0 = 1) = false', True), ('(x / 0 != 1) = false', True),
    ('x / 0 = x / 0', False), ('!(x / 0 = x / 0)', True),
    (r'(x / 0 + 1 = 4) \/ x = 2', True),
    ('x % 0 = 0', False), ('!(x % 0 = 0)', True),
    ('x = 2 -> x / 0 = 0', True),
    ('catchUndef(x / 0, 7) = 7', True),
    ('catchUndef(x / 0 + 1, 7) = 7', True),
    ('catchUndef(catchUndef(x / 0, 7) / 0, 8) = 8', True),
    ('catchUndef(x / 0 = 1, true) = false', True),
    ('sum([x / 0 | i : int(1..2)]) = 0', False),
    ('!(sum([x / 0 | i : int(1..2)]) = 0)', True),
    ('allDiff([x / 0])', False), ('!allDiff([x / 0])', True),
    ('alldifferent_except([x / 0, 2], 0)', False),
    ('!alldifferent_except([x / 0, 2], 0)', True),
    ('[x / 0, 1] <lex [2, 3]', False),
    ('!([x / 0, 1] <lex [2, 3])', True),
    ('catchUndef(min([x / 0, 2]), 9) = 9', True),
    ('min([x / 0, 2]) = 0', False),
    ('min([x | i : int(1..0)]) = 0', False),
    ('catchUndef(min([x | i : int(1..0)]), 9) = 9', True),
    ('sum([x / 0 | i : int(1..0)]) = 0', True),
    ('sum([x / 0 | i : int(1..2), i < 0]) = 0', True),
])
def test_arithmetic_closes_at_source_boolean_boundary(expression, expected):
    assert (solver(translate('find x: int(0..3)', expression)).check() == z3.sat) == expected


@pytest.mark.parametrize('element_type,expression,expected', [
    ('bool', '!m[0]', True), ('bool', 'm[0]', False),
    ('bool', 'm[0] = m[1]', True), ('bool', 'm[0] = m[0]', True),
    ('int(0..1)', 'm[0] = m[1]', False),
    ('int(0..1)', 'm[0] = m[0]', False),
    ('int(0..1)', '!(m[0] = m[1])', True),
    ('int(0..1)', 'm[0] != m[1]', False),
    ('int(0..1)', 'catchUndef(m[0], 7) = 7', True),
])
def test_boolean_reads_and_integer_reads_have_different_boundaries(element_type, expression, expected):
    result = translate('find m: matrix indexed by [int(1..2)] of ' + element_type, expression)
    assert (solver(result).check() == z3.sat) == expected


def test_dynamic_indices_and_division_for_each_assignment():
    declarations = ('find m: matrix indexed by [int(1..2), int(2..3)] of int(0..9)\n'
                    'find i: int(0..3)\nfind j: int(1..4)\nfind d: int(-1..1)')
    result = translate(declarations, '!(m[i, j] / d = 1)')
    s = solver(result)
    a = z3.Array('m', z3.IntSort(), z3.IntSort())
    s.add(*[z3.Select(a, k) == 1 for k in range(4)])
    for i in range(4):
        for j in range(1, 5):
            for d in range(-1, 2):
                s.push()
                s.add(z3.Int('i') == i, z3.Int('j') == j, z3.Int('d') == d)
                expected = not (1 <= i <= 2 and 2 <= j <= 3 and d == 1)
                assert (s.check() == z3.sat) == expected, (i, j, d)
                s.pop()


def test_nested_boolean_scope_does_not_consume_an_outer_numeric_guard():
    result = translate('find x: int(0..3)', 'x / 0 + toInt(!(x / 0 = 1)) = 1')
    assert solver(result).check() == z3.unsat


def test_constant_matrix_generator_uses_the_same_partiality_rule():
    result = translate('find x: int(0..3)',
        'and([!(m[0] = x) | m : matrix indexed by [int(1..1)] of int(0..1)])')
    assert solver(result).check() == z3.sat


@pytest.mark.parametrize('expression', ['catchUndef(x / 0, x)', 'catchUndef(x / 0, true)',
                                        'catchUndef(x / 0, 1 / 0)'])
def test_catch_requires_a_defined_constant_of_the_same_type(expression):
    result = sp.translate(source="language ESSENCE' 1.0\nfind x: int(0..3)\nsuch that " +
                          expression + ' = 1', language='essence')
    assert not result.ok


def test_undefined_objective_is_not_an_arbitrary_smt_value():
    result = sp.translate(source="language ESSENCE' 1.0\nfind x: int(0..3)\n"
                          'minimising x / 0\nsuch that true', language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    s = z3.Optimize()
    s.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    assert s.check() == z3.unsat


def test_original_basic_set07_has_the_reference_solution_and_no_other_cells():
    path = Path(__file__).resolve().parents[2] / 'languages/essence/instances/upstream/basic_set07.eprime'
    result = sp.translate(source=path.read_text(), language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    s = solver(result)
    assert s.check() == z3.sat
    occurrence = z3.Array('x_Occurrence', z3.IntSort(), z3.BoolSort())
    values = z3.Array('x_ExplicitVarSizeWithMarker_Values', z3.IntSort(), z3.IntSort())
    marker = z3.Int('x_ExplicitVarSizeWithMarker_Marker')
    reference = [marker == 3]
    reference += [z3.Select(occurrence, i) == (i <= 3) for i in range(1, 5)]
    reference += [z3.Select(values, i) == v for i, v in enumerate([1, 2, 3, 1], 1)]
    s.add(z3.Not(z3.And(*reference)))
    assert s.check() == z3.unsat
