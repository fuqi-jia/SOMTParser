"""Matrix values/slices, with an unchanged published CSPLib application."""
import ast
from pathlib import Path
import re

import pytest
import somtparser as sp
import z3


def translate(declarations, constraint):
    result = sp.translate(source="language ESSENCE' 1.0\n" + declarations +
                          "\nsuch that " + constraint, language="essence")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    return result


def solver(result):
    out = z3.Solver()
    out.set(timeout=30000)
    out.from_string(result.to_smt2())
    return out


def test_named_rectangular_matrix_preserves_source_index_domains():
    result = translate("letting P = [[2, 3; int(-1..0)], [5, 7; int(-1..0)]; int(3..4)]\n"
                       "find answer : int(0..100)",
                       "answer = P[3,-1] + 10*P[4,0]")
    check = solver(result)
    assert check.check() == z3.sat
    check.add(z3.Int('answer') != 72)
    assert check.check() == z3.unsat


def test_named_matrix_values_are_available_to_comprehension_guards():
    result = translate("letting P be [[0, 100], [1, 7], [2, 11]]\n"
                       "find answer : int(0..100)",
                       "answer = sum([P[i,2] | i : int(1..3), P[i,1] > 0])")
    check = solver(result)
    assert check.check() == z3.sat
    check.add(z3.Int('answer') != 18)
    assert check.check() == z3.unsat


@pytest.mark.parametrize('condition,expected', [
    ('P[1] /\\ !P[2]', True), ('P[0]', False), ('!P[0]', True),
])
def test_named_boolean_matrix_uses_boolean_read_boundary(condition, expected):
    result = translate("letting P = [true, false]\nfind x : int(0..1)", condition)
    assert solver(result).check() == (z3.sat if expected else z3.unsat)


@pytest.mark.parametrize('expression,truth', [
    ('sum(a[i,..]) = 6', [False, True, False, False]),
    ('!(sum(a[i,..]) = 6)', [True, False, True, True]),
    ('allDiff(a[i,..])', [False, True, True, False]),
    ('!allDiff(a[i,..])', [True, False, False, True]),
])
def test_symbolic_slice_indices_keep_numeric_partiality_local(expression, truth):
    result = translate('find a : matrix indexed by [int(-1..0), int(3..5)] of int(0..9)\n'
                       'find i : int(-2..1)', expression)
    check = solver(result)
    array = z3.Array('a', z3.IntSort(), z3.IntSort())
    check.add(*[z3.Select(array, k) == k + 1 for k in range(6)])
    for index, expected in zip(range(-2, 2), truth):
        check.push()
        check.add(z3.Int('i') == index)
        assert check.check() == (z3.sat if expected else z3.unsat), index
        check.pop()


@pytest.mark.parametrize('expression,expected', [
    ('or(a[i,..])', [False, True, False]),
    ('!or(a[i,..])', [True, False, True]),
    ('and(a[i,..])', [False, True, False]),
])
def test_boolean_slice_invalid_cells_close_before_fold(expression, expected):
    result = translate('find a : matrix indexed by [int(1..1), int(1..2)] of bool\n'
                       'find i : int(0..2)', expression)
    check = solver(result)
    array = z3.Array('a', z3.IntSort(), z3.BoolSort())
    check.add(z3.Select(array, 0), z3.Select(array, 1))
    for index, truth in enumerate(expected):
        check.push()
        check.add(z3.Int('i') == index)
        assert check.check() == (z3.sat if truth else z3.unsat)
        check.pop()


def test_column_slice_and_whole_vector_fold():
    result = translate('find a : matrix indexed by [int(-1..0), int(3..5)] of int(0..9)\n'
                       'find b : matrix indexed by [int(3..4)] of int(0..9)',
                       'sum(a[..,4]) = sum(b)')
    check = solver(result)
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    b = z3.Array('b', z3.IntSort(), z3.IntSort())
    check.add(*[z3.Select(a, k) == k + 1 for k in range(6)])
    check.add(z3.Select(b, 3) == 3, z3.Select(b, 4) == 4)
    assert check.check() == z3.sat


def test_flatten_multiple_retained_dimensions_uses_row_major_order():
    result = translate('find a : matrix indexed by [int(1..2), int(3..4), int(-1..0)] of int(0..9)',
                       'flatten(a[2,..,..]) <=lex [5,6,7,8], '
                       '[5,6,7,8] <=lex flatten(a[2,..,..])')
    check = solver(result)
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    check.add(*[z3.Select(a, k) == k + 1 for k in range(8)])
    assert check.check() == z3.sat


@pytest.mark.parametrize('declarations,constraint,diagnostic', [
    ('letting P = [[1,2], [3]]', 'true', 'identical index domains'),
    ('letting P = [true, 1]', 'true', 'mix Boolean and integer'),
    ('letting P = [2,3; int(1,3)]', 'true', 'contiguous integer'),
    ('letting P = []', 'true', 'empty named matrix'),
    ('letting P = [1,2]\nletting P be 3', 'true', 'already declared'),
    ('letting P = [1,2]\nletting P be domain int(1..2)', 'true', 'already declared'),
    ('letting P = [1,2]\nfind P : int(0..2)', 'true', 'already declared'),
    ('find a : matrix indexed by [int(1..2), int(1..2)] of int(0..9)',
     'sum(a) = 0', 'retain one matrix dimension'),
    ('find a : matrix indexed by [int(1..2), int(1..2)] of int(0..9)',
     'sum(a[..]) = 0', 'number of matrix slice subscripts'),
])
def test_unsupported_or_ill_shaped_matrix_values_are_explicit(declarations, constraint, diagnostic):
    result = sp.translate(source="language ESSENCE' 1.0\n" + declarations +
                          '\nsuch that ' + constraint, language='essence')
    assert not result.ok
    assert any(diagnostic in item.message for item in result.diagnostic_items)


def _published_killer_sudoku():
    path = (Path(__file__).resolve().parents[2] / 'languages/essence/instances/csplib/'
            'killer_sudoku.eprime')
    source = path.read_text()
    cages = ast.literal_eval(re.search(r'letting P\s*=\s*(\[.*?\])\s*\$ decision variables',
                                     source, re.S).group(1))
    result = sp.translate(source=source, language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    return result, cages


def _killer_reference(cages):
    matrix = z3.Array('x', z3.IntSort(), z3.IntSort())
    cells = [[z3.Select(matrix, row*9 + col) for col in range(9)] for row in range(9)]
    clauses = [z3.And(value >= 1, value <= 9) for row in cells for value in row]
    clauses += [z3.Distinct(row) for row in cells]
    clauses += [z3.Distinct([cells[r][c] for r in range(9)]) for c in range(9)]
    clauses += [z3.Distinct([cells[r][c] for r in range(br, br+3) for c in range(bc, bc+3)])
                for br in range(0, 9, 3) for bc in range(0, 9, 3)]
    # The published source imposes cage sums; it does not add a cage allDiff.
    # Preserve that exact formal model rather than importing extra prose rules.
    clauses += [z3.Sum([cells[cage[k]-1][cage[k+1]-1] for k in range(0, 8, 2)
                       if cage[k] > 0]) == cage[8] for cage in cages]
    return z3.And(clauses), cells


def test_complete_csplib_model_matches_independent_explicit_constraints():
    result, cages = _published_killer_sudoku()
    assert len(cages) == 29
    reference, _ = _killer_reference(cages)
    target = z3.And(list(z3.parse_smt2_string(result.to_smt2())))
    check = z3.Solver()
    check.set(timeout=30000)
    check.add(z3.Xor(reference, target))
    assert check.check() == z3.unsat


def test_complete_csplib_model_admits_its_published_solution():
    result, cages = _published_killer_sudoku()
    _, cells = _killer_reference(cages)
    solution = [
        [2,1,5,6,4,7,3,9,8], [3,6,8,9,5,2,1,7,4], [7,9,4,3,8,1,6,5,2],
        [5,8,6,2,7,4,9,3,1], [1,4,2,5,9,3,8,6,7], [9,7,3,8,1,6,4,2,5],
        [8,2,1,7,3,9,5,4,6], [6,5,9,4,2,8,7,1,3], [4,3,7,1,6,5,2,8,9],
    ]
    check = solver(result)
    check.add(*[cells[r][c] == solution[r][c] for r in range(9) for c in range(9)])
    assert check.check() == z3.sat


@pytest.mark.parametrize('declarations,constraint', [
    ('letting n be P[1]\nfind x : int(0..1)', 'x = n'),
    ('letting Q = [P[1]]\nfind x : int(0..1)', 'x = Q[1]'),
    ('find x : int(0..P[1])', 'true'),
    ('find x : matrix indexed by [int(1..P[1])] of bool', 'true'),
    ('letting Q = [7]\nfind x : int(0..9)', 'x = Q[P[1]]'),
    ('find x : int(0..9)', 'x = sum([i | i : int(1..P[1])])'),
    ('where P[1] = 1\nfind x : int(0..1)', 'true'),
])
def test_boolean_matrix_cells_coerce_in_integer_elaboration_contexts(declarations, constraint):
    result = sp.translate(source="language ESSENCE' 1.0\nletting P = [true]\n" +
                          declarations + '\nsuch that ' + constraint, language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert solver(result).check() == z3.sat


@pytest.mark.parametrize('guard', ['b[1] + 1 = 2', 'b[1] = 1'])
def test_constant_guard_uses_implicit_boolean_numeric_coercion(guard):
    result = sp.translate(source="language ESSENCE' 1.0\nfind x : int(0..2)\n"
                          'such that x = sum([1 | b : matrix indexed by [int(1..1)] of bool, '
                          + guard + '])', language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    check = solver(result)
    assert check.check() == z3.sat
    check.add(z3.Int('x') != 1)
    assert check.check() == z3.unsat


def test_boolean_matrix_generator_guard_remains_a_boolean_condition():
    result = translate('find x : int(0..2)',
                       'x = sum([1 | b : matrix indexed by [int(1..1)] of bool, b[1]])')
    check = solver(result)
    assert check.check() == z3.sat
    check.add(z3.Int('x') != 1)
    assert check.check() == z3.unsat
