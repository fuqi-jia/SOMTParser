"""Matrix parameter shape/inference rules follow Savile Row 1.11.1.

Reference: ModelContainer.processGiven/processLetting and
ConstantMatrixStore.makeLettingsConstantMatrix/correctIndicesConstantMatrix.
"""
from pathlib import Path

import pytest
import somtparser as sp
import z3


def translated(tmp_path, declaration, params, expression, *, good=True):
    data = tmp_path / 'instance.param'
    data.write_text(params)
    result = sp.translate(source="language ESSENCE' 1.0\n" + declaration +
                          '\nsuch that ' + expression, data=[str(data)], language='essence')
    if good:
        assert result.ok, [d.message for d in result.diagnostic_items]
        assert result.report.fidelity.sound and result.report.fidelity.complete
    else:
        assert not result.ok
    return result


def solver(result):
    check = z3.Solver()
    check.from_string(result.to_smt2())
    return check


def test_official_quasigroup_style_matrix_parameter_reaches_every_cell(tmp_path):
    result = translated(tmp_path,
        'given N: int(1..)\ngiven start: matrix indexed by [int(1..N), int(1..N)] of int(0..N)\n'
        'find x: matrix indexed by [int(1..N), int(1..N)] of int(0..N)',
        "language ESSENCE' 1.0\nletting N = 2\nletting start = [[1,0],[0,2]]",
        'forall i,j: int(1..N) . x[i,j] = start[i,j]')
    check = solver(result)
    x = z3.Array('x', z3.IntSort(), z3.IntSort())
    assert check.check() == z3.sat
    check.add(z3.Not(z3.And(*[z3.Select(x, i) == v for i,v in enumerate([1,0,0,2])])))
    assert check.check() == z3.unsat


@pytest.mark.parametrize('domain,expression', [
    ('int(0..2)', 'M[0] = 7 /\\ M[2] = 9'),
    ('int(-2..0)', 'M[-2] = 7 /\\ M[0] = 9'),
    ('int(3..5)', 'M[3] = 7 /\\ M[5] = 9'),
])
def test_given_reindexes_without_permuting_parameter_cells(tmp_path, domain, expression):
    result = translated(tmp_path, 'given M: matrix indexed by [' + domain + '] of int',
                        'letting M = [7,8,9]', expression)
    assert solver(result).check() == z3.sat
    assert any('reindexed' in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize('domain,expression', [
    ('int(1..n)', 'n = 3 /\\ M[1] = 7 /\\ M[n] = 9'),
    ('int(0..last)', 'last = 2 /\\ M[0] = 7 /\\ M[last] = 9'),
    ('int(first..5)', 'first = 3 /\\ M[first] = 7 /\\ M[5] = 9'),
])
def test_single_unknown_endpoint_is_inferred_from_actual_extent(tmp_path, domain, expression):
    result = translated(tmp_path, 'given M: matrix indexed by [' + domain + '] of int',
                        'letting M = [7,8,9]', expression)
    assert solver(result).check() == z3.sat


def test_plotting_style_infers_two_dimensions_and_constant_flatten_max(tmp_path):
    result = translated(tmp_path,
        'given grid: matrix indexed by [int(1..height), int(1..width)] of int(0..)\n'
        'letting colours be max(flatten(grid))\nfind x: int(0..colours)',
        'letting grid = [[1,2,3],[2,1,2]]',
        'height = 2 /\\ width = 3 /\\ x = colours')
    check = solver(result)
    assert check.check() == z3.sat
    check.add(z3.Int('x') != 3)
    assert check.check() == z3.unsat


@pytest.mark.parametrize('params,declaration', [
    ('letting M = [[1,2],[3]]', 'given M: matrix indexed by [int(1..2),int(1..2)] of int'),
    ('letting M = [1,2]', 'given M: matrix indexed by [int(1..3)] of int'),
    ('letting M = [[1,2]]', 'given M: matrix indexed by [int(1..2)] of int'),
    ('letting M = [1,3]', 'given M: matrix indexed by [int(1..2)] of int(0..2)'),
    ('letting M = [1,2]', 'given M: matrix indexed by [int(1..2)] of int(1,3)'),
    ('letting M = [0,1]', 'given M: matrix indexed by [int(1..2)] of bool'),
    ('letting M = [true,false]', 'given M: matrix indexed by [int(1..2)] of int'),
    ('letting M = [1]', 'given M: matrix indexed by [int(a..b)] of int'),
    ('letting n = 2\nletting M = [1,2,3]', 'given n: int\ngiven M: matrix indexed by [int(1..n)] of int'),
    ('letting M = [1]\nletting M = [2]', 'given M: matrix indexed by [int(1..1)] of int'),
    ('letting M = 3', 'given M: matrix indexed by [int(1..1)] of int'),
    ('letting n = 1', 'given n: bool'),
])
def test_parameter_mismatch_is_rejected_before_model_generation(tmp_path, params, declaration):
    translated(tmp_path, declaration, params, 'true', good=False)


def test_boolean_parameters_keep_boolean_identity(tmp_path):
    result = translated(tmp_path, 'given b: bool\ngiven M: matrix indexed by [int(1..2)] of bool',
                        'letting b = true\nletting M = [true,false]', 'b /\\ M[1] /\\ !M[2]')
    assert solver(result).check() == z3.sat


def test_parameter_matrix_trailing_commas_preserve_shape(tmp_path):
    result = translated(tmp_path, 'given M: matrix indexed by [int(1..2),int(1..2)] of int',
                        'letting M = [[1,2,],[3,4,],]', 'M[1,2] = 2 /\\ M[2,1] = 3')
    assert solver(result).check() == z3.sat


def test_given_multiple_names_share_domain_not_values(tmp_path):
    result = translated(tmp_path, 'given M,N: matrix indexed by [int(0..1)] of int',
                        'letting M = [1,2]\nletting N = [3,4]', 'M[0] = 1 /\\ N[0] = 3')
    assert solver(result).check() == z3.sat


def test_boolean_generator_shadow_restores_parameter_type(tmp_path):
    result = translated(tmp_path, 'given b: bool\nfind x: int(0..5)', 'letting b = true',
                        'x = (sum b: int(1..2) . b) /\\ b /\\ (forall b: bool . b \\/ !b)')
    check = solver(result)
    assert check.check() == z3.sat
    check.add(z3.Int('x') != 3)
    assert check.check() == z3.unsat


def test_distinct_parameter_files_share_constants_but_reject_duplicate_assignments(tmp_path):
    first, second = tmp_path / 'a.param', tmp_path / 'b.param'
    first.write_text('letting n = 2')
    second.write_text('letting M = [[1,2],[3,n]]')
    source = "language ESSENCE' 1.0\ngiven n: int\ngiven M: matrix indexed by [int(1..n),int(1..n)] of int\nsuch that M[2,2] = n"
    result = sp.translate(source=source, data=[str(first),str(second)], language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert solver(result).check() == z3.sat
    second.write_text('letting n = 2')
    result = sp.translate(source=source, data=[str(first),str(second)], language='essence')
    assert not result.ok


def test_constant_parameter_catch_evaluates_only_the_defined_branch(tmp_path):
    result = translated(tmp_path, 'given n: int\nfind x: int(0..9)',
                        'letting n = catchUndef(1/0, 7)', 'x = n')
    check = solver(result)
    assert check.check() == z3.sat
    check.add(z3.Int('x') != 7)
    assert check.check() == z3.unsat


def test_matrix_generator_cannot_read_a_shadowed_scalar_parameter(tmp_path):
    translated(tmp_path, 'given b: bool', 'letting b = true',
               'sum([toInt(b) | b: matrix indexed by [int(1..1)] of bool]) = 2', good=False)


def test_scalar_generator_cannot_read_a_shadowed_matrix_parameter(tmp_path):
    translated(tmp_path, 'given M: matrix indexed by [int(1..1)] of int',
               'letting M = [1]', 'forall M: int(1..1) . M[1] = 1', good=False)


def test_matrix_generator_restores_a_shadowed_scalar_parameter(tmp_path):
    result = translated(tmp_path, 'given b: bool', 'letting b = true',
                        '(sum([toInt(b[1]) | b: matrix indexed by [int(1..1)] of bool]) = 1) /\\ b')
    assert solver(result).check() == z3.sat
