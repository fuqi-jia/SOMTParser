"""Two-dimensional Gecode element semantics, including independent bounds."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

import pytest
import z3

from tools.semantic_checks.source_oracles.fzn_json_source import Reader, Unsupported, read_source


def literal(indices):
    value = z3.EmptySet(z3.IntSort())
    for index in indices:
        value = z3.SetAdd(value, index)
    return value


def relation(kind, row, column, values, rows, columns, result):
    return Reader().predicate('gecode_'+kind+'_element2d',
        [row, column, values, literal(rows), literal(columns), result])


def prove(formula, expected=z3.unsat):
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == expected


@pytest.mark.parametrize('kind', ['int', 'bool'])
@pytest.mark.parametrize('rows,columns', [([1, 2], [0, 1, 2]),
    ([-2, -1], [4, 5, 6]), ([5], [-7])])
def test_exact_complete_relation_for_all_indices_and_cell_values(kind, rows, columns):
    r, c = z3.FreshInt('row'), z3.FreshInt('column')
    fresh = z3.FreshInt if kind == 'int' else z3.FreshBool
    cells = [fresh('cell') for _ in range(len(rows)*len(columns))]
    out = fresh('out')
    actual = relation(kind, r, c, cells, rows, columns, out)
    expected = z3.Or(*[z3.And(r == i, c == j, out == cells[n])
        for n, (i, j) in enumerate((i, j) for i in rows for j in columns)])
    prove(z3.Xor(actual, expected))


@pytest.mark.parametrize('row,column', [(0, 5), (1, 5), (2, 2), (3, 0)])
def test_flattened_index_does_not_accept_out_of_range_coordinate(row, column):
    # Several invalid coordinate pairs still have a valid flattened index.
    out = z3.FreshInt('out')
    actual = relation('int', z3.IntVal(row), z3.IntVal(column),
                      list(map(z3.IntVal, [10, 20, 30, 40])), [1, 2], [3, 4], out)
    prove(actual)


@pytest.mark.parametrize('fault', ['sparse', 'symbolic-set', 'length',
                                  'arity', 'cell-sort', 'result-sort'])
def test_invalid_shape_and_sorts_are_not_silently_approximated(fault):
    args = [z3.FreshInt('r'), z3.FreshInt('c'), list(map(z3.IntVal, [1, 2, 3, 4])),
            literal([1, 2]), literal([3, 4]), z3.FreshInt('out')]
    if fault == 'sparse':
        args[3] = literal([1, 3])
    elif fault == 'symbolic-set':
        args[3] = z3.FreshConst(z3.SetSort(z3.IntSort()), 'indices')
    elif fault == 'length':
        args[2] = args[2][:-1]
    elif fault == 'arity':
        args.pop()
    elif fault == 'cell-sort':
        args[2][0] = z3.BoolVal(True)
    else:
        args[5] = z3.BoolVal(True)
    with pytest.raises(Unsupported):
        Reader().predicate('gecode_int_element2d', args)


@pytest.mark.parametrize('empty_dimension', [0, 1])
def test_empty_dimension_has_no_valid_element(empty_dimension):
    domains = [[1, 2], [3, 4]]
    domains[empty_dimension] = []
    prove(relation('int', z3.FreshInt('r'), z3.FreshInt('c'), [],
                   *domains, z3.FreshInt('out')))


def test_literal_index_cache_retains_original_ast_and_respects_deletions():
    reader = Reader()
    original = z3.SetAdd(z3.SetDel(literal([1, 2, 3]), 3), 0)
    assert reader.index_interval(original) == (0, 3)
    assert reader.index_interval(original) == (0, 3)
    cached = next(iter(reader.index_intervals.values()))
    assert cached[0].eq(original)
    with pytest.raises(Unsupported, match='contiguous'):
        reader.index_interval(z3.SetDel(literal([0, 1, 2]), 1))


def test_official_json_argument_order_enters_complete_source_relation():
    flat = read_source(dict(version='1.0', variables={
        'r': dict(type='int', domain=[[-3, 0]]),
        'c': dict(type='int', domain=[[3, 7]]),
        'z': dict(type='int', domain=[[-100, 100]])}, arrays={}, constraints=[
            dict(id='gecode_int_element2d', args=['r', 'c', [7, -3, 2, 9, 4, 6],
                 {'set': [[-2, -1]]}, {'set': [[4, 6]]}, 'z'])],
        output=['r', 'c', 'z'], solve=dict(method='minimize', objective='z')))
    r, c, out = (flat.variables[name] for name in ['r', 'c', 'z'])
    expected = z3.Or(*[z3.And(r == i, c == j, out == value)
        for (i, j), value in zip(((i, j) for i in [-2, -1] for j in [4, 5, 6]),
                                 [7, -3, 2, 9, 4, 6])])
    prove(z3.Xor(flat.relation, expected))


@pytest.mark.parametrize('kind', ['int', 'bool'])
@pytest.mark.parametrize('shifted', [False, True])
def test_actual_gecode_enumerates_exact_source_coordinates(tmp_path, kind, shifted):
    compiler = Path(os.environ['SOMTPARSER_MINIZINC_EXECUTABLE'])
    executable = compiler.with_name('fzn-gecode')
    rows, columns = ([-2, -1], [4, 5, 6]) if shifted else ([1, 2], [0, 1, 2])
    values = [7, -3, 2, 9, 4, 6] if kind == 'int' else [True, False, False, True, True, False]
    text = lambda x: str(x).lower() if isinstance(x, bool) else str(x)
    source = '\n'.join([
        f'predicate gecode_{kind}_element2d(var int: r, var int: c, array[int] of var {kind}: x, set of int: rs, set of int: cs, var {kind}: z);',
        f'var {rows[0]-1}..{rows[-1]+1}: r :: output_var;',
        f'var {columns[0]-1}..{columns[-1]+1}: c :: output_var;',
        'var -100..100: z :: output_var;' if kind == 'int' else 'var bool: z :: output_var;',
        f'constraint gecode_{kind}_element2d(r,c,[{",".join(map(text, values))}],{rows[0]}..{rows[-1]},{columns[0]}..{columns[-1]},z);',
        'solve satisfy;'])+'\n'
    model = tmp_path/'element2d.fzn'
    model.write_text(source)
    argv = [str(executable), '-a', str(model)]
    process = subprocess.run(argv, capture_output=True, text=True)
    (tmp_path/'official.stdout').write_text(process.stdout)
    (tmp_path/'official.stderr').write_text(process.stderr)
    (tmp_path/'official-process.json').write_text(json.dumps(dict(argv=argv,
        returncode=process.returncode, executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
        input_sha256=hashlib.sha256(model.read_bytes()).hexdigest()), indent=2)+'\n')
    assert process.returncode == 0, process.stderr
    assert '==========' in process.stdout
    solutions = set()
    for block in process.stdout.split('----------'):
        bindings = dict(re.findall(r'\b(r|c|z)\s*=\s*(-?\d+|true|false)\s*;', block))
        if not bindings:
            continue
        value = (bindings['z'] == 'true') if kind == 'bool' else int(bindings['z'])
        solutions.add((int(bindings['r']), int(bindings['c']), value))
    expected = {(i, j, value) for (i, j), value in
        zip(((i, j) for i in rows for j in columns), values)}
    assert solutions == expected
