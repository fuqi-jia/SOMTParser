"""Complete bin-load relations, including index bounds and official Gecode controls."""
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import subprocess

import pytest
import z3

from tools.semantic_checks.source_oracles.fzn_json_source import Reader, Unsupported, read_source


def relation(loads, bins, weights, first):
    return Reader().predicate('gecode_bin_packing_load',
                              [loads, bins, list(map(z3.IntVal, weights)), z3.IntVal(first)])


def independent_relation(loads, bins, weights, first):
    # Enumerate all valid item assignments for small controls; all public
    # variables themselves remain unbounded in the equivalence query.
    choices = []
    for assignment in itertools.product(range(first, first + len(loads)), repeat=len(bins)):
        amounts = [sum(w for b, w in zip(assignment, weights) if b == i)
                   for i in range(first, first + len(loads))]
        choices.append(z3.And(*[x == b for x, b in zip(bins, assignment)],
                              *[x == w for x, w in zip(loads, amounts)]))
    return z3.Or(*choices)


def check(formula, answer=z3.unsat):
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == answer


@pytest.mark.parametrize('first,nbins,weights', [
    (1, 2, []), (0, 0, []), (-4, 0, [0]), (0, 1, [0]),
    (-2, 3, [0, 2, 3]), (5, 2, [2, 2, 1]), (10**35, 2, [10**40, 7])])
def test_complete_unbounded_relation_matches_assignment_specification(first, nbins, weights):
    loads = [z3.FreshInt('load') for _ in range(nbins)]
    bins = [z3.FreshInt('bin') for _ in weights]
    check(z3.Xor(relation(loads, bins, weights, first),
                 independent_relation(loads, bins, weights, first)))


@pytest.mark.parametrize('mode', ['alias', 'literal', 'expression'])
def test_repeated_and_literal_item_indices_keep_every_weight(mode):
    a, b, x = z3.Ints('load_a load_b item')
    bins = {'alias': [x, x], 'literal': [z3.IntVal(-2), z3.IntVal(-1)],
            'expression': [x, x + 1]}[mode]
    check(z3.Xor(relation([a, b], bins, [2, 3], -2),
                 independent_relation([a, b], bins, [2, 3], -2)))


@pytest.mark.parametrize('outside', [-3, 0])
def test_zero_weight_item_cannot_escape_bin_index_range(outside):
    loads = [z3.IntVal(0), z3.IntVal(0)]
    check(relation(loads, [z3.IntVal(outside)], [0], -2))


@pytest.mark.parametrize('suffix', ['_reif', '_imp'])
def test_reification_scopes_both_index_bounds_and_load_equations(suffix):
    load, item = z3.Ints('load item')
    flag = z3.Bool('flag')
    actual = Reader().predicate('gecode_bin_packing_load' + suffix,
                               [[load], [item], [z3.IntVal(3)], z3.IntVal(-1), flag])
    expected = z3.And(item == -1, load == 3)
    expected = flag == expected if suffix == '_reif' else z3.Implies(flag, expected)
    check(z3.Xor(actual, expected))
    check(z3.And(actual, z3.Not(flag), item == 99, load == -8), z3.sat)


@pytest.mark.parametrize('fault', [
    'arity', 'load-array', 'bin-array', 'weight-array', 'load-sort', 'bin-sort',
    'weight-sort', 'offset-sort', 'variable-weight', 'negative-weight',
    'variable-offset', 'lengths'])
def test_invalid_primitive_arguments_fail_explicitly(fault):
    args = [[z3.FreshInt('load')], [z3.FreshInt('bin')], [z3.IntVal(3)], z3.IntVal(1)]
    if fault == 'arity': args.pop()
    elif fault.endswith('-array'): args[{'load-array': 0, 'bin-array': 1, 'weight-array': 2}[fault]] = z3.IntVal(1)
    elif fault in ['load-sort', 'bin-sort', 'weight-sort']:
        args[{'load-sort': 0, 'bin-sort': 1, 'weight-sort': 2}[fault]] = [z3.BoolVal(True)]
    elif fault == 'offset-sort': args[3] = z3.BoolVal(True)
    elif fault == 'variable-weight': args[2] = [z3.FreshInt('weight')]
    elif fault == 'negative-weight': args[2] = [z3.IntVal(-1)]
    elif fault == 'variable-offset': args[3] = z3.FreshInt('offset')
    else: args[2] = []
    with pytest.raises(Unsupported): Reader().predicate('gecode_bin_packing_load', args)


@pytest.mark.parametrize('method', ['minimize', 'maximize'])
def test_complete_json_projection_retains_loads_and_signed_objective(method):
    source = read_source(dict(version='1.0', variables={name: dict(type='int') for name in ['a', 'b', 'x', 'y']},
        arrays={}, constraints=[dict(id='gecode_bin_packing_load', args=[['a', 'b'], ['x', 'y'], [0, 3], -2])],
        output=['a', 'b', 'x', 'y'], solve=dict(method=method, objective='a')))
    a, b, x, y, cost = z3.Ints('public_a public_b public_x public_y signed_cost')
    actual = source.projected(zip([a, b, x, y], [source.variables[n] for n in ['a', 'b', 'x', 'y']]), signed_cost=cost)
    expected = z3.And(independent_relation([a, b], [x, y], [0, 3], -2),
                      cost == (a if method == 'minimize' else -a))
    check(z3.Xor(actual, expected))


@pytest.mark.parametrize('first,nbins,weights,names', [
    (1, 2, [], []), (-2, 3, [0, 2, 3], ['x', 'y', 'z']),
    (0, 2, [0], ['x']), (4, 2, [1, 1], ['x', 'x']),
    (-3, 2, [2, 3, 0], [-3, -2, -4])])
def test_actual_gecode_all_solutions_match_exact_bin_assignment(tmp_path, first, nbins, weights, names):
    executable = Path(os.environ['SOMTPARSER_MINIZINC_EXECUTABLE']).with_name('fzn-gecode')
    variables = sorted({n for n in names if isinstance(n, str)})
    load_names = [f'load{i}' for i in range(nbins)]
    source = '\n'.join([
        'predicate gecode_bin_packing_load(array[int] of var int: load, array[int] of var int: bin, array[int] of int: weight, int: first);',
        *[f'var {first-1}..{first+nbins}: {name} :: output_var;' for name in variables],
        *[f'var 0..{sum(weights)}: {name} :: output_var;' for name in load_names],
        f'constraint gecode_bin_packing_load([{",".join(load_names)}], [{",".join(map(str,names))}], [{",".join(map(str,weights))}], {first});',
        'solve satisfy;']) + '\n'
    model = tmp_path / 'binpacking.fzn'; model.write_text(source)
    argv = [str(executable), '-a', str(model)]
    process = subprocess.run(argv, capture_output=True, text=True)
    (tmp_path / 'official.stdout').write_text(process.stdout)
    (tmp_path / 'official.stderr').write_text(process.stderr)
    (tmp_path / 'official-process.json').write_text(json.dumps(dict(argv=argv, returncode=process.returncode,
        executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
        input_sha256=hashlib.sha256(model.read_bytes()).hexdigest()), indent=2) + '\n')
    assert process.returncode == 0, process.stderr
    assert '==========' in process.stdout or '=====UNSATISFIABLE=====' in process.stdout
    solutions = set()
    for block in process.stdout.split('----------'):
        bindings = dict(re.findall(r'\b(load\d+|x|y|z)\s*=\s*(-?\d+)\s*;', block))
        if all(n in bindings for n in variables + load_names):
            solutions.add(tuple(int(bindings[n]) for n in variables + load_names))
    expected = set()
    for assignment in itertools.product(range(first-1, first+nbins+1), repeat=len(variables)):
        values = dict(zip(variables, assignment))
        bins = [values[n] if isinstance(n, str) else n for n in names]
        if all(first <= b < first + nbins for b in bins):
            expected.add(assignment + tuple(sum(w for b, w in zip(bins, weights) if b == i)
                                           for i in range(first, first + nbins)))
    assert solutions == expected
