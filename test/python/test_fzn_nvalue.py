"""Exact distinct-value counts from official FlatZinc, with independent controls."""
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


def first_occurrence_count(values):
    # Independent quadratic specification for small semantic controls only.
    return z3.Sum(*[z3.If(z3.And(*[x != y for y in values[:i]]), 1, 0)
                    for i, x in enumerate(values)]) if values else 0


def check(formula, expected=z3.unsat):
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == expected


@pytest.mark.parametrize('size', [0, 1, 2, 3, 5, 8])
def test_unbounded_integer_relation_matches_independent_definition(size):
    values = [z3.FreshInt('value') for _ in range(size)]
    count = z3.FreshInt('count')
    actual = Reader().predicate('fzn_nvalue', [count, values])
    check(z3.Xor(actual, count == first_occurrence_count(values)))


@pytest.mark.parametrize('values', [[], [0], [-17, -17],
                                   [10**40, -10**40, 10**40, 0], [2, 1, 2, 1, 3]])
def test_constants_include_empty_negative_huge_and_duplicate_values(values):
    count = z3.FreshInt('count')
    actual = Reader().predicate('fzn_nvalue', [count, list(map(z3.IntVal, values))])
    check(z3.Xor(actual, count == len(set(values))))


@pytest.mark.parametrize('suffix', ['_reif', '_imp'])
def test_reification_and_implication_keep_false_branch_unrestricted(suffix):
    count, x, y = z3.Ints('count x y')
    flag = z3.Bool('flag')
    actual = Reader().predicate('fzn_nvalue'+suffix, [count, [x, y, x], flag])
    relation = count == z3.If(x == y, 1, 2)
    expected = (flag == relation) if suffix == '_reif' else z3.Implies(flag, relation)
    check(z3.Xor(actual, expected))
    check(z3.And(actual, z3.Not(flag), count == -1), z3.sat)


@pytest.mark.parametrize('fault', ['arity', 'count-sort', 'array', 'element-sort'])
def test_invalid_calls_fail_explicitly(fault):
    args = [z3.FreshInt('n'), [z3.FreshInt('x')]]
    if fault == 'arity':
        args.append(z3.IntVal(1))
    elif fault == 'count-sort':
        args[0] = z3.FreshBool('n')
    elif fault == 'array':
        args[1] = z3.FreshInt('x')
    else:
        args[1][0] = z3.FreshBool('x')
    with pytest.raises(Unsupported):
        Reader().predicate('fzn_nvalue', args)


@pytest.mark.parametrize('method', ['minimize', 'maximize'])
def test_json_projection_keeps_distinct_count_and_signed_objective(method):
    source = read_source(dict(version='1.0', variables={
        'x': dict(type='int'), 'y': dict(type='int'), 'n': dict(type='int')},
        arrays={'values': {'a': ['x', 'y', 'x']}}, constraints=[
            {'id': 'fzn_nvalue', 'args': ['n', 'values']}], output=['x', 'y', 'n'],
        solve={'method': method, 'objective': 'n'}))
    x, y, n, cost = z3.Ints('public_x public_y public_n cost')
    actual = source.projected(zip([x, y, n], [source.variables[k] for k in ['x', 'y', 'n']]), signed_cost=cost)
    expected = z3.And(n == z3.If(x == y, 1, 2), cost == (n if method == 'minimize' else -n))
    check(z3.Xor(actual, expected))
    check(z3.And(actual, cost != (n if method == 'minimize' else -n)))
    check(z3.And(actual, n == 0), z3.unsat)


def test_large_count_uses_linear_shared_dag():
    values = [z3.FreshInt('v') for _ in range(1000)]
    formula = Reader().predicate('fzn_nvalue', [z3.FreshInt('n'), values])
    seen, pending = {}, [formula]
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen[term.get_id()] = term
        pending.extend(term.children())
    assert len(seen) < 7*len(values)+20


@pytest.mark.parametrize('names', [[], ['x'], ['x', 'x', 'y'], ['x', 'y', 'z']])
def test_actual_gecode_enumeration_matches_mathematical_count(tmp_path, names):
    executable = Path(os.environ['SOMTPARSER_MINIZINC_EXECUTABLE']).with_name('fzn-gecode')
    variables = sorted(set(names))
    source = '\n'.join([
        'predicate fzn_nvalue(var int: n, array[int] of var int: xs);',
        *[f'var -1..1: {name} :: output_var;' for name in variables],
        'var -1..4: n :: output_var;',
        f'constraint fzn_nvalue(n, [{",".join(names)}]);',
        'solve satisfy;'])+'\n'
    model = tmp_path/'nvalue.fzn'
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
        bindings = dict(re.findall(r'\b(n|x|y|z)\s*=\s*(-?\d+)\s*;', block))
        if 'n' in bindings:
            solutions.add(tuple(int(bindings[k]) for k in variables+['n']))
    expected = set()
    for assignment in itertools.product(range(-1, 2), repeat=len(variables)):
        values = dict(zip(variables, assignment))
        expected.add(assignment+(len({values[name] for name in names}),))
    assert solutions == expected
