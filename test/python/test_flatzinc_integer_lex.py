"""Official Gecode lex ordering, including prefixes and signed-cost projection."""
import os
import hashlib
import json
from pathlib import Path
import subprocess

import pytest
import z3

from tools.semantic_checks.source_oracles.fzn_json_source import Reader, Unsupported, read_source
from tools.semantic_checks.source_oracles.target_relation import compare


NAMES = ['array_int_lq', 'array_int_lt', 'gecode_array_int_lq',
         'gecode_array_int_lt', 'fzn_lex_lesseq_int', 'fzn_lex_less_int']


def independent_prefix_definition(left, right, strict):
    terms = []
    for position, (x, y) in enumerate(zip(left, right)):
        terms.append(z3.And(*[a == b for a, b in zip(left[:position], right[:position])], x < y))
    prefix_wins = len(left) < len(right) if strict else len(left) <= len(right)
    if prefix_wins:
        terms.append(z3.And(*[a == b for a, b in zip(left, right)]))
    return z3.Or(*terms)


@pytest.mark.parametrize('name', NAMES)
def test_symbolic_unbounded_lex_relation(name):
    strict = name.endswith('_lt') or name == 'fzn_lex_less_int'
    for n in range(5):
        for m in range(5):
            left = [z3.Int(f'left_{i}') for i in range(n)]
            right = [z3.Int(f'right_{i}') for i in range(m)]
            actual = Reader().predicate(name, [left, right])
            expected = independent_prefix_definition(left, right, strict)
            check = z3.Solver(); check.add(z3.Xor(actual, expected))
            assert check.check() == z3.unsat


CONSTANTS = [([], []), ([], [0]), ([0], []), ([2], [2, -9]),
             ([2, -9], [2]), ([-5, 90], [-4, -90]),
             ([3, -90], [2, 90]), ([2, -8], [2, -7])]


@pytest.mark.parametrize('name', ['array_int_lq', 'array_int_lt'])
@pytest.mark.parametrize('left,right', CONSTANTS)
def test_literal_equal_prefix_and_first_difference(name, left, right):
    expected = tuple(left) < tuple(right) if name.endswith('_lt') else tuple(left) <= tuple(right)
    actual = Reader().predicate(name, [[z3.IntVal(x) for x in left], [z3.IntVal(y) for y in right]])
    assert z3.is_true(z3.simplify(actual)) == expected
    assert z3.is_false(z3.simplify(actual)) != expected


@pytest.mark.parametrize('args', [[], [[]], [[], [], []], [z3.IntVal(1), []], [[z3.RealVal('1.5')], []], [[], [z3.BoolVal(True)]]])
def test_bad_signature_is_rejected(args):
    with pytest.raises(Unsupported):
        Reader().predicate('array_int_lq', args)


@pytest.mark.parametrize('suffix', ['_reif', '_imp'])
@pytest.mark.parametrize('strict', [False, True])
def test_reification_keeps_boolean_direction(suffix, strict):
    x, y = z3.Ints('lex_reif_x lex_reif_y'); b = z3.Bool('lex_reif_b')
    name = 'fzn_lex_less_int' if strict else 'fzn_lex_lesseq_int'
    relation = x < y if strict else x <= y
    actual = Reader().predicate(name + suffix, [[x], [y], b])
    expected = b == relation if suffix == '_reif' else z3.Implies(b, relation)
    solver = z3.Solver(); solver.add(z3.Xor(actual, expected)); assert solver.check() == z3.unsat
    solver = z3.Solver(); solver.add(actual, z3.Not(b), x > y); assert solver.check() == z3.sat


@pytest.mark.parametrize('direction,shift', [('minimize', 0), ('maximize', 0), ('minimize', 1)])
def test_full_observation_and_signed_cost(direction, shift):
    doc = dict(version='1.0', variables={n:dict(type='int', domain=[[-2,2]]) for n in ['a','b','c','d']},
               arrays={'left':dict(a=['a','b']), 'right':dict(a=['c','d'])},
               constraints=[dict(id='array_int_lq', args=['left','right'])], output=['a','b','c','d'],
               solve=dict(method=direction, objective='a'))
    source = read_source(doc)
    observations = [dict(name=n, value=source.variables[n], indices=None, dimensions=[]) for n in ['a','b','c','d']]
    text = '\n'.join(f'(declare-const {n} Int)' for n in ['a','b','c','d'])
    text += '\n' + '\n'.join(f'(assert (and (<= (- 2) {n}) (<= {n} 2)))' for n in ['a','b','c','d'])
    text += '\n(assert (or (< a c) (and (= a c) (<= b d))))'
    text += f'\n({direction} (+ a {shift}))\n(check-sat)\n(exit)\n'
    raw = []
    result = compare(source, observations, text.encode(), solve=True, complete_relation_callback=lambda a,b:raw.append((a,b)))
    assert len(raw) == 1
    assert result['equivalent'] is (shift == 0)
    assert result['all_source_constraints_retained'] and result['all_target_assertions_retained']
    solver = z3.Solver(); solver.add(z3.Xor(*raw[0]))
    assert solver.check() == (z3.unsat if shift == 0 else z3.sat)


def test_lex_ast_is_linear():
    n = 1024; left = [z3.Int(f'scale_l_{i}') for i in range(n)]; right = [z3.Int(f'scale_r_{i}') for i in range(n)]
    relation = Reader().predicate('array_int_lq', [left, right])
    seen = set(); todo = [relation]
    while todo:
        term = todo.pop()
        if term.get_id() in seen: continue
        seen.add(term.get_id()); todo.extend(term.children())
    assert len(seen) <= 6*n + 2


@pytest.mark.parametrize('name', ['array_int_lq', 'array_int_lt'])
@pytest.mark.parametrize('left,right', [([], []), ([], [0]), ([0], []), ([2], [2, -9]), ([-5, 90], [-4, -90]), ([3, -90], [2, 90])])
def test_official_gecode_flatzinc_result(tmp_path, name, left, right):
    configured = os.environ.get('SOMTPARSER_MINIZINC_EXECUTABLE')
    if not configured:
        pytest.skip('set SOMTPARSER_MINIZINC_EXECUTABLE for official Gecode controls')
    executable = Path(configured).parent / 'fzn-gecode'
    assert executable.is_file()
    def literal(values): return '[' + ','.join(str(x) for x in values) + ']'
    model = tmp_path/'lex.fzn'
    model.write_text(f'constraint {name}({literal(left)},{literal(right)});\nsolve satisfy;\n')
    process = subprocess.run([str(executable), str(model)], capture_output=True, text=True)
    (tmp_path/'official-process.json').write_text(json.dumps(dict(argv=process.args,returncode=process.returncode,stdout=process.stdout,stderr=process.stderr,executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest()),indent=2)+'\n')
    assert process.returncode == 0, process.stderr
    expected = tuple(left) < tuple(right) if name.endswith('_lt') else tuple(left) <= tuple(right)
    assert ('=====UNSATISFIABLE=====' not in process.stdout) == expected, process.stdout
