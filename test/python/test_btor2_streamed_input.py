"""Borrowed input storage preserves bounded BV/array transition relations."""
from pathlib import Path
import hashlib

import pytest
import z3

import somtparser as sp


FIXTURES = Path(__file__).resolve().parents[2] / 'languages/btor2/instances/competition'
PINS = {
    'fib_30': '1bb400e569c8c3147d38245dd81458261c4cc0aac565286e731dabf78fdf31d0',
    'standard_init1_ground-2': '2c89175d78b79037995318cbdf194f25a180d9e4defe3582d46c113434f890e1',
}


def source(name):
    raw = (FIXTURES / (name + '.btor2')).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PINS[name]
    return raw.decode()


def bounded_relation(text, depth):
    """Independent direct Z3 interpretation of the operators in these originals."""
    rows = {}
    sorts = {}
    names = {}
    for line in text.splitlines():
        words = line.split(';', 1)[0].split()
        if not words:
            continue
        index, op = int(words[0]), words[1]
        rows[index] = words
        if op == 'sort':
            sorts[index] = (z3.BitVecSort(int(words[3])) if words[2] == 'bitvec'
                            else z3.ArraySort(sorts[int(words[3])], sorts[int(words[4])]))
        elif op in {'state', 'input'}:
            names[index] = ' '.join(words[3:]) or op + str(index)
        elif op == 'output':
            names[index] = ' '.join(words[3:]) or op + str(index)

    cache = {}

    def bit(condition):
        return z3.If(condition, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

    def term(index, step):
        if index < 0:
            return ~term(-index, step)
        key = (index, step)
        if key in cache:
            return cache[key]
        row = rows[index]
        op, sort = row[1], sorts[int(row[2])]
        if op in {'state', 'input'}:
            value = z3.Const(names[index] + '@' + str(step), sort)
        elif op in {'const', 'constd', 'consth'}:
            base = {'const': 2, 'constd': 10, 'consth': 16}[op]
            value = z3.BitVecVal(int(row[3], base), sort.size())
        elif op == 'one':
            value = z3.BitVecVal(1, sort.size())
        else:
            a = term(int(row[3]), step)
            if op == 'not':
                value = ~a
            elif op == 'uext':
                value = z3.ZeroExt(int(row[4]), a)
            else:
                b = term(int(row[4]), step)
                if op == 'add':
                    value = a + b
                elif op == 'and':
                    value = a & b
                elif op == 'or':
                    value = a | b
                elif op == 'eq':
                    value = bit(a == b)
                elif op == 'ult':
                    value = bit(z3.ULT(a, b))
                elif op == 'ugt':
                    value = bit(z3.UGT(a, b))
                elif op == 'ugte':
                    value = bit(z3.UGE(a, b))
                elif op == 'slt':
                    value = bit(a < b)
                elif op == 'ite':
                    value = z3.If(a == 1, b, term(int(row[5]), step))
                elif op == 'read':
                    value = z3.Select(a, b)
                elif op == 'write':
                    value = z3.Store(a, b, term(int(row[5]), step))
                else:
                    raise AssertionError('Unreviewed oracle operator: ' + op)
        cache[key] = value
        return value

    relation = []
    for index, row in rows.items():
        op = row[1]
        if op == 'init':
            relation.append(term(int(row[3]), 0) == term(int(row[4]), 0))
        elif op == 'next':
            relation += [term(int(row[3]), step + 1) == term(int(row[4]), step)
                         for step in range(depth)]
        elif op == 'output':
            for step in range(depth + 1):
                value = term(int(row[2]), step)
                relation.append(z3.Const(names[index] + '@' + str(step), value.sort()) == value)
    prefix = []
    witnesses = []
    for step in range(depth + 1):
        prefix += [term(int(row[2]), step) == 1 for row in rows.values() if row[1] == 'constraint']
        witnesses += [z3.And(*prefix, term(int(row[2]), step) == 1)
                      for row in rows.values() if row[1] == 'bad']
    return z3.And(*relation, z3.Or(*witnesses))


def translated_after_source_release(text, mode, depth, tmp_path):
    if mode == 'path':
        path = tmp_path / 'machine.btor2'
        path.write_text(text)
        result = sp.translate(path=str(path), language='btor2', profile='bmc',
                              options={'bmc_depth': str(depth)})
        path.unlink()
    else:
        result = sp.translate(source=text, language='btor2', profile='bmc',
                              options={'bmc_depth': str(depth)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    # The native SourceUnit and reader have already been destroyed at return.
    # Serialization must only inspect owning HIR/DAG data, never a source view.
    del text
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def equivalent(actual, expected, require_sat=False):
    solver = z3.Solver()
    solver.set(timeout=10000)
    if require_sat:
        solver.add(expected)
        assert solver.check() == z3.sat
        solver.reset()
        solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('name', list(PINS))
@pytest.mark.parametrize('mode', ['path', 'inline'])
def test_unmodified_official_originals_keep_the_bmc1_query(name, mode, tmp_path):
    text = source(name)
    equivalent(translated_after_source_release(text, mode, 1, tmp_path), bounded_relation(text, 1))


@pytest.mark.parametrize('name', list(PINS))
@pytest.mark.parametrize('mode', ['path', 'inline'])
@pytest.mark.parametrize('depth', [0, 2])
def test_official_transition_relations_are_nonvacuously_preserved(name, mode, depth, tmp_path):
    # An explicitly derived regression, not an official benchmark result:
    # ADD a true bad witness so safety UNSAT cannot mask a lost transition.
    # Every original declaration, initializer, transition and label is retained.
    text = source(name)
    rows = [line.split(';', 1)[0].split() for line in text.splitlines()]
    rows = [row for row in rows if row]
    maximum = max(int(row[0]) for row in rows)
    boolean_sort = next(int(row[0]) for row in rows if row[1:] == ['sort', 'bitvec', '1'])
    text += f'\n{maximum + 1} one {boolean_sort}\n{maximum + 2} bad {maximum + 1}\n'
    expected = bounded_relation(text, depth)
    equivalent(translated_after_source_release(text, mode, depth, tmp_path), expected, require_sat=True)


@pytest.mark.parametrize('mode', ['path', 'inline'])
def test_crlf_comments_and_final_line_without_newline(mode, tmp_path):
    text = '; preface\r\n1 sort bitvec 1\r\n2 input 1 flag\r\n3 bad 2 ; last'
    equivalent(translated_after_source_release(text, mode, 0, tmp_path),
               z3.BitVec('flag@0', 1) == 1, require_sat=True)


@pytest.mark.parametrize('mode', ['path', 'inline'])
def test_unreferenced_invalid_record_is_not_skipped(mode, tmp_path):
    text = '1 sort bitvec 1\n2 one 1\n3 bad 2\n4 add 1 2 999\n'
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '1'})
    if mode == 'path':
        path = tmp_path / 'invalid.btor2'
        path.write_text(text)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=text, **options)
    assert not result.ok
    assert any(d.line == 4 and 'undeclared earlier node' in d.message for d in result.diagnostic_items)
