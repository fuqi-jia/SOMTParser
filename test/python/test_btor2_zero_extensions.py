"""Zero-width aliases preserve every source sort check and bounded trace."""
import gc

import pytest
import z3
import somtparser as sp

from test_btor2_shared_bit_constants import equivalent, translate_releasing_source


def machine(aliases):
    rows = ['1 sort bitvec 1', '2 sort bitvec 3', '3 sort bitvec 5',
            '4 one 1', '5 one 2', '6 state 2 source state', '7 input 2 source input',
            '8 add 2 6 7', '9 uext 2 8 0', '10 uext 3 9 2',
            '11 slice 2 10 2 0', '12 sext 2 11 0', '13 next 2 6 12',
            '14 output 10 wider output', '15 output 12 narrow output', '16 bad 4']
    last = 12
    for index in range(17, 17 + aliases):
        rows.append(f'{index} uext 2 {last} 0 alias annotation {index}')
        last = index
    rows.append(f'{17 + aliases} output {last} final alias output')
    return '\n'.join(rows) + '\n'


def relation(depth):
    def value(name, frame, width=3): return z3.BitVec(name + '@' + str(frame), width)
    formulas = []
    for frame in range(depth + 1):
        total = value('source state', frame) + value('source input', frame)
        formulas += [value('wider output', frame, 5) == z3.ZeroExt(2, total),
                     value('narrow output', frame) == total,
                     value('final alias output', frame) == total]
        if frame < depth:
            formulas.append(value('source state', frame + 1) == total)
    return z3.And(*formulas)


@pytest.mark.parametrize('mode', ['inline', 'path'])
@pytest.mark.parametrize('depth', [0, 2])
@pytest.mark.parametrize('aliases', [0, 512])
def test_zero_and_nonzero_extensions_keep_all_outputs_and_transitions(mode, depth, aliases, tmp_path):
    text = machine(aliases)
    result = translate_releasing_source(text, mode, depth, tmp_path)
    del text
    gc.collect()
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected = relation(depth)
    equivalent(actual, expected)
    # A mistaken truncation/removal of the nonzero extension is observable:
    # the high bits of the widened result must stay zero at every frame.
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(actual, z3.Extract(4, 3, z3.BitVec('wider output@0', 5)) != 0)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('record,line,part', [
    ('6 uext 3 5 0', 6, 'declares result sort'),
    ('6 uext 2 5 -1', 6, 'cannot extend by a negative width'),
    ('6 uext 2 5', 6, 'too few arguments'),
    ('6 uext 2 999 0', 6, 'undeclared earlier node'),
])
@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_unused_malformed_extension_is_still_checked(record, line, part, mode, tmp_path):
    text = '1 sort bitvec 1\n2 sort bitvec 3\n3 sort bitvec 5\n4 one 1\n5 input 2 x\n' + record + '\n7 bad 4\n'
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '2'})
    if mode == 'path':
        path = tmp_path / 'invalid-zero-extend.btor2'; path.write_text(text)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=text, **options)
    assert not result.ok
    assert any(d.line == line and part in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_zero_extension_of_an_array_is_not_silently_an_identity(mode, tmp_path):
    text = ('1 sort bitvec 1\n2 sort bitvec 3\n3 sort array 1 2\n4 one 1\n'
            '5 input 3 memory\n6 uext 3 5 0\n7 bad 4\n')
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '0'})
    if mode == 'path':
        path = tmp_path / 'invalid-array-extension.btor2'; path.write_text(text)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=text, **options)
    assert not result.ok
    assert any(d.line == 6 and 'declares result sort' in d.message for d in result.diagnostic_items)
