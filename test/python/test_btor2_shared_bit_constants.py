"""Independent bounded relations for Bool/BV1 adapters and parser lifetime."""
import gc

import pytest
import z3
import somtparser as sp


OPERATORS = ['eq', 'neq', 'ult', 'ulte', 'ugt', 'ugte', 'slt', 'slte', 'sgt',
             'sgte', 'redand', 'redor', 'redxor', 'implies', 'iff']


def condition(op, left, right):
    if op == 'eq': return left == right
    if op == 'neq': return left != right
    if op == 'ult': return z3.ULT(left, right)
    if op == 'ulte': return z3.ULE(left, right)
    if op == 'ugt': return z3.UGT(left, right)
    if op == 'ugte': return z3.UGE(left, right)
    if op == 'slt': return left < right
    if op == 'slte': return left <= right
    if op == 'sgt': return left > right
    if op == 'sgte': return left >= right
    if op == 'redand': return left == 7
    if op == 'redor': return left != 0
    if op == 'redxor':
        return z3.Xor(z3.Xor(z3.Extract(0, 0, left) == 1,
                             z3.Extract(1, 1, left) == 1), z3.Extract(2, 2, left) == 1)
    if op == 'implies': return z3.Implies(left == 1, right == 1)
    assert op == 'iff'
    return (left == 1) == (right == 1)


def machine(op, prefix):
    sort = 1 if op in {'implies', 'iff'} else 2
    operands = '5' if op.startswith('red') else '5 6'
    return (f'1 sort bitvec 1\n2 sort bitvec 3\n3 const 1 0\n4 const 1 1\n'
            f'5 state {sort} {prefix}state\n6 input {sort} {prefix}input\n'
            f'7 input 1 {prefix}choose\n8 {op} 1 {operands}\n9 ite 1 8 4 3\n'
            f'10 consth 2 5\n11 constd 2 2\n12 ite 2 7 10 11\n'
            f'13 output 8 {prefix}gate\n14 output 9 {prefix}selected\n'
            f'15 output 12 {prefix}wide\n16 next {sort} 5 6\n17 bad 4\n')


def expected(op, prefix, depth):
    width = 1 if op in {'implies', 'iff'} else 3
    def bv(name, step, size=width): return z3.BitVec(prefix + name + '@' + str(step), size)
    formulas = [bv('state', k + 1) == bv('input', k) for k in range(depth)]
    for k in range(depth + 1):
        bit = z3.If(condition(op, bv('state', k), bv('input', k)),
                    z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
        formulas += [bv('gate', k, 1) == bit, bv('selected', k, 1) == bit,
                     bv('wide', k, 3) == z3.If(bv('choose', k, 1) == 1,
                                               z3.BitVecVal(5, 3), z3.BitVecVal(2, 3))]
    return z3.And(*formulas)


def translate_releasing_source(text, mode, depth, tmp_path):
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': str(depth)})
    if mode == 'path':
        path = tmp_path / 'adapter-machine.btor2'
        path.write_text(text)
        result = sp.translate(path=str(path), **options)
        path.unlink()
    else:
        result = sp.translate(source=text, **options)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


def equivalent(actual, reference):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(reference)
    assert solver.check() == z3.sat
    solver.reset()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, reference))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('op', OPERATORS)
@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_all_adapter_relations_keep_outputs_and_transitions(op, mode, tmp_path):
    prefix = op + ' long source label '
    text = machine(op, prefix)
    result = translate_releasing_source(text, mode, 1, tmp_path)
    del text
    gc.collect()
    equivalent(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected(op, prefix, 1))


def test_two_live_translations_keep_independent_names_depths_and_owned_literals(tmp_path):
    first = translate_releasing_source(machine('redxor', 'first '), 'inline', 0, tmp_path)
    second = translate_releasing_source(machine('implies', 'second '), 'path', 2, tmp_path)
    equivalent(z3.And(*z3.parse_smt2_string(second.to_smt2())), expected('implies', 'second ', 2))
    del second
    gc.collect()
    equivalent(z3.And(*z3.parse_smt2_string(first.to_smt2())), expected('redxor', 'first ', 0))


@pytest.mark.parametrize('text,line,part', [
    ('1 sort bitvec 1\n2 one 1\n3 eq 1 2 2\n4 constd 1 2\n5 bad 2\n', 4, 'does not fit'),
    ('1 sort bitvec 1\n2 sort bitvec 3\n3 input 2 wide\n4 one 1\n5 ite 1 3 4 4\n6 bad 4\n',
     5, 'width 1'),
    ('1 sort bitvec 1\n2 sort bitvec 3\n3 sort array 1 2\n4 input 3 memory\n5 one 1\n'
     '6 ite 1 4 5 5\n7 bad 5\n', 6, 'width 1'),
])
@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_populated_or_unused_adapters_preserve_sort_errors(text, line, part, mode, tmp_path):
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '1'})
    if mode == 'path':
        path = tmp_path / 'invalid-adapter.btor2'; path.write_text(text)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=text, **options)
    assert not result.ok
    assert any(d.line == line and part in d.message for d in result.diagnostic_items)
