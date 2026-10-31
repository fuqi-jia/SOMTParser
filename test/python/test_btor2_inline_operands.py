"""Operand storage boundaries and deep initialization dependency validation."""
import pytest
import somtparser as sp
import z3


def translate(source, mode, tmp_path, depth=0):
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': str(depth)})
    if mode == 'path':
        path = tmp_path / 'operands.btor2'
        path.write_text(source)
        return sp.translate(path=str(path), **options)
    return sp.translate(source=source, **options)


@pytest.mark.parametrize('mode', ['inline', 'path'])
@pytest.mark.parametrize('arity', [4, 5, 6])
@pytest.mark.parametrize('invalid_last', [False, True])
def test_justice_overflow_keeps_every_reference(mode, arity, invalid_last, tmp_path):
    # Many preceding records move the justice record across source blocks.
    rows = ['1 sort bitvec 1', '2 input 1 x']
    rows.extend(f'{node} not 1 {node-1}' for node in range(3, 1003))
    operands = ['2'] * arity
    if invalid_last:
        operands[-1] = '-9223372036854775808'
    rows.append(f'1003 justice {arity} ' + ' '.join(operands))
    rows.append('1004 bad 2')
    result = translate('\n'.join(rows) + '\n', mode, tmp_path)
    assert not result.ok
    if invalid_last:
        assert any(d.code == sp.ErrorCode.E_PARSE and d.line == 1003
                   and 'negated node id is out of range' in d.message
                   for d in result.diagnostic_items)
    else:
        assert any(d.code == sp.ErrorCode.E_UNSUPPORTED_CONSTRUCT
                   for d in result.diagnostic_items)


@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_deep_init_input_dependency_has_bounded_stack(mode, tmp_path):
    depth = 65536
    rows = ['1 sort bitvec 1', '2 input 1 x']
    rows.extend(f'{node} not 1 {node-1}' for node in range(3, depth + 3))
    state = depth + 3
    rows += [f'{state} state 1 s', f'{state+1} init 1 {state} -{state-1}',
             f'{state+2} bad {state}']
    result = translate('\n'.join(rows) + '\n', mode, tmp_path)
    assert not result.ok
    assert any(d.code == sp.ErrorCode.E_PARSE and d.line == state+1
               and 'inputs are not allowed in initialization expressions' in d.message
               for d in result.diagnostic_items)


@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_initial_state_is_not_an_input_dependency(mode, tmp_path):
    # The first state is unconstrained at step zero. A later state's init
    # expression may depend on it; only actual primary inputs are forbidden.
    source = ('1 sort bitvec 1\n2 state 1 a\n3 not 1 2\n4 state 1 b\n'
              '5 init 1 4 3\n6 one 1\n7 bad 6\n')
    result = translate(source, mode, tmp_path)
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected = z3.BitVec('b@0', 1) == ~z3.BitVec('a@0', 1)
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
