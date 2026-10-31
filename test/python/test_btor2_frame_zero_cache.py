"""Frame-local caching preserves unused source checks and complemented aliases."""
import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize('mode', ['inline', 'path'])
@pytest.mark.parametrize('negative', [False, True])
def test_aliases_keep_all_frames_and_complemented_operands(mode, negative, tmp_path):
    # Sparse IDs do not index cache storage, and the cache of frame zero must
    # not substitute the first input value into any later observation.
    ids = [2**63 - 1000 + 7 * i for i in range(10)]
    sort, value, first, second, output, one, bad = ids[:7]
    source = (f'{sort} sort bitvec 3\n{value} input {sort} x\n'
              f'{first} uext {sort} {"-" if negative else ""}{value} 0\n'
              f'{second} uext {sort} {first} 0\n'
              f'{output} output {second} observed\n')
    # A separate one-bit true bad property keeps every input valuation possible.
    source += f'{one} sort bitvec 1\n{bad} one {one}\n{ids[7]} bad {bad}\n'
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '3'})
    if mode == 'path':
        path = tmp_path / 'alias.btor2'; path.write_text(source)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=source, **options)
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    relations = []
    for frame in range(4):
        x = z3.BitVec(f'x@{frame}', 3)
        relations.append(z3.BitVec(f'observed@{frame}', 3) == (~x if negative else x))
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(z3.Xor(actual, z3.And(*relations)))
    assert solver.check() == z3.unsat
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(actual, z3.BitVec('x@0', 3) == 1, z3.BitVec('x@3', 3) == 6)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_unused_alias_keeps_ill_typed_ancestor_validation(mode, tmp_path):
    source = ('1 sort bitvec 1\n2 sort bitvec 3\n3 input 1 x\n4 input 2 y\n'
              '5 and 1 3 4\n6 uext 1 5 0\n7 uext 1 6 0\n8 one 1\n9 bad 8\n')
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '1'})
    if mode == 'path':
        path = tmp_path / 'unused-alias.btor2'; path.write_text(source)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=source, **options)
    assert not result.ok
    assert any(d.line == 5 and d.code == sp.ErrorCode.E_TYPE for d in result.diagnostic_items)


@pytest.mark.parametrize('mode', ['inline', 'path'])
def test_unused_deep_source_chain_survives_parser_teardown(mode, tmp_path):
    # Every valid source term is checked even though the property does not
    # reference this chain. Releasing parser caches must not recurse through
    # all 65,536 source records on the C++ stack.
    count = 65536
    rows = ['1 sort bitvec 1', '2 input 1 x']
    rows.extend(f'{node} not 1 {node-1}' for node in range(3, count + 3))
    rows += [f'{count+3} one 1', f'{count+4} bad {count+3}']
    source = '\n'.join(rows) + '\n'
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '0'})
    if mode == 'path':
        path = tmp_path / 'deep-unused.btor2'; path.write_text(source)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=source, **options)
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
