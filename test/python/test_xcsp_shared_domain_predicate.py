"""Complete two-point domains can share their entire predicate, including bounds."""
import pytest
import somtparser as sp

z3 = pytest.importorskip('z3')


@pytest.mark.parametrize('count', [255, 256, 257])
@pytest.mark.parametrize('members', [(-1, 1), (-5, 3), (-(2**63), 2**63-1)])
def test_shared_domain_equals_exact_members_and_keeps_every_cell(count, members):
    source = (f'<instance format="XCSP3" type="CSP"><variables>'
              f'<array id="x" size="[{count}]">{members[0]} {members[1]}</array>'
              '</variables></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    actual = z3.And(*z3.parse_smt2_string(script))
    expected = z3.And(*[z3.Or(z3.Int(f'x[{i}]') == members[0],
                              z3.Int(f'x[{i}]') == members[1]) for i in range(count)])
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    assert script.count('(declare-fun ') + script.count('(declare-const ') == count


@pytest.mark.parametrize('future', ['__somt_xcsp_group_0', '|__somt_xcsp_group_0|'])
def test_domain_helper_does_not_capture_a_future_source_declaration(future):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="x" size="[256]">-1 1</array>'
              f'<var id="{future}">-2..2</var></variables>'
              '</instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    assert '(define-fun __somt_xcsp_group_0 ' not in script
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(script))
    assert solver.check() == z3.sat
    # Quoting is an SMT symbol spelling; the collision check does not require
    # feeding that spelling into the XCSP intension expression grammar.
    source_variable = z3.Int('__somt_xcsp_group_0')
    for value in (-3, -2, 0, 2, 3):
        solver.push()
        solver.add(source_variable == value)
        assert solver.check() == (z3.sat if -2 <= value <= 2 else z3.unsat)
        solver.pop()
    solver.add(z3.Int('x[255]') == 0)
    assert solver.check() == z3.unsat


def test_shared_domain_aliases_preserve_independent_exact_source_cells():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="a" size="[256]">-1 1</array>'
              '<var id="b" as="a"/>'
              '<var id="c" as="a[255]"/>'
              '</variables></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    names = [f'{array}[{i}]' for array in ('a', 'b') for i in range(256)] + ['c']
    actual = z3.And(*z3.parse_smt2_string(script))
    expected = z3.And(*[z3.Or(z3.Int(name) == -1, z3.Int(name) == 1)
                       for name in names])
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(actual, z3.Int('a[255]') == -1, z3.Int('b[255]') == 1,
               z3.Int('c') == 1)
    assert solver.check() == z3.sat
