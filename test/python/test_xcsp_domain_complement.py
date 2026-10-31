"""Exact domain complementation, including signed endpoint overflow guards."""
import pytest
import somtparser as sp

z3 = pytest.importorskip('z3')


@pytest.mark.parametrize('members', [
    [-1, 1], [0, 3], [-5, -4, -1, 0, 1], list(range(4)) + [7, 9, 10, 11, 12],
    [-(1 << 63), -(1 << 63) + 2], [(1 << 63) - 3, (1 << 63) - 1],
    [-(1 << 63), (1 << 63) - 1], [-100, 0, 1, 100],
])
def test_domain_complement_matches_independent_enumeration(members):
    source = ('<instance format="XCSP3" type="CSP"><variables><var id="x">'
              + ' '.join(map(str, members)) + '</var></variables></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    x = z3.Int('x')
    expected = z3.Or(*[x == v for v in members])
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    check = z3.Solver(); check.set(timeout=5000)
    check.add(z3.Xor(actual, expected))
    assert check.check() == z3.unsat


def test_many_sign_variables_keep_linear_single_node_membership():
    n = 1000
    source = (f'<instance format="XCSP3" type="CSP"><variables>'
              f'<array id="sign" size="[{n}]">-1 1</array>'
              '</variables></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    # The whole two-point domain (including its bounds) is shared once;
    # individual array cells remain declared and call that exact predicate.
    assert script.count('(define-fun ') == 1
    assert script.count('(or ') == 1
    assert '(distinct ' not in script
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(script))
    solver.push(); solver.add(z3.Int('sign[0]') == 0)
    assert solver.check() == z3.unsat
    solver.pop(); solver.add(*[z3.Int(f'sign[{i}]') == (-1 if i % 2 else 1) for i in range(n)])
    assert solver.check() == z3.sat


def test_implicit_precedence_uses_members_not_excluded_holes():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="x" size="[3]">1 3</array></variables><constraints>'
              '<precedence>x[]</precedence></constraints></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    xs = [z3.Int(f'x[{i}]') for i in range(3)]
    expected = z3.And(*[z3.Or(x == 1, x == 3) for x in xs],
                      *[z3.Implies(xs[i] == 3,
                                   z3.Or(*[xs[j] == 1 for j in range(i)]))
                        for i in range(3)])
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
