"""Large groups retain one exact relation instead of falling back to copies."""
import re

import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize('kind', ['supports', 'conflicts'])
def test_large_functional_table_is_shared_with_exact_boundary_semantics(kind):
    size = 149
    # 66,603 scalar cells: above the former 65,536-cell sharing cutoff.
    tuples = ''.join(f'({a},{b},{(a + b) % 2})'
                     for a in range(size) for b in range(size))
    variables = ''.join(f'<var id="{name}">0..{size - 1}</var>'
                        for name in ['a', 'b', 'c', 'd'])
    source = (f'<instance format="XCSP3" type="CSP"><variables>{variables}'
              '<var id="u">0..1</var><var id="v">0..1</var></variables>'
              '<constraints><group><extension><list>%0 %1 %2</list>'
              f'<{kind}>{tuples}</{kind}></extension>'
              '<args>a b u</args><args>c d v</args>'
              '</group></constraints></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    helpers = re.findall(r'\(define-fun (__somt_xcsp_group_\d+)\s+\(', script)
    assert len(helpers) == 1
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(script))
    names = ['a', 'b', 'c', 'd', 'u', 'v']
    for a, b, c, d in [(0, 0, 1, 2), (148, 147, 148, 148),
                       (3, 4, 4, 3), (-1, 0, 0, 0), (149, 0, 0, 0)]:
        for u in [0, 1]:
            for v in [0, 1]:
                values = [a, b, c, d, u, v]
                inside = all(0 <= x < size for x in [a, b, c, d])
                first = (a + b) % 2 == u
                second = (c + d) % 2 == v
                expected = inside and (first and second if kind == 'supports'
                                       else not first and not second)
                solver.push()
                solver.add(*(z3.Int(name) == value for name, value in zip(names, values)))
                assert solver.check() == (z3.sat if expected else z3.unsat), values
                solver.pop()
