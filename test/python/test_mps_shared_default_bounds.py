"""Sharing default bound leaves preserves complete MPS variable domains."""
import pytest
import somtparser as sp

z3 = pytest.importorskip('z3')


@pytest.mark.parametrize('packed', [False, True])
def test_shared_default_bounds_keep_marker_and_bound_overrides(packed):
    lines = ['NAME defaults', 'ROWS', ' N cost']
    if packed:
        lines.extend(f' E padding{i}' for i in range(65536))
    lines.extend(['COLUMNS', " marker0 'MARKER' 'INTORG'", ' a cost 0', ' b cost 0',
                  ' c cost 0', " marker1 'MARKER' 'INTEND'", ' u cost 0', ' v cost 0',
                  ' f cost 0', ' n cost 0', ' s cost 0', ' q cost 0', 'BOUNDS',
                  ' LO bounds c 2', ' FR bounds f', ' MI bounds n', ' SC bounds s 3',
                  ' BV bounds q', 'ENDATA'])
    result = sp.translate(source='\n'.join(lines) + '\n', language='mps', dialect=sp.OmtDialect.Z3)
    assert result.ok, [item.message for item in result.diagnostic_items]
    assert result.uses_packed_smt_stream == packed
    opt = z3.Optimize()
    opt.from_string(result.to_smt2(sp.OmtDialect.Z3))
    a, b, c, q = z3.Ints('a b c q')
    u, v, f, n, s = z3.Reals('u v f n s')
    expected = z3.And(a >= 0, a <= 1, b >= 0, b <= 1, c >= 2, u >= 0, v >= 0,
                      q >= 0, q <= 1, z3.Or(s == 0, z3.And(s >= 1, s <= 3)))
    solver = z3.Solver()
    solver.add(z3.Xor(expected, z3.And(*opt.assertions())))
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(*opt.assertions(), a == 0, b == 1, c == 3, u == 0, v == 0,
               f == -100, n == -100, s == 0, q == 1)
    assert solver.check() == z3.sat
