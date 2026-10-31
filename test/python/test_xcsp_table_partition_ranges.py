"""Table prefix partitions preserve unordered rows, duplicates and wildcards."""
import itertools

import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize('positive', [False, True])
@pytest.mark.parametrize('order', ['source', 'reversed', 'interleaved', 'sorted', 'late-inversion'])
def test_factored_tables_match_the_raw_tuple_relation(positive, order):
    rows = [(-1, '*', 2), (0, 1, 2), (0, 1, 2), (0, -1, 0),
            (2, 0, '*'), ('*', 2, 1), (7, 1, 0), (1, 1, 1)]
    if order == 'reversed':
        rows.reverse()
    elif order == 'interleaved':
        rows = rows[::2] + rows[1::2]
    if order in ('sorted', 'late-inversion'):
        rows.sort(key=lambda row: tuple((cell == '*', 0 if cell == '*' else cell)
                                        for cell in row))
        if order == 'late-inversion':
            rows[-2], rows[-1] = rows[-1], rows[-2]
    kind = 'supports' if positive else 'conflicts'
    text = ''.join('(' + ','.join(map(str, row)) + ')' for row in rows)
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="a">-1..2</var><var id="b">-1..2</var><var id="c">-1..2</var>'
              '</variables><constraints><extension><list>a b c</list>'
              f'<{kind}>{text}</{kind}></extension></constraints></instance>')
    translated = sp.translate(source=source, language='xcsp3')
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx);solver.set(timeout=3000)
    solver.add(z3.parse_smt2_string(translated.to_smt2(), ctx=ctx))
    for values in itertools.product(range(-1, 3), repeat=3):
        listed = any(all(cell == '*' or cell == value for cell, value in zip(row, values))
                     for row in rows)
        solver.push()
        solver.add(*(z3.Int(name, ctx=ctx) == value for name, value in zip('abc', values)))
        assert solver.check() == (z3.sat if listed == positive else z3.unsat), values
        solver.pop()
