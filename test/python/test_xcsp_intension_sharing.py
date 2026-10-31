"""Repeated intensions preserve exact division and local definedness."""
import itertools

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def convert(expression, rows):
    text = ('<instance format="XCSP3" type="CSP"><variables>'
            '<var id="x">-2..2</var><var id="y">-2..2</var>'
            '<var id="d">-1..1</var></variables><constraints><group>'
            '<intension>' + expression + '</intension>'
            + ''.join('<args>' + row + '</args>' for row in rows)
            + '</group></constraints></instance>')
    translation = sp.translate(source=text, language="xcsp3")
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(translation.to_smt2()))
    return solver


def trunc_div(a, b):
    return (abs(a) // abs(b)) * (-1 if (a < 0) != (b < 0) else 1)


@pytest.mark.parametrize("op", ["div", "mod"])
@pytest.mark.parametrize("divisor", [-2, 0, 2])
def test_repeated_constant_divisors_keep_zero_rejection_and_signed_values(op, divisor):
    expression = f'eq(add({op}(%0,{divisor}),{op}(%0,{divisor})),%1)'
    solver = convert(expression, ['x y'] * 256)
    for x, y in itertools.product(range(-2, 3), repeat=2):
        expected = False
        if divisor:
            quotient = trunc_div(x, divisor)
            value = quotient if op == "div" else x - quotient * divisor
            expected = 2 * value == y
        solver.push()
        solver.add(z3.Int("x") == x, z3.Int("y") == y)
        assert (solver.check() == z3.sat) == expected
        solver.pop()


@pytest.mark.parametrize("guarded", [False, True])
def test_shared_symbolic_remainder_preserves_lazy_branch_definedness(guarded):
    term = 'add(mod(%0,d),mod(%0,d))'
    if guarded:
        term = 'if(eq(d,0),1,' + term + ')'
    solver = convert('eq(' + term + ',%1)', ['x y'] * 257)
    for x, y, d in itertools.product(range(-2, 3), range(-2, 3), range(-1, 2)):
        expected = (guarded and y == 1) if d == 0 else 2 * (x - trunc_div(x, d) * d) == y
        solver.push()
        solver.add(z3.Int("x") == x, z3.Int("y") == y, z3.Int("d") == d)
        assert (solver.check() == z3.sat) == expected
        solver.pop()
