"""Shared intension helpers preserve assignments, aliases and definedness."""
import itertools
import re

import pytest
import somtparser as sp
import z3


def compile_group(expression, rows, domains=None):
    domains = domains or {"x": "-2..2", "y": "-2..2", "d": "-1..1"}
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              + ''.join(f'<var id="{name}">{domain}</var>' for name, domain in domains.items())
              + '</variables><constraints><group><intension>' + expression
              + '</intension>' + ''.join('<args>' + row + '</args>' for row in rows)
              + '</group></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=3000)
    solver.add(z3.parse_smt2_string(script, ctx=ctx))
    helpers = re.findall(r'\(define-fun(?:-rec)? (__somt_xcsp_group_\d+)\s+\(', script)
    return solver, helpers


def check_assignments(solver, domains, expected):
    names = list(domains)
    for values in itertools.product(*(domains[name] for name in names)):
        assignment = dict(zip(names, values))
        solver.push()
        solver.add(*(z3.Int(name, ctx=solver.ctx) == value for name, value in assignment.items()))
        assert solver.check() == (z3.sat if expected(**assignment) else z3.unsat), assignment
        solver.pop()


def trunc_div(a, b):
    return (abs(a) // abs(b)) * (-1 if (a < 0) != (b < 0) else 1)


@pytest.mark.parametrize("op", ["div", "mod"])
@pytest.mark.parametrize("divisor", [-2, 2])
def test_literal_specialization_has_signed_integer_semantics(op, divisor):
    solver, helpers = compile_group(f'eq(add({op}(%0,%1),1),%2)', [f'x {divisor} y'] * 4)
    assert len(helpers) == 1
    def expected(x, y):
        quotient = trunc_div(x, divisor)
        return y == 1 + (quotient if op == "div" else x - quotient * divisor)
    check_assignments(solver, {"x": range(-2, 3), "y": range(-2, 3)}, expected)


def test_literal_classes_are_separate_and_actual_aliases_are_not_folded():
    # The first row aliases both parameters; the next does not. A body built
    # from the first actual row could simplify x-x and wrongly accept x!=y.
    rows = ['x x 0', 'x y 0', 'x x 0', 'x y 0', 'x y 1'] * 3
    solver, helpers = compile_group('eq(sub(%0,%1),mul(%2,%0))', rows)
    assert len(helpers) == 2
    check_assignments(solver, {"x": range(-2, 3), "y": range(-2, 3)},
                      lambda x, y: x == y and x - y == x)


@pytest.mark.parametrize("guarded", [False, True])
def test_free_globals_keep_conditional_zero_divisor_definedness(guarded):
    term = 'add(mod(%0,d),mod(%0,d))'
    if guarded:
        term = 'if(eq(d,0),1,' + term + ')'
    solver, helpers = compile_group('eq(' + term + ',%1)', ['x y'] * 4)
    assert len(helpers) == 1
    def expected(x, y, d):
        return (guarded and y == 1) if d == 0 else y == 2 * (x - trunc_div(x, d) * d)
    check_assignments(solver, {"x": range(-2, 3), "y": range(-2, 3), "d": range(-1, 2)}, expected)


@pytest.mark.parametrize("name", ["__somt_xcsp_group_0_p0", "__somt_xcsp_group_1_p0"])
def test_global_names_cannot_be_captured_by_generated_parameters(name):
    solver, helpers = compile_group('eq(add(%0,' + name + '),%1)', ['x y'] * 4,
                                   {"x": "-2..2", "y": "-2..2", name: "-1..1"})
    assert len(helpers) == 1
    check_assignments(solver, {"x": range(-2, 3), "y": range(-2, 3), name: range(-1, 2)},
                      lambda **a: a['x'] + a[name] == a['y'])


def test_boolean_domain_variables_keep_boolean_coercion():
    solver, helpers = compile_group('imp(%0,eq(add(%1,1),%2))', ['b x y'] * 4,
                                   {"b": "0..1", "x": "-2..2", "y": "-2..2"})
    assert len(helpers) == 1
    check_assignments(solver, {"b": range(2), "x": range(-2, 3), "y": range(-2, 3)},
                      lambda b, x, y: not b or x + 1 == y)


def test_literal_power_exponents_are_specialized():
    solver, helpers = compile_group('eq(add(pow(%0,%1),1),%2)', ['x 2 y'] * 4 + ['x 3 y'] * 4)
    assert len(helpers) == 2
    check_assignments(solver, {"x": range(-2, 3), "y": range(-2, 3)},
                      lambda x, y: x ** 2 + 1 == y and x ** 3 + 1 == y)


def test_partial_compound_actuals_keep_substitution_evaluation():
    solver, helpers = compile_group('eq(if(eq(d,0),1,%0),%1)', ['div(x,d) y'] * 4)
    assert not helpers
    check_assignments(solver, {"x": range(-2, 3), "y": range(-2, 3), "d": range(-1, 2)},
                      lambda x, y, d: y == (1 if d == 0 else trunc_div(x, d)))


@pytest.mark.parametrize("rows", [['x y', 'x'], ['x y', 'unknown y']])
def test_invalid_arguments_still_report_errors(rows):
    with pytest.raises(AssertionError):
        compile_group('eq(add(%0,1),%1)', rows)
