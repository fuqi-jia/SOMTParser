"""XCSP3 3.2 section 2.10: an absent domain is not an empty domain."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def translate(variables, constraints="", objectives="", *, path=None):
    source = (f'<instance format="XCSP3" type="{"COP" if objectives else "CSP"}">'
              f'<variables>{variables}</variables><constraints>{constraints}</constraints>'
              + (f'<objectives>{objectives}</objectives>' if objectives else "")
              + '</instance>')
    if path is not None:
        path.write_text(source)
        return sp.translate(path=str(path), language="xcsp3", dialect=sp.OmtDialect.Z3)
    return sp.translate(source=source, language="xcsp3", dialect=sp.OmtDialect.Z3)


def relation(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(dialect=sp.OmtDialect.Z3)
    parsed = z3.Optimize()
    parsed.from_string(script)
    return script, z3.And(*parsed.assertions()), list(parsed.objectives())


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("file_input", [False, True])
def test_sparse_array_preserves_all_defined_coordinates_and_signed_cost(file_input, tmp_path):
    variables = ('<array id="x" size="[2][3]">'
                 '<domain for="x[0][0] x[0][2] x[1][1]">0..1</domain>'
                 '</array>')
    constraints = ('<group><intension>ne(%0,%1)</intension>'
                   '<args>x[0][0] x[0][2]</args><args>x[0][2] x[1][1]</args></group>')
    objective = ('<maximize type="sum"><list>x[0][0] x[0][2] x[1][1]</list>'
                 '<coeffs>1 2 3</coeffs></maximize>')
    script, actual, costs = relation(translate(
        variables, constraints, objective, path=tmp_path/'sparse.xml' if file_input else None))
    a, b, c, cost = z3.Ints('x[0][0] x[0][2] x[1][1] observed_cost')
    assert len(costs) == 1
    for absent in ['x[0][1]', 'x[1][0]', 'x[1][2]']:
        assert absent not in script
    equivalent(z3.And(actual, cost == costs[0]), z3.And(
        *[z3.And(v >= 0, v <= 1) for v in (a, b, c)],
        a != b, b != c, cost == -(a + 2*b + 3*c)))


def test_defined_slices_and_array_domain_alias_keep_holes_and_independence():
    script, actual, _ = relation(translate(
        '<array id="x" size="[2][3]" startIndex="2">'
        '<domain for="x[2][2..3] x[3][4]">-2 0 2</domain></array>'
        '<var id="y" as="x"/><var id="z" as="y[3][4]"/>',
        '<sum><list>x[2][2..3]</list><condition>(eq,0)</condition></sum>'
        '<intension>ne(x[3][4],y[3][4])</intension>'))
    names = [f'{base}{cell}' for base in ['x', 'y']
             for cell in ['[2][2]', '[2][3]', '[3][4]']] + ['z']
    for base in ['x', 'y']:
        for cell in ['[2][4]', '[3][2]', '[3][3]']:
            assert base + cell not in script
    equivalent(actual, z3.And(
        *[z3.Or(*[z3.Int(n) == v for v in [-2, 0, 2]]) for n in names],
        z3.Int('x[2][2]') + z3.Int('x[2][3]') == 0,
        z3.Int('x[3][4]') != z3.Int('y[3][4]')))


@pytest.mark.parametrize("variables", [
    '<var id="x"/>',
    '<var id="x"> \n </var><var id="y" as="x"/>',
    '<array id="x" size="[2]"/>',
    '<array id="x" size="[2]"><domain for="x[0]"/></array>',
    '<array id="x" size="[2]"><domain for="x[0]">0..1</domain>'
    '<domain for="others"/></array>',
    '<array id="x" size="[1]"/><array id="y" size="[2]" as="x"/>',
])
@pytest.mark.parametrize("file_input", [False, True])
def test_explicit_empty_domains_export_the_empty_relation(variables, file_input, tmp_path):
    _, actual, costs = relation(translate(
        variables, path=tmp_path/'empty.xml' if file_input else None))
    assert not costs
    equivalent(actual, z3.BoolVal(False))


@pytest.mark.parametrize("constraints, objective", [
    ('<intension>eq(x[1],0)</intension>', ''),
    ('<sum><list>x[0] x[1]</list><condition>(eq,0)</condition></sum>', ''),
    ('<sum><list>x[]</list><condition>(eq,0)</condition></sum>', ''),
    ('', '<minimize>x[1]</minimize>'),
    ('', '<minimize type="sum">x[]</minimize>'),
])
def test_undefined_operands_are_rejected_instead_of_dropped(constraints, objective):
    result = translate('<array id="x" size="[2]">'
                       '<domain for="x[0]">0..1</domain></array>', constraints, objective)
    assert not result.ok
    assert result.diagnostic_items


def test_undefined_cell_cannot_supply_a_domain_alias():
    result = translate('<array id="x" size="[2]">'
                       '<domain for="x[0]">0..1</domain></array>'
                       '<var id="y" as="x[1]"/>')
    assert not result.ok


def test_empty_domain_does_not_hide_an_invalid_constraint():
    result = translate('<var id="empty"/>', '<intension>eq(undeclared,0)</intension>')
    assert not result.ok


def test_reversed_interval_is_still_a_syntax_error():
    assert not translate('<var id="x">2..1</var>').ok
