"""Membership and scope obligations for certified finite product domains."""
from itertools import product

import pytest
import somtparser as sp

z3 = pytest.importorskip('z3')


def values(n):
    return sorted({a * b for a, b in product(range(-n, n + 1), repeat=2)})


def domain(n, members=None):
    # Also exercise recognition on small independently enumerable sets.
    return ' ' * 1024 + ' '.join(map(str, values(n) if members is None else members))


def translate(declarations, constraints='', path=None):
    source = ('<instance format="XCSP3" type="CSP"><variables>' + declarations
              + '</variables><constraints>' + constraints + '</constraints></instance>')
    if path:
        path.write_text(source)
        result = sp.translate(path=str(path), language='xcsp3')
    else:
        result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2()
    return text, z3.And(*z3.parse_smt2_string(text))


def check_at(formula, assignments, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(formula, *[z3.Int(k) == v for k, v in assignments.items()])
    assert solver.check() == (z3.sat if expected else z3.unsat), assignments


@pytest.mark.parametrize('n', [3, 5, 7])
@pytest.mark.parametrize('file_input', [False, True])
def test_exact_product_membership_all_values(n, file_input, tmp_path):
    script, formula = translate(f'<var id="x">{domain(n)}</var>',
                                path=tmp_path/'domain.xml' if file_input else None)
    assert script.count('(declare-fun !somt_exists_') == 2
    assert len(script) < 2500
    expected = set(values(n))
    for v in range(-n * n - 1, n * n + 2):
        check_at(formula, {'x': v}, v in expected)


@pytest.mark.parametrize('change', ['missing', 'extra', 'duplicate', 'reversed', 'range'])
def test_unverified_set_keeps_its_actual_membership(change):
    n = 7
    members = values(n)
    if change == 'missing':
        members.remove(6)
    elif change == 'extra':
        members.append(11)
        members.sort()
    elif change == 'duplicate':
        members.insert(10, members[10])
    elif change == 'reversed':
        members.reverse()
    text = domain(n, members)
    if change == 'range':
        text = text.replace(' -1 0 1 ', ' -1..1 ')
    script, formula = translate(f'<var id="x">{text}</var>')
    assert '(exists ' not in script
    for v in [-50, -49, -11, 0, 6, 11, 49, 50]:
        check_at(formula, {'x': v}, v in members)


@pytest.mark.parametrize('name', ['__somt_xcsp3_domain_left', '__somt_xcsp3_domain_right'])
def test_membership_binders_cannot_capture_source_variable(name):
    _, formula = translate(f'<var id="{name}">{domain(5)}</var>')
    for v in [-25, -7, 0, 7, 25]:
        check_at(formula, {name: v}, v in values(5))


def test_array_content_alias_and_cell_domain_keep_certificates(tmp_path):
    script, formula = translate(
        f'<array id="a" size="[1]">{domain(5)}</array>'
        '<array id="b" size="[2]" as="a"/>'
        f'<array id="c" size="[1]"><domain for="others">{domain(7)}</domain></array>'
        '<var id="d" as="c[0]"/>', path=tmp_path/'aliases.xml')
    assert script.count('(declare-fun !somt_exists_') == 10
    assignment = {'a[0]': 25, 'b[0]': -25, 'b[1]': 0, 'c[0]': 49, 'd': -49}
    check_at(formula, assignment, True)
    for name in assignment:
        check_at(formula, dict(assignment, **{name: 11}), False)


@pytest.mark.parametrize('polarity', ['supports', 'conflicts'])
def test_table_labels_do_not_treat_compact_domain_as_empty(polarity):
    script, formula = translate(
        f'<var id="x">{domain(5)}</var><var id="y">0..1</var>',
        '<extension><list>x y</list><' + polarity + '>(0,0)(25,1)</' + polarity
        + '></extension>')
    for x, y in product([-25, -7, 0, 7, 25], [0, 1]):
        relation = (x, y) in {(0, 0), (25, 1)}
        check_at(formula, {'x': x, 'y': y}, x in values(5) and
                 (relation if polarity == 'supports' else not relation))


def test_array_alias_with_own_product_content_is_still_rejected():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="a" size="[1]">0..1</array>'
              f'<array id="b" size="[1]" as="a">{domain(5)}</array>'
              '</variables></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert not result.ok
    assert any('must not have its own content' in d.message for d in result.diagnostic_items)
