"""Independent relation checks for iterative XCSP trees, templates and tables."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def source(body):
    return ('<instance format="XCSP3" type="CSP"><variables>'
            '<var id="x">-2..2</var><var id="y">-2..2</var>'
            '<var id="z">-2..2</var></variables><constraints>' + body
            + '</constraints></instance>')


def equivalent(body, relation, tmp_path=None):
    text = source(body)
    if tmp_path is None:
        result = sp.translate(source=text, language="xcsp3")
    else:
        path = tmp_path / 'deep.xml'
        path.write_text(text)
        result = sp.translate(path=str(path), language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    x, y, z = z3.Ints('x y z')
    expected = z3.And(*(z3.And(v >= -2, v <= 2) for v in (x, y, z)), relation)
    check = z3.Solver()
    check.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert check.check() == z3.unsat
    return result


@pytest.mark.parametrize('depth', [129, 130, 1024])
def test_deep_intension_keeps_sign_and_repeated_dag(depth):
    x, y = z3.Ints('x y')
    expression = 'neg(' * depth + 'x' + ')' * depth
    equivalent('<intension>eq(add(' + expression + ',' + expression + '),y)</intension>',
               2 * ((-1) ** depth) * x == y)


@pytest.mark.parametrize('file_backed', [False, True])
def test_deep_block_group_copy_and_batched_negation_preserve_all_rows(file_backed, tmp_path):
    x, y, z = z3.Ints('x y z')
    pattern = ('<block>' * 150
               + '<intension>ne(%0,0)</intension><intension>eq(%0,%1)</intension>'
               + '</block>' * 150)
    rows = ['x y', 'y z'] * 129
    body = '<group>' + pattern + ''.join('<args>' + row + '</args>' for row in rows) + '</group>'
    equivalent(body, z3.And(x != 0, y != 0, x == y, y == z),
               tmp_path if file_backed else None)


def test_nested_group_continuations_preserve_siblings_and_slide_order():
    x, y, z = z3.Ints('x y z')
    # Inner templates have literal bodies; repeated nested group constraints
    # must finish before the outer row continues to the slide and next sibling.
    nested = ('<group><block><group><intension>ne(x,y)</intension>'
              '<args>x</args><args>y</args></group>'
              '</block><args>x</args><args>z</args></group>'
              '<slide><list>x y z</list><intension>le(%0,%1)</intension></slide>'
              '<intension>eq(z,2)</intension>')
    equivalent(nested, z3.And(x != y, x <= y, y <= z, z == 2))


@pytest.mark.parametrize('polarity', ['supports', 'conflicts'])
@pytest.mark.parametrize('grouped', [False, True])
def test_wide_factored_tables_keep_repeated_coordinates_wildcards_and_aliases(polarity, grouped):
    x, y, z = z3.Ints('x y z')
    width = 96
    # First row repeated at the end deliberately tests sorted partitioning and
    # duplicate tuple handling. The last cell is wildcard in the middle row.
    tuples = ('(' + ','.join(['0'] * (width - 1) + ['1']) + ')'
              + '(' + ','.join(['2'] * (width - 1) + ['*']) + ')'
              + '(' + ','.join(['0'] * (width - 1) + ['1']) + ')')

    def table(left, right):
        return ('<extension><list>' + ' '.join([left] * (width - 1) + [right])
                + '</list><' + polarity + '>' + tuples + '</' + polarity + '></extension>')

    if grouped:
        body = ('<group>' + table('%0', '%1')
                + '<args>x y</args><args>y z</args><args>x y</args></group>')
    else:
        body = ('<block>' * 100 + table('x', 'y') + '</block>' * 100
                + table('y', 'z') + table('x', 'y'))
    first = z3.Or(z3.And(x == 0, y == 1), x == 2)
    second = z3.Or(z3.And(y == 0, z == 1), y == 2)
    equivalent(body, z3.And(first, second) if polarity == 'supports'
               else z3.And(z3.Not(first), z3.Not(second)))


@pytest.mark.parametrize('ending', ['</wrong>', '', '</intension extra>'])
def test_deep_xml_errors_are_not_silently_accepted(ending):
    text = source('<block>' * 300 + '<intension>eq(x,1)' + ending)
    result = sp.translate(source=text, language="xcsp3")
    assert not result.ok


def test_deep_partial_expression_keeps_zero_divisor_guard():
    x, y = z3.Ints('x y')
    # The unused div branch remains lazy. Sharing/parsing must not hoist its
    # nonzero guard above the conditional or drop it from the selected branch.
    expression = 'neg(' * 130 + 'if(eq(y,0),1,div(x,y))' + ')' * 130
    relation = z3.Or(y == 0,
                     z3.And(y != 0, z3.If(x * y >= 0, z3.Abs(x) / z3.Abs(y),
                                          -(z3.Abs(x) / z3.Abs(y))) == 1))
    equivalent('<intension>eq(' + expression + ',1)</intension>', relation)
