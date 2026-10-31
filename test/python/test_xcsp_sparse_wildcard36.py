"""Whole-model equivalence checks for wildcard factors over exact domains."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _member(value, domain):
    return z3.Or(*[value == item for item in domain])


def _assert_xor_unsat(result, expected):
    assert result.ok, [d.message for d in result.diagnostic_items]
    emitted = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(z3.Xor(emitted, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
@pytest.mark.parametrize("domain_x,domain_y", [
    ([-5, -1, 3], [-8, -4, 0, 4]),  # irregular negative values and an AP
    ([-8, -4, 0, 4], [-5, -1, 3]),  # AP and irregular, in opposite columns
])
def test_sparse_wildcards_are_redundant_in_the_complete_model(
        polarity, domain_x, domain_y):
    rows = [(None, 0), (-1, None)]
    tuple_text = "".join("(" + ",".join("*" if v is None else str(v) for v in row)
                         + ")" for row in rows)
    declarations = (f'<var id="x">{" ".join(map(str, domain_x))}</var>'
                    f'<var id="y">{" ".join(map(str, domain_y))}</var>')
    source = ('<instance format="XCSP3" type="CSP"><variables>' + declarations
              + '</variables><constraints><extension><list>x y</list><' + polarity
              + '>' + tuple_text + '</' + polarity
              + '></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    x, y = z3.Ints("x y")
    relation = z3.Or(y == 0, x == -1)
    expected = z3.And(_member(x, domain_x), _member(y, domain_y),
                      relation if polarity == "supports" else z3.Not(relation))
    _assert_xor_unsat(result, expected)


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
def test_all_wildcard_row_is_true_before_table_polarity(polarity):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">-5 -1 3</var><var id="y">-8 -4 0 4</var>'
              '</variables><constraints><extension><list>x y</list><' + polarity
              + '>(*,*)</' + polarity + '></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    x, y = z3.Ints("x y")
    domain = z3.And(_member(x, [-5, -1, 3]), _member(y, [-8, -4, 0, 4]))
    expected = domain if polarity == "supports" else z3.BoolVal(False)
    _assert_xor_unsat(result, expected)


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
def test_repeated_scope_and_sparse_wildcard_match_independent_relation(polarity):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">-3 -1 1</var></variables><constraints>'
              '<extension><list>x x</list><' + polarity
              + '>(*,1)</' + polarity + '></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    x = z3.Int("x")
    member = _member(x, [-3, -1, 1])
    relation = x == 1
    expected = z3.And(member, relation if polarity == "supports" else z3.Not(relation))
    _assert_xor_unsat(result, expected)


def test_sparse_wildcard_survives_array_content_alias():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="base" size="[2]">-5 -1 3</array>'
              '<array id="copy" size="[2]" as="base"/>'
              '</variables><constraints><extension><list>copy[0] copy[1]</list>'
              '<supports>(*,3)</supports></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    base = [z3.Int(f"base[{i}]") for i in range(2)]
    copy = [z3.Int(f"copy[{i}]") for i in range(2)]
    expected = z3.And(*[_member(v, [-5, -1, 3]) for v in base + copy], copy[1] == 3)
    _assert_xor_unsat(result, expected)


@pytest.mark.parametrize("container", ["group", "slide"])
def test_sparse_wildcards_in_group_and_slide_templates(container):
    variables = ''.join(f'<var id="{name}">-5 -1 3</var>' for name in "abc")
    if container == "group":
        body = ('<group><extension><list>%0 %1</list><supports>(*,3)</supports>'
                '</extension><args>a b</args><args>b c</args></group>')
    else:
        body = ('<slide><list>a b c</list><extension><list>%0 %1</list>'
                '<supports>(*,3)</supports></extension></slide>')
    result = sp.translate(source=('<instance format="XCSP3" type="CSP"><variables>'
                                  + variables + '</variables><constraints>' + body
                                  + '</constraints></instance>'), language="xcsp3")
    a, b, c = z3.Ints("a b c")
    domains = [_member(v, [-5, -1, 3]) for v in (a, b, c)]
    expected = z3.And(*domains, b == 3, c == 3)
    _assert_xor_unsat(result, expected)
