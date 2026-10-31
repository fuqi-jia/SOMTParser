"""Semantic checks for compact/list forms occurring in XCSP competition inputs."""
import itertools

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def translate(body, variables='<var id="x">0..2</var><var id="y">0..2</var>'):
    kind = "COP" if "<objectives>" in body else "CSP"
    result = sp.translate(
        source='<instance format="XCSP3" type="' + kind + '"><variables>' + variables
        + '</variables>' + body + '</instance>',
        language="xcsp3", dialect=sp.OmtDialect.Z3,
    )
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.Optimize()
    target.from_string(result.to_smt2(sp.OmtDialect.Z3))
    return target


@pytest.mark.parametrize("values", [
    [0, 4, 8, 12], [-9, -5, -1, 3, 7], [2, 6, 10, 14], [1, 3, 5, 7],
    [0, 4, 8, 13], [0, 4], [0, 1, 2],
    [-9223372036854775808, -1, 9223372036854775806],
])
@pytest.mark.parametrize("array", [False, True])
def test_sparse_domain_compaction_matches_the_complete_enumerated_set(values, array):
    domain = ' '.join(str(value) for value in values)
    declaration = (f'<array id="x" size="[2]">{domain}</array>' if array
                   else f'<var id="x">{domain}</var>')
    target = translate('<constraints/>', declaration)
    names = ['x[0]', 'x[1]'] if array else ['x']
    expected = z3.And(*[z3.Or(*[z3.Int(name) == value for value in values])
                       for name in names])
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("source", [
    '<array id="rows" size="[4]">1 3 5</array>',
    '<array id="rows" size="[4]"><domain for="others">1 3 5</domain></array>',
    '<var id="rows">1 3 5</var>',
])
def test_array_content_alias_keeps_its_own_shape_and_independent_values(source):
    target = translate(
        '<constraints><intension>ne(diag[0],diag[1])</intension></constraints>',
        source + '<array id="diag" size="[2]" as="rows"/>',
    )
    names = ["rows"] if source.startswith('<var ') else [f"rows[{i}]" for i in range(4)]
    cells = [z3.Int(name) for name in names + ["diag[0]", "diag[1]"]]
    expected = z3.And(*[z3.Or(v == 1, v == 3, v == 5) for v in cells],
                      cells[-2] != cells[-1])
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat
    assert target.check() == z3.sat


@pytest.mark.parametrize("tail", [
    '<array id="a" size="[2]" as="missing"/>',
    '<array id="a" size="[2]" as="x">0..1</array>',
    '<array id="a" size="[2]" as="x"/><array id="b" size="[3]" as="a"/>',
])
def test_array_content_alias_checks_reference_and_content(tail):
    result = sp.translate(source='<instance format="XCSP3" type="CSP"><variables>'
                          '<array id="x" size="[2]">0..1</array>' + tail
                          + '</variables></instance>', language="xcsp3")
    assert not result.ok
    assert any("as" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("except_zero", [False, True])
def test_all_different_expression_views_match_independent_values(except_zero):
    body = ('<constraints><allDifferent><list>mod(add(2,x),3) sub(y,1) 0</list>'
            + ('<except>0</except>' if except_zero else '')
            + '</allDifferent></constraints>')
    target = translate(body)
    x, y = z3.Ints("x y")
    for xv, yv in itertools.product(range(3), repeat=2):
        values = [(2 + xv) % 3, yv - 1, 0]
        included = [v for v in values if not except_zero or v != 0]
        target.push()
        target.add(x == xv, y == yv)
        assert (target.check() == z3.sat) == (len(included) == len(set(included)))
        target.pop()


@pytest.mark.parametrize("expression,expected", [
    ("mod(x,0)", False),
    ("if(eq(x,0),1,mod(x,0))", True),
    ("if(eq(x,0),mod(x,0),1)", False),
])
def test_all_different_views_preserve_partial_and_conditional_operands(expression, expected):
    target = translate('<constraints><allDifferent>' + expression + ' 0</allDifferent>'
                       '<intension>eq(x,0)</intension></constraints>')
    assert (target.check() == z3.sat) == expected


def test_compact_group_arguments_expand_before_numbering():
    target = translate(
        '<constraints><group><intension>eq(add(%0,mul(%1,2)),%2)</intension>'
        '<args>q[0][]</args><args>q[1][0] q[1][1..2]</args>'
        '</group></constraints>',
        '<array id="q" size="[2][3]">0..2</array>',
    )
    cells = [[z3.Int(f"q[{i}][{j}]") for j in range(3)] for i in range(2)]
    expected = z3.And(
        *[z3.And(v >= 0, v <= 2) for row in cells for v in row],
        *[row[0] + 2 * row[1] == row[2] for row in cells],
    )
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("rows", [255, 256, 1025])
@pytest.mark.parametrize("condition", ["eq", "gt"])
def test_large_group_compaction_keeps_all_equal_and_not_all_equal_relations(rows, condition):
    # Exceptional rows cross the compaction threshold and the batch boundary.
    # Losing either leaves three independently declared variables unconstrained.
    indices = [(0, 1, 2)] * rows
    indices[rows // 2] = (3, 4, 5)
    indices[-1] = (6, 7, 8)
    arguments = ''.join('<args>' + ' '.join(f'q[{i}]' for i in row) + '</args>'
                        for row in indices)
    target = translate(
        '<constraints><group><nValues><list>%0 %1 %2</list>'
        f'<condition>({condition},1)</condition></nValues>{arguments}'
        '</group></constraints>', '<array id="q" size="[9]">0..2</array>')
    q = [z3.Int(f'q[{i}]') for i in range(9)]
    relations = []
    for a, b, c in set(indices):
        equal = z3.And(q[a] == q[b], q[b] == q[c])
        relations.append(equal if condition == 'eq' else z3.Not(equal))
    expected = z3.And(*[z3.And(v >= 0, v <= 2) for v in q], *relations)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("rows", [256, 1025])
def test_large_group_compaction_keeps_partial_arithmetic_guards(rows):
    indices = [(0, 1)] * rows
    indices[-1] = (2, 3)
    arguments = ''.join(f'<args>q[{a}] q[{b}]</args>' for a, b in indices)
    target = translate(
        '<constraints><group><intension>ne(div(%0,%1),1)</intension>'
        + arguments + '</group></constraints>',
        '<array id="q" size="[4]">0..2</array>')
    q = [z3.Int(f'q[{i}]') for i in range(4)]
    expected = z3.And(*[z3.And(v >= 0, v <= 2) for v in q],
                      q[1] != 0, q[3] != 0, q[0] / q[1] != 1, q[2] / q[3] != 1)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


def test_compact_group_tail_and_expression_argument():
    target = translate(
        '<constraints><group><sum><list>%...</list><condition>(eq,%0)</condition>'
        '</sum><args>x add(y, 1) q[0][]</args><args>y q[1][]</args>'
        '</group></constraints>',
        '<array id="q" size="[2][2]">0..2</array>'
        '<var id="x">0..2</var><var id="y">0..2</var>',
    )
    x, y = z3.Ints("x y")
    cells = [z3.Int(f"q[{i}][{j}]") for i in range(2) for j in range(2)]
    expected = z3.And(*[z3.And(v >= 0, v <= 2) for v in [x, y] + cells],
                      x == y + 1 + cells[0] + cells[1], y == cells[2] + cells[3])
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind", ["sum", "product", "minimum", "maximum", "nValues"])
def test_expression_objective_values(kind):
    target = translate('<objectives><minimize type="' + kind + '">'
                       'ne(x, 1) add(y, 2)</minimize></objectives>')
    x, y = z3.Ints("x y")
    solver = z3.Solver()
    solver.add(*target.assertions())
    for xv, yv in itertools.product(range(3), repeat=2):
        solver.push()
        solver.add(x == xv, y == yv)
        assert solver.check() == z3.sat
        a, b = int(xv != 1), yv + 2
        expected = {"sum": a + b, "product": a * b, "minimum": min(a, b),
                    "maximum": max(a, b), "nValues": len({a, b})}[kind]
        assert solver.model().eval(target.objectives()[0]).as_long() == expected
        solver.pop()


def test_sum_predicates_and_mixed_coefficients():
    target = translate('<constraints><sum><list>eq(x, 1) add(y, 1)</list>'
                       '<coeffs>2 x</coeffs><condition>(eq,2)</condition>'
                       '</sum></constraints>')
    x, y = z3.Ints("x y")
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2,
                      2 * z3.If(x == 1, 1, 0) + x * (y + 1) == 2)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("body,relation", [
    ('<sum><list>x</list><coeffs>-1</coeffs><condition>(eq,0)</condition></sum>',
     lambda x,y: x == 0),
    ('<count><list>ne(x,1) eq(y,2)</list><values>1</values><condition>(eq,1)</condition></count>',
     lambda x,y: z3.Xor(x != 1, y == 2)),
    ('<count><list>x</list><values>1</values><condition>(eq,y)</condition></count>',
     lambda x,y: z3.If(x == 1, 1, 0) == y),
])
def test_singleton_aggregates_and_counted_expressions(body, relation):
    target = translate('<constraints>' + body + '</constraints>')
    x, y = z3.Ints("x y")
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2, relation(x,y))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("body", [
    '<constraints><sum><list>div(6,x) y</list><condition>(ge,0)</condition></sum></constraints>',
    '<constraints><count><list>div(6,x) y</list><values>1</values><condition>(ge,0)</condition></count></constraints>',
    '<objectives><minimize type="sum">div(6,x) y</minimize></objectives>',
    '<objectives><minimize type="nValues">div(6,x) y</minimize></objectives>',
    '<objectives><minimize type="lex">div(6,x) y</minimize></objectives>',
])
def test_list_expression_keeps_division_definedness(body):
    target = translate(body)
    solver = z3.Solver()
    solver.add(*target.assertions(), z3.Int("x") == 0)
    assert solver.check() == z3.unsat


def test_list_expression_only_requires_selected_branch():
    target = translate('<objectives><minimize type="sum">'
                       'if(eq(x,0),7,div(6,x)) y</minimize></objectives>')
    solver = z3.Solver()
    solver.add(*target.assertions(), z3.Int("x") == 0, z3.Int("y") == 1)
    assert solver.check() == z3.sat
    assert solver.model().eval(target.objectives()[0]).as_long() == 8


@pytest.mark.parametrize("operator", ["in", "notin"])
def test_condition_brace_set(operator):
    target = translate('<constraints><sum><list>x y</list><condition>('
                       + operator + ',{0,2,4})</condition></sum></constraints>')
    x, y = z3.Ints("x y")
    membership = z3.Or(x+y == 0, x+y == 2, x+y == 4)
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2,
                      membership if operator == "in" else z3.Not(membership))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


def test_repeated_instantiation_values_and_objective_coefficients():
    target = translate('<constraints><instantiation><list>q[]</list>'
                       '<values>1x2 0 2x2</values></instantiation></constraints>'
                       '<objectives><minimize type="sum"><list>q[]</list>'
                       '<coeffs>-2x2 3x3</coeffs></minimize></objectives>',
                       '<array id="q" size="[5]">0..2</array>')
    solver = z3.Solver()
    solver.add(*target.assertions())
    assert solver.check() == z3.sat
    model = solver.model()
    assert [model.eval(z3.Int(f"q[{i}]")).as_long() for i in range(5)] == [1,1,0,2,2]
    assert model.eval(target.objectives()[0]).as_long() == 8


def test_sum_repeated_coefficients_preserve_multiplicity():
    target = translate('<constraints><sum><list>q[]</list><coeffs>2x3 -1</coeffs>'
                       '<condition>(eq,0)</condition></sum></constraints>',
                       '<array id="q" size="[4]">0..2</array>')
    q = [z3.Int(f"q[{i}]") for i in range(4)]
    expected = z3.And(*[z3.And(v >= 0, v <= 2) for v in q],
                      2 * (q[0] + q[1] + q[2]) - q[3] == 0)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


def test_repeated_task_lengths_preserve_no_overlap():
    target = translate('<constraints><noOverlap><origins>q[]</origins>'
                       '<lengths>1x3</lengths></noOverlap></constraints>',
                       '<array id="q" size="[3]">0..2</array>')
    q = [z3.Int(f"q[{i}]") for i in range(3)]
    expected = z3.And(*[z3.And(v >= 0, v <= 2) for v in q], z3.Distinct(*q))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("op", ["lt", "le", "gt", "ge"])
def test_singleton_lex_is_integer_order(op):
    target = translate('<constraints><lex><list>x</list><list>y</list>'
                       '<operator>' + op + '</operator></lex></constraints>')
    x, y = z3.Ints("x y")
    relation = {"lt": x < y, "le": x <= y, "gt": x > y, "ge": x >= y}[op]
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2, relation)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("condition", ["(eq,1)", "(le,1)", "(lt,2)",
                                       "(ne,1)", "(gt,1)", "(ge,2)"])
@pytest.mark.parametrize("excluded", ["", "<except>0</except>"])
def test_nvalues_uniformity_preserves_exclusions(condition, excluded):
    target = translate('<constraints><nValues><list>x y z</list>' + excluded
                       + '<condition>' + condition + '</condition></nValues></constraints>',
                       '<var id="x">0..2</var><var id="y">0..2</var><var id="z">0..2</var>')
    x, y, z = z3.Ints("x y z")
    solver = z3.Solver()
    solver.add(*target.assertions())
    for xv, yv, zv in itertools.product(range(3), repeat=3):
        count = len({xv, yv, zv} - ({0} if excluded else set()))
        op, value = condition[1:-1].split(',')
        rhs = int(value)
        expected = {"eq": count == rhs, "le": count <= rhs, "lt": count < rhs,
                    "ne": count != rhs, "gt": count > rhs, "ge": count >= rhs}[op]
        solver.push()
        solver.add(x == xv, y == yv, z == zv)
        assert solver.check() == (z3.sat if expected else z3.unsat)
        solver.pop()


@pytest.mark.parametrize("coeffs", ["1x9223372036854775807", "1x-1"])
def test_invalid_sum_repetitions_remain_rejected(coeffs):
    result = sp.translate(source='<instance format="XCSP3" type="CSP"><variables>'
                          '<var id="x">0..2</var><var id="y">0..2</var></variables>'
                          '<constraints><sum><list>x y</list><coeffs>' + coeffs
                          + '</coeffs><condition>(eq,0)</condition></sum></constraints></instance>',
                          language="xcsp3")
    assert not result.ok


@pytest.mark.parametrize("values", ["1x0", "1x-2", "1x9223372036854775807", "1x2 0", "1xabc"])
def test_invalid_repetitions_remain_rejected(values):
    result = sp.translate(source='<instance format="XCSP3" type="CSP"><variables>'
                          '<array id="q" size="[2]">0..2</array></variables><constraints>'
                          '<instantiation><list>q[]</list><values>' + values
                          + '</values></instantiation></constraints></instance>', language="xcsp3")
    assert not result.ok


@pytest.mark.parametrize("args", ["q[0..3]", "q[0..1]", "add(q[0],1)) q[1] q[2]"])
def test_invalid_group_argument_lists_remain_rejected(args):
    result = sp.translate(source='<instance format="XCSP3" type="CSP"><variables>'
                          '<array id="q" size="[3]">0..2</array></variables><constraints>'
                          '<group><intension>eq(add(%0,%1),%2)</intension><args>' + args
                          + '</args><args>q[]</args></group></constraints></instance>',
                          language="xcsp3")
    assert not result.ok


@pytest.mark.parametrize("minimum", [True, False])
@pytest.mark.parametrize("site", ["objective", "intension", "constraint"])
def test_large_extremum_matches_order_characterization(minimum, site):
    # ButtonsScissors competition models minimize a 25-element maximum.
    # Characterize the result by order and membership, independently of ITEs.
    names = [f"q[{i}]" for i in range(25)]
    kind = "minimum" if minimum else "maximum"
    if site == "objective":
        body = f'<objectives><minimize type="{kind}">q[]</minimize></objectives>'
    elif site == "intension":
        op = "min" if minimum else "max"
        body = '<constraints><intension>eq(' + op + '(' + ','.join(names) + '),r)</intension></constraints>'
    else:
        body = f'<constraints><{kind}><list>q[]</list><condition>(eq,r)</condition></{kind}></constraints>'
    target = translate(body, '<array id="q" size="[25]">-3..3</array>'
                             '<var id="r">-3..3</var>')
    q = [z3.Int(name) for name in names]
    r = target.objectives()[0] if site == "objective" else z3.Int("r")
    extremum = z3.And(z3.Or(*[r == value for value in q]),
                       *[r <= value if minimum else r >= value for value in q])
    solver = z3.Solver()
    if site == "objective":
        solver.add(*target.assertions(), z3.Not(extremum))
    else:
        expected = z3.And(*[z3.And(v >= -3, v <= 3) for v in q + [r]], extremum)
        solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("minimum", [True, False])
@pytest.mark.parametrize("site", ["objective", "intension"])
@pytest.mark.parametrize("position", range(5))
def test_extremum_requires_every_operand_defined(minimum, site, position):
    terms = ["7", "-9", "2", "0"]
    terms.insert(position, "div(6,x)")
    if site == "objective":
        kind = "minimum" if minimum else "maximum"
        body = f'<objectives><minimize type="{kind}">' + ' '.join(terms) + '</minimize></objectives>'
    else:
        op = "min" if minimum else "max"
        body = '<constraints><intension>eq(' + op + '(' + ','.join(terms) + '),y)</intension></constraints>'
    target = translate(body, '<var id="x">0..2</var><var id="y">-20..20</var>')
    x, y = z3.Ints("x y")
    solver = z3.Solver()
    solver.add(*target.assertions())
    solver.push()
    solver.add(x == 0)
    assert solver.check() == z3.unsat
    solver.pop()
    solver.add(x == 1)
    assert solver.check() == z3.sat
    value = target.objectives()[0] if site == "objective" else y
    solver.add(value != (-9 if minimum else 7))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind", ["minimum", "maximum"])
def test_extremum_preserves_conditional_operand_definedness(kind):
    target = translate('<objectives><minimize type="' + kind + '">'
                       '7 -9 if(eq(x,0),2,div(6,x)) 0 1</minimize></objectives>')
    solver = z3.Solver()
    solver.add(*target.assertions(), z3.Int("x") == 0)
    assert solver.check() == z3.sat
    assert solver.model().eval(target.objectives()[0]).as_long() == (-9 if kind == "minimum" else 7)


@pytest.mark.parametrize("condition", [None, "(eq,1)", "(le,1)", "(lt,2)",
                                        "(ne,1)", "(gt,1)", "(ge,2)"])
def test_nary_uniformity_matches_independent_equality_chain(condition):
    names = [f"x{i}" for i in range(8)]
    variables = ''.join(f'<var id="{name}">-2..2</var>' for name in names)
    kind = "allEqual" if condition is None else "nValues"
    body = '<constraints><' + kind + '><list>' + ' '.join(names) + '</list>'
    if condition is not None:
        body += '<condition>' + condition + '</condition>'
    body += '</' + kind + '></constraints>'
    target = translate(body, variables)
    terms = [z3.Int(name) for name in names]
    uniform = z3.And(*[terms[0] == term for term in terms[1:]])
    relation = z3.Not(uniform) if condition in {"(ne,1)", "(gt,1)", "(ge,2)"} else uniform
    expected = z3.And(*[z3.And(term >= -2, term <= 2) for term in terms], relation)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*target.assertions()), expected))
    assert solver.check() == z3.unsat
