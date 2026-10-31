"""The linear suffix encoding retains the full XCSP lexicographic relation."""
import pytest
import somtparser as sp
import z3


def translate(n, op, *, matrix=False, right=None):
    if matrix:
        variables = f'<array id="x" size="[2][{n}]">-2..2</array>'
        operand = '<matrix>x[][]</matrix>'
    else:
        variables = (f'<array id="x" size="[{n}]">-2..2</array>'
                     f'<array id="y" size="[{n}]">-2..2</array>')
        operand = '<list>x[]</list><list>' + (right or 'y[]') + '</list>'
    return sp.translate(source='<instance format="XCSP3" type="CSP"><variables>'
                        + variables + '</variables><constraints><lex>' + operand
                        + '<operator>' + op + '</operator></lex></constraints></instance>',
                        language='xcsp3', dialect=sp.OmtDialect.Z3)


def first_difference(left, right, op):
    # Independent flat first-difference specification; no suffix recurrence.
    strict = op in ('lt', 'gt')
    ascending = op in ('lt', 'le')
    possibilities = [z3.And(*[left[j] == right[j] for j in range(i)],
                            left[i] < right[i] if ascending else left[i] > right[i])
                     for i in range(len(left))]
    if not strict:
        possibilities.append(z3.And(*[a == b for a, b in zip(left, right)]))
    return z3.Or(*possibilities)


def target(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    model = z3.Optimize()
    model.from_string(result.to_smt2(sp.OmtDialect.Z3))
    return z3.And(*model.assertions())


@pytest.mark.parametrize('op', ['lt', 'le', 'gt', 'ge'])
@pytest.mark.parametrize('n', [1, 2, 6])
def test_lex_suffix_entire_relation_all_directions(op, n):
    x, y = [[z3.Int(f'{name}[{i}]') for i in range(n)] for name in ('x', 'y')]
    expected = z3.And(*[z3.And(v >= -2, v <= 2) for v in x + y],
                      first_difference(x, y, op))
    solver = z3.Solver()
    solver.add(z3.Xor(target(translate(n, op)), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('op', ['lt', 'le', 'gt', 'ge'])
def test_lex_matrix_keeps_both_adjacent_rows_and_columns(op):
    x = [[z3.Int(f'x[{i}][{j}]') for j in range(3)] for i in range(2)]
    columns = list(zip(*x))
    expected = z3.And(*[z3.And(v >= -2, v <= 2) for row in x for v in row],
                      first_difference(x[0], x[1], op),
                      *[first_difference(a, b, op) for a, b in zip(columns, columns[1:])])
    solver = z3.Solver()
    solver.add(z3.Xor(target(translate(3, op, matrix=True)), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('op', ['lt', 'le', 'gt', 'ge'])
def test_lex_constant_tuple_and_equal_prefix(op):
    x, y = [[z3.Int(f'{name}[{i}]') for i in range(3)] for name in ('x', 'y')]
    expected = z3.And(*[z3.And(v >= -2, v <= 2) for v in x + y],
                      first_difference(x, [0, 1, -1], op))
    solver = z3.Solver()
    solver.add(z3.Xor(target(translate(3, op, right='0 1 -1')), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('operand', ['<list/> <list>y[]</list>',
                                     '<list>x[]</list><list>y[0]</list>',
                                     '<list>x[]</list>'])
def test_lex_rejects_empty_unequal_and_missing_operand(operand):
    result = sp.translate(source='<instance format="XCSP3" type="CSP"><variables>'
                          '<array id="x" size="[2]">0..1</array>'
                          '<array id="y" size="[2]">0..1</array></variables>'
                          '<constraints><lex>' + operand + '<operator>le</operator>'
                          '</lex></constraints></instance>', language='xcsp3')
    assert not result.ok
    assert result.diagnostic_items


def test_lex_output_growth_is_linear_in_tuple_length():
    small, large = translate(96, 'le'), translate(192, 'le')
    assert small.ok and large.ok
    a, b = [v.to_smt2(sp.OmtDialect.Z3) for v in (small, large)]
    assert len(b) < 2.6 * len(a)
