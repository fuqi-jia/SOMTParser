"""Array bin conditions include zero-load bins; uniform conditions do not."""
import pytest
import z3
import somtparser as sp


def translated(variables, sizes, form, scope='x[]', objective=''):
    text = '<instance format="XCSP3" type="' + ('COP' if objective else 'CSP') + '"><variables>' + variables + '</variables><constraints><binPacking><list>' + scope + '</list><sizes>' + sizes + '</sizes>' + form + '</binPacking><intension>ne(x[0],1)</intension></constraints>' + objective + '</instance>'
    result = sp.translate(source=text, language='xcsp3', dialect=sp.OmtDialect.Z3)
    assert result.ok
    target = z3.Optimize()
    target.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    return target


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('form,accepted', [
    ('<loads>3 1</loads>', False),
    ('<loads>3 0</loads>', True),
    ('<limits>3 -1</limits>', False),
    ('<limits>3 0</limits>', True),
])
def test_fixed_empty_bin_is_checked(form, accepted):
    target = translated('<array id="x" size="[2]">0</array>', '1 2', form)
    a, b = z3.Ints('x[0] x[1]')
    equivalent(z3.And(*target.assertions()), z3.And(a == 0, b == 0, accepted))


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_variable_loads_complete_relation_and_signed_cost(direction):
    target = translated('<array id="x" size="[2]">0..1</array><array id="b" size="[2]">0..3</array>', '1 2', '<loads>b[]</loads>',
                        objective='<objectives><' + direction + '>sub(b[1],7)</' + direction + '></objectives>')
    x = [z3.Int('x[%d]' % i) for i in range(2)]
    b = [z3.Int('b[%d]' % i) for i in range(2)]
    expected = z3.And(*[z3.And(a >= 0, a <= 1) for a in x], *[z3.And(a >= 0, a <= 3) for a in b], x[0] != 1,
                      *[b[j] == z3.Sum(*[z3.If(x[i] == j, size, 0) for i, size in enumerate([1, 2])]) for j in range(2)])
    equivalent(z3.And(*target.assertions()), expected)
    assert len(target.objectives()) == 1
    signed = b[1] - 7 if direction == 'minimize' else 7 - b[1]
    cost = z3.Int('observed_binpacking_signed_cost')
    equivalent(z3.And(*target.assertions(), cost == target.objectives()[0]), z3.And(expected, cost == signed))
    negative = z3.Solver()
    negative.add(expected, target.objectives()[0] != -signed)
    assert negative.check() == z3.sat


def test_variable_limits_reject_negative_empty_capacity():
    target = translated('<array id="x" size="[2]">0</array><array id="b" size="[2]">-1..3</array>', '1 2', '<limits>b[]</limits>')
    a, b, c, d = z3.Ints('x[0] x[1] b[0] b[1]')
    equivalent(z3.And(*target.assertions()), z3.And(a == 0, b == 0, c == 3, d >= 0, d <= 3))


@pytest.mark.parametrize('condition', ['(eq,3)', '(ge,3)'])
def test_uniform_condition_only_checks_used_negative_bin(condition):
    target = translated('<array id="x" size="[2]">-2</array>', '1 2', '<condition>' + condition + '</condition>')
    a, b = z3.Ints('x[0] x[1]')
    equivalent(z3.And(*target.assertions()), z3.And(a == -2, b == -2))


def test_repeated_item_coordinate_and_zero_size_preserve_all_contributions():
    target = translated('<array id="x" size="[2]">0..2</array>', '2 3 0', '<loads>5 0 0</loads>', scope='x[0] x[0] x[1]')
    a, b = z3.Ints('x[0] x[1]')
    equivalent(z3.And(*target.assertions()), z3.And(a == 0, b >= 0, b <= 2))
