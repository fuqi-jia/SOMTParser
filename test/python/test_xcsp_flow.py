"""Exact network-flow conservation, capacities and joint signed cost."""
import pytest
import z3
import somtparser as sp


def document(flow, variables=None, objective=''):
    if variables is None:
        variables = '<array id="x" size="[2]">-3..3</array>'
    return ('<instance format="XCSP3" type="' + ('COP' if objective else 'CSP') + '">'
            '<variables>' + variables + '</variables><constraints>' + flow +
            '</constraints>' + objective + '</instance>')


def flow(arcs, balance, *, scope='x[]', extra='', attributes=''):
    return (f'<flow {attributes}><list>{scope}</list><balance>{balance}</balance>'
            f'<arcs>{arcs}</arcs>{extra}</flow>')


def translate(text):
    result = sp.translate(source=text, language='xcsp3', dialect=sp.OmtDialect.Z3)
    assert result.ok, result.report
    target = z3.Optimize()
    target.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    return target


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def domain(*variables, lower=-3, upper=3):
    return z3.And(*[z3.And(v >= lower, v <= upper) for v in variables])


@pytest.mark.parametrize('start', [0, 1, -2, 9223372036854775806])
def test_outgoing_minus_incoming_parallel_arcs_and_nonzero_node_origin(start):
    target = translate(document(flow(f'({start},{start+1})({start},{start+1})', '2 -2')))
    x, y = z3.Ints('x[0] x[1]')
    equivalent(z3.And(*target.assertions()), z3.And(domain(x, y), x + y == 2))
    # No positivity restriction is invented: a negative arc is valid when its
    # source domain and all explicitly supplied capacities allow it.
    solver = z3.Solver(); solver.add(*target.assertions(), x == -1, y == 3)
    assert solver.check() == z3.sat


def test_self_loop_and_repeated_source_coordinate_keep_arc_multiplicity():
    target = translate(document(flow('(0,0)(0,1)(1,0)', '1 -1', scope='x[0] x[1] x[0]',
                                    extra='<weights>2 3 5</weights><condition>(eq,10)</condition>')))
    x, y = z3.Ints('x[0] x[1]')
    equivalent(z3.And(*target.assertions()), z3.And(domain(x, y), y-x == 1, 7*x+3*y == 10))


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_variable_balances_weights_and_exact_signed_objective(direction):
    variables = ('<array id="x" size="[2]">-3..3</array>'
                 '<array id="b" size="[2]">-3..3</array>'
                 '<array id="w" size="[2]">-3..3</array><var id="z">-20..20</var>')
    text = document(flow('(1,2)(2,1)', 'b[]',
                         extra='<weights>w[]</weights><condition>(eq,z)</condition>'), variables,
                    f'<objectives><{direction}>z</{direction}></objectives>')
    target = translate(text)
    x, y, b, c, u, v, z = z3.Ints('x[0] x[1] b[0] b[1] w[0] w[1] z')
    expected = z3.And(domain(x,y,b,c,u,v), domain(z, lower=-20, upper=20),
                      x-y == b, y-x == c, z == x*u+y*v)
    signed = z if direction == 'minimize' else -z
    cost = z3.Int('observed_flow_cost')
    assert len(target.objectives()) == 1
    equivalent(z3.And(*target.assertions(), cost == target.objectives()[0]),
               z3.And(expected, cost == signed))


@pytest.mark.parametrize('capacities, bounds', [
    ('-2..1 -1..2', [(-2,1),(-1,2)]),
    ('-2..2x2', [(-2,2),(-2,2)]),
])
def test_capacities_include_both_signed_endpoints(capacities, bounds):
    target = translate(document(flow('(0,1)(1,0)', '0x2',
                                    extra='<capacities>' + capacities + '</capacities>')))
    xs = z3.Ints('x[0] x[1]')
    expected = z3.And(domain(*xs), xs[0] == xs[1],
                      *[z3.And(x >= lo, x <= hi) for x,(lo,hi) in zip(xs,bounds)])
    equivalent(z3.And(*target.assertions()), expected)


@pytest.mark.parametrize('operator', ['eq','ne','lt','le','gt','ge','in','notin'])
def test_weighted_cost_uses_the_complete_condition_api(operator):
    operand = '-1..1' if operator in ['in','notin'] else '0'
    target = translate(document(flow('(0,1)(1,0)', '0x2',
        extra=f'<weights>2 -3</weights><condition>({operator},{operand})</condition>')))
    x, y = z3.Ints('x[0] x[1]'); cost = 2*x-3*y
    conditions = dict(eq=cost==0, ne=cost!=0, lt=cost<0, le=cost<=0, gt=cost>0, ge=cost>=0,
                      **{'in':z3.And(cost>=-1,cost<=1), 'notin':z3.Or(cost<-1,cost>1)})
    equivalent(z3.And(*target.assertions()), z3.And(domain(x,y),x==y,conditions[operator]))


def test_flow_inside_group_uses_each_call_independently():
    body = ('<group><flow><list>%0 %1</list><balance>1 -1</balance>'
            '<arcs>(0,1)(1,0)</arcs></flow><args>x[0] x[1]</args>'
            '<args>x[1] x[0]</args></group>')
    target = translate(document(body))
    equivalent(z3.And(*target.assertions()), z3.BoolVal(False))


@pytest.mark.parametrize('body', [
    flow('(0,1)(1,0)', '0x2', extra='<weights>1 2</weights>'),
    flow('(0,1)(1,0)', '0x2', extra='<condition>(eq,1)</condition>'),
    flow('(0,1)(1,0)', '0'),
    flow('(0,1)(1,0)', '0x2', extra='<weights>1</weights><condition>(eq,0)</condition>'),
    flow('(0,1)(1,0)', '0x2', extra='<capacities>0..1</capacities>'),
    flow('(0,1)(1,0)', '0x2', extra='<capacities>2..1 0..1</capacities>'),
    flow('(0,1)(1,0)', '0x2', extra='<capacities>0..1x3</capacities>'),
    flow('(0,x[0])(1,0)', '0x2'),
    flow('(0,1,2)(1,0,2)', '0x3'),
    flow('(0,2)(2,0)', '0x2'),
    flow('(0,1)(1,0)', '0x2', extra='<balance>0x2</balance>'),
    flow('(0,1)(1,0)', '0x2', attributes='reifiedBy="x[0]"'),
])
def test_incomplete_or_ambiguous_flow_is_not_silently_weakened(body):
    result = sp.translate(source=document(body), language='xcsp3', dialect=sp.OmtDialect.Z3)
    assert not result.ok
