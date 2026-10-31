"""Public object APIs checked against independently written complete relations."""
import pytest
import z3
from somtparser import planning as p


def universe():
    return p.HirObjectUniverse([], [p.HirPlanningObject('a', 'object'),
                                    p.HirPlanningObject('b', 'object')])


def fixture(names=('x', 'y')):
    model = p.HirModel()
    typ = p.HirObjectType(['object'])
    def cell(name):
        return p.HirObjectStateCell(model.declare(name, p.HirSort.integer()),
                                   model.declare(name + 'd', p.HirSort.boolean()), typ)
    return model, universe(), [cell(name) for name in names], [cell('n' + name) for name in names]


def body(model):
    result = model.translate()
    assert result.ok, [row.message for row in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def exact(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def attach(model, constraints):
    for constraint in constraints:
        model.constrain(constraint)


def domain(name):
    value, defined = z3.Int(name), z3.Bool(name + 'd')
    return z3.If(defined, z3.Or(value == 1, value == 2), value == 0)


def address(model, u, index):
    return p.planning_object_address(model, u, p.HirObjectTable([], [[]]), [], [index])


def transition(model, u, before, after, updates, policy=p.ObjectAssignmentPolicy.SINGLE_WRITER):
    old = model.translate().to_smt2()
    constraints = p.planning_object_transition(model, u, before, after, updates, policy)
    assert model.translate().to_smt2() == old
    attach(model, constraints)
    return body(model)


def test_simultaneous_swap_and_inactive_undefined_frame():
    model, u, before, after = fixture()
    enabled = model.declare('enabled', p.HirSort.boolean())
    reads = [p.planning_object_read(u, cell, i) for i, cell in enumerate(before)]
    updates = [p.HirObjectUpdate(address(model, u, i), reads[1 - i], enabled) for i in range(2)]
    actual = transition(model, u, before, after, updates)
    x, y, nx, ny = z3.Ints('x y nx ny')
    xd, yd, nxd, nyd, e = z3.Bools('xd yd nxd nyd enabled')
    expected = z3.And(domain('x'), domain('y'), z3.Implies(e, z3.And(xd, yd)),
                      nx == z3.If(e, y, x), ny == z3.If(e, x, y),
                      nxd == z3.If(e, True, xd), nyd == z3.If(e, True, yd))
    exact(actual, expected)
    # A sequential implementation would lose the original x in this case.
    witness = z3.Solver()
    witness.add(actual, e, x == 1, y == 2, ny == 1)
    assert witness.check() == z3.sat


def test_dynamic_target_is_resolved_in_old_state():
    names = ('ptr', 'x', 'y', 'rhs')
    model, u, before, after = fixture(names)
    enabled = model.declare('enabled', p.HirSort.boolean())
    reads = [p.planning_object_read(u, cell, i) for i, cell in enumerate(before)]
    table = p.HirObjectTable([p.HirObjectType(['object'])], [[0], [1]])
    target = p.planning_object_address(model, u, table, [reads[0]], [1, 2])
    actual = transition(model, u, before, after, [p.HirObjectUpdate(target, reads[3], enabled)])
    e, pd, rd = z3.Bools('enabled ptrd rhsd')
    pointer, rhs = z3.Ints('ptr rhs')
    expected = [domain(name) for name in names]
    expected.append(z3.Implies(e, z3.And(pd, rd)))
    for i, name in enumerate(names):
        writes = z3.And(e, pointer == i) if i in (1, 2) else z3.BoolVal(False)
        expected += [z3.Int('n' + name) == z3.If(writes, rhs, z3.Int(name)),
                     z3.Bool('n' + name + 'd') == z3.If(writes, True, z3.Bool(name + 'd'))]
    exact(actual, z3.And(*expected))
    assert [read.cell for read in target.reads] == [0]


def test_nested_lookup_keeps_guarded_read_dependencies():
    model, u, before, _ = fixture(('ptr', 'x', 'y'))
    reads = [p.planning_object_read(u, cell, i) for i, cell in enumerate(before)]
    typ = p.HirObjectType(['object'])
    table = p.HirObjectTable([typ], [[1], [0]])  # Row order is immaterial.
    first = p.planning_object_lookup(model, u, table, [reads[0]], [reads[2], reads[1]], typ)
    second = p.planning_object_lookup(model, u, table, [first],
        [p.planning_object_constant(u, 'a'), p.planning_object_constant(u, 'b')], typ)
    value = model.declare('out', p.HirSort.integer())
    defined = model.declare('outd', p.HirSort.boolean())
    attach(model, second.constraints)
    model.constrain(p.operation('eq', [value, second.value]))
    model.constrain(p.operation('eq', [defined, second.defined]))
    ptr, x, y, out = z3.Ints('ptr x y out')
    pd, xd, yd, od = z3.Bools('ptrd xd yd outd')
    selected_defined = z3.And(pd, z3.If(ptr == 1, xd, yd))
    selected_value = z3.If(ptr == 1, x, y)
    exact(body(model), z3.And(domain('ptr'), domain('x'), domain('y'), od == selected_defined,
        out == z3.If(selected_defined, z3.If(selected_value == 1, 2, 1), 0)))
    assert {read.cell for read in second.reads} == {0, 1, 2}


def test_explicit_undefined_assignment_does_not_require_old_definedness():
    model, u, before, after = fixture(('x',))
    enabled = model.declare('enabled', p.HirSort.boolean())
    actual = transition(model, u, before, after, [p.HirObjectUpdate(address(model, u, 0), None, enabled)])
    x, nx = z3.Ints('x nx')
    xd, nxd, e = z3.Bools('xd nxd enabled')
    exact(actual, z3.And(domain('x'), nx == z3.If(e, 0, x), nxd == z3.And(xd, z3.Not(e))))


@pytest.mark.parametrize('agreeing,same', [(False, True), (True, True), (True, False)])
def test_duplicate_writes_obey_explicit_policy(agreeing, same):
    model, u, before, after = fixture(('x',))
    a, b = [model.declare(name, p.HirSort.boolean()) for name in ('a_on', 'b_on')]
    target = address(model, u, 0)
    updates = [p.HirObjectUpdate(target, p.planning_object_constant(u, 'a'), a),
               p.HirObjectUpdate(target, p.planning_object_constant(u, 'a' if same else 'b'), b)]
    policy = p.ObjectAssignmentPolicy.AGREEING_WRITERS if agreeing else p.ObjectAssignmentPolicy.SINGLE_WRITER
    actual = transition(model, u, before, after, updates, policy)
    a, b, xd, nxd = z3.Bools('a_on b_on xd nxd')
    x, nx = z3.Ints('x nx')
    exact(actual, z3.And(domain('x'), nxd == z3.Or(a, b, xd),
        nx == z3.If(b, 1 if same else 2, z3.If(a, 1, x)),
        z3.BoolVal(True) if agreeing and same else z3.Not(z3.And(a, b))))


@pytest.mark.parametrize('strict', [True, False])
def test_undefined_equality_then_negation_requires_explicit_semantics(strict):
    model, u, before, _ = fixture(('x',))
    lhs = p.planning_object_read(u, before[0], 0)
    policy = p.ObjectUndefinedPolicy.STRICT if strict else p.ObjectUndefinedPolicy.ATOMIC_FALSE
    atom = p.planning_object_equal(u, lhs, p.planning_object_constant(u, 'a'), policy)
    negated = p.planning_object_logical('not', [atom])
    accepted = model.declare('accepted', p.HirSort.boolean())
    attach(model, negated.constraints)
    model.constrain(p.operation('eq', [accepted, p.planning_object_satisfied(negated)]))
    x, xd, yes = z3.Int('x'), z3.Bool('xd'), z3.Bool('accepted')
    expected = z3.And(xd, x != 1) if strict else z3.Not(z3.And(xd, x == 1))
    exact(body(model), z3.And(domain('x'), yes == expected))


def test_numeric_lookup_preserves_separate_guarded_namespaces():
    model, u, before, _ = fixture(('ptr',))
    pointer = p.planning_object_read(u, before[0], 0)
    rows = [p.HirNumericStateCell(model.declare(name, p.HirSort.real()),
                                model.declare(name + 'd', p.HirSort.boolean())) for name in ('x', 'y')]
    table = p.HirObjectTable([p.HirObjectType(['object'])], [[0], [1]])
    result = p.planning_object_numeric_lookup(model, u, table, [pointer],
        [p.planning_numeric_read(cell, i) for i, cell in enumerate(rows)])
    assert [read.cell for read in result.object_reads] == [0]
    assert [read.cell for read in result.numeric_reads] == [0, 1]
    assert result.numeric.reads == [0, 1]
    out = model.declare('out', p.HirSort.real())
    defined = model.declare('outd', p.HirSort.boolean())
    attach(model, result.constraints)
    model.constrain(p.operation('eq', [out, result.numeric.value]))
    model.constrain(p.operation('eq', [defined, result.numeric.defined]))
    for i, read in enumerate(result.numeric_reads):
        marker = model.declare('read' + str(i), p.HirSort.boolean())
        model.constrain(p.operation('eq', [marker, read.when]))
    ptr = z3.Int('ptr')
    x, y, out = z3.Reals('x y out')
    pd, xd, yd, od, r0, r1 = z3.Bools('ptrd xd yd outd read0 read1')
    is_defined = z3.And(pd, z3.If(ptr == 1, xd, yd))
    exact(body(model), z3.And(domain('ptr'), od == is_defined,
        out == z3.If(is_defined, z3.If(ptr == 1, x, y), 0),
        r0 == z3.And(pd, ptr == 1), r1 == z3.And(pd, ptr == 2)))


def test_initial_state_defaults_to_undefined_without_mutating_context():
    model, u, before, _ = fixture()
    snapshot = model.translate().to_smt2()
    constraints = p.planning_object_initial_state(model, u, before, [(1, 0)])
    assert model.translate().to_smt2() == snapshot
    attach(model, constraints)
    exact(body(model), z3.And(z3.Int('x') == 0, z3.Not(z3.Bool('xd')),
                              z3.Int('y') == 1, z3.Bool('yd')))


def test_action_precondition_object_update_and_exact_cost_compose():
    model, u, before, after = fixture(('x',))
    enabled = model.declare('enabled', p.HirSort.boolean())
    cells = [p.HirNumericStateCell(model.declare(name, p.HirSort.real()),
                                  model.declare(name + 'd', p.HirSort.boolean()))
             for name in ('cost', 'ncost')]
    condition = p.planning_object_equal(u, p.planning_object_read(u, before[0], 0),
        p.planning_object_constant(u, 'a'), p.ObjectUndefinedPolicy.STRICT)
    attach(model, condition.constraints)
    model.constrain(p.operation('implies', [enabled, p.planning_object_satisfied(condition)]))
    attach(model, p.planning_numeric_transition(model, [cells[0]], [cells[1]],
        [p.HirNumericUpdate(0, p.NumericUpdateKind.INCREASE,
                            p.planning_numeric_constant('1/3'), enabled, 'move')]))
    actual = transition(model, u, before, after,
        [p.HirObjectUpdate(address(model, u, 0), p.planning_object_constant(u, 'b'), enabled)])
    x, nx = z3.Ints('x nx')
    cost, ncost = z3.Reals('cost ncost')
    xd, nxd, cd, ncd, e = z3.Bools('xd nxd costd ncostd enabled')
    exact(actual, z3.And(domain('x'), z3.Implies(z3.Not(cd), cost == 0),
        z3.Implies(e, z3.And(xd, x == 1, cd)),
        nx == z3.If(e, 2, x), nxd == z3.Or(e, xd), ncd == cd,
        ncost == z3.If(cd, cost + z3.If(e, z3.RealVal('1/3'), 0), 0)))


def test_union_subtyping_is_nominal_even_with_empty_carriers():
    u = p.HirObjectUniverse([p.HirObjectTypeDeclaration('vehicle', []),
                            p.HirObjectTypeDeclaration('truck', ['vehicle']),
                            p.HirObjectTypeDeclaration('location', [])], [])
    assert p.planning_object_subtype(u, p.HirObjectType(['truck', 'location']),
                                     p.HirObjectType(['vehicle', 'location']))
    assert not p.planning_object_subtype(u, p.HirObjectType(['location']), p.HirObjectType(['vehicle']))
    assert p.planning_object_carrier(u, p.HirObjectType(['truck', 'location'])) == []


@pytest.mark.parametrize('bad', ['missing_row', 'duplicate_row', 'wrong_object', 'wrong_arity',
                                'duplicate_init', 'unknown_constant', 'future_rhs'])
def test_invalid_construction_preserves_model(bad):
    model, u, before, after = fixture(('x',))
    snapshot = model.translate().to_smt2()
    with pytest.raises(ValueError):
        if bad == 'duplicate_init':
            p.planning_object_initial_state(model, u, before, [(0, 0), (0, 1)])
        elif bad == 'unknown_constant':
            p.planning_object_constant(u, 'undefined')
        elif bad == 'future_rhs':
            rhs = p.planning_object_read(u, after[0], 0)
            update = p.HirObjectUpdate(address(model, u, 0), rhs, p.literal(p.HirSort.boolean(), 'true'))
            p.planning_object_transition(model, u, before, after, [update], p.ObjectAssignmentPolicy.SINGLE_WRITER)
        else:
            rows = {'missing_row': [[0]], 'duplicate_row': [[0], [0], [1]],
                    'wrong_object': [[0], [2]], 'wrong_arity': [[0, 1], [1]]}[bad]
            table = p.HirObjectTable([p.HirObjectType(['object'])], rows)
            p.planning_object_dispatch(model, u, table, [p.planning_object_read(u, before[0], 0)])
    assert model.translate().to_smt2() == snapshot
