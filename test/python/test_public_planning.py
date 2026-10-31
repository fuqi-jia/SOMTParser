"""Public imports and explicit composition across planning API families."""
import pytest
import z3
from z3.z3util import get_vars
from somtparser import planning as p
from somtparser import _somtparser as native


def body(model):
    translated = model.translate()
    assert translated.ok, [row.message for row in translated.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(translated.to_smt2()))


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_public_native_exports_preserve_identity():
    helpers = {'literal', 'bound_variable', 'operation'}
    assert len(p.__all__) == len(set(p.__all__))
    for name in set(p.__all__) - helpers:
        assert getattr(p, name) is getattr(native, name)


def test_numeric_temporal_and_timed_events_require_explicit_composition():
    model = p.HirModel()
    real, boolean = p.HirSort.real(), p.HirSort.boolean()
    x0, x1, time = [model.declare(name, real) for name in ['x0', 'x1', 'time']]
    d0, d1, active = [model.declare(name, boolean) for name in ['d0', 'd1', 'active']]
    true = p.literal(boolean, 'true')
    before, after = p.HirNumericStateCell(x0, d0), p.HirNumericStateCell(x1, d1)
    grid = [p.HirTemporalHappening(active, time)]
    initial = model.translate().to_smt2()
    updates = [p.HirNumericUpdate(0, p.NumericUpdateKind.INCREASE,
        p.planning_numeric_constant('1/3'), true, 'action')]
    numeric = p.planning_numeric_transition(model, [before], [after], updates)
    order = p.planning_temporal_happening_order(grid)
    events = p.planning_timed_initial_literals(grid,
        [p.HirTimedInitialLiteral(p.literal(real, '2'), 'event', True)])
    interference = p.planning_temporal_interference(events.accesses)
    assert model.translate().to_smt2() == initial
    for constraint in numeric + order + events.constraints + interference:
        model.constrain(constraint)
    # This relation combines a numeric transition with an event schedule;
    # no proposition state transition or complete PDDL plan is claimed.
    a, b, t = z3.Reals('x0 x1 time')
    da, db, enabled = z3.Bools('d0 d1 active')
    equivalent(body(model), z3.And(da, db, b == a + z3.RealVal('1/3'), enabled, t == 2))


def test_derived_closure_mutates_delta_but_requires_observation_binding():
    model = p.HirModel()
    base, atom = [model.declare(name, p.HirSort.boolean()) for name in ['base', 'atom']]
    before = model.translate().to_smt2()
    closure = p.planning_derived_closure(model, [atom], [(0, base)], 'public_lfp')
    assert model.translate().to_smt2() != before
    # Until explicitly bound, the observation atom is still independent.
    solver = z3.Solver()
    solver.add(body(model), z3.Bool('base'), z3.Not(z3.Bool('atom')))
    assert solver.check() == z3.sat
    model.constrain(p.operation('eq', [atom, closure['values'][0]]))
    actual = body(model)
    auxiliaries = [term for term in get_vars(actual)
                   if str(term) not in {'base', 'atom'}]
    projected = z3.Tactic('qe')(z3.Exists(auxiliaries, actual)).as_expr()
    equivalent(projected, z3.Bool('atom') == z3.Bool('base'))
    snapshot = model.translate().to_smt2()
    with pytest.raises(ValueError):
        p.planning_derived_closure(model, [atom], [(0, p.operation('not', [atom]))], 'invalid_lfp')
    assert model.translate().to_smt2() == snapshot


@pytest.mark.parametrize('bad', ['float', 'bool_as_int', 'free_bound_variable'])
def test_public_helpers_keep_exact_types_and_lexical_scope(bad):
    if bad == 'float':
        with pytest.raises((ValueError, TypeError)):
            p.literal(p.HirSort.real(), 0.1)
    elif bad == 'bool_as_int':
        with pytest.raises((ValueError, TypeError)):
            p.literal(p.HirSort.integer(), 'true')
    else:
        model = p.HirModel()
        unbound = p.bound_variable('missing', p.HirSort.real())
        model.constrain(p.operation('eq', [unbound, p.literal(p.HirSort.real(), '0')]))
        assert not model.translate().ok
