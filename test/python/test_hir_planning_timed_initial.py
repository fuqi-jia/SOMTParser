"""Timed events and stable-goal makespan through the shared public HIR API."""
import pytest
import z3
from somtparser import _somtparser as n


def real(value):
    return n._hir_literal(n.HirSort.real(), str(value))


def boolean(value):
    return n._hir_literal(n.HirSort.boolean(), "true" if value else "false")


def emit(model, constraints, profile):
    for expression in constraints:
        model.constrain(expression)
    assert model.validate() == []
    translated = model.translate(profile=profile, dialect=n.OmtDialect.Z3)
    assert translated.ok, translated.diagnostic_items
    parsed = z3.Optimize()
    parsed.from_string(translated.to_smt2(dialect=n.OmtDialect.Z3))
    assert len(parsed.objectives()) == 0
    return z3.And(*parsed.assertions())


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_all_timed_events_are_mandatory_with_exact_times(profile):
    model = n.HirModel()
    active = [model.declare(f"a{i}", n.HirSort.boolean()) for i in range(2)]
    times = [model.declare(f"t{i}", n.HirSort.real()) for i in range(2)]
    grid = [n.HirTemporalHappening(a, t) for a, t in zip(active, times)]
    events = [n.HirTimedInitialLiteral(real("1/8"), "p", True),
              n.HirTimedInitialLiteral(real(100), "p", False)]
    built = n.planning_timed_initial_literals(grid, events, "til:")
    assert len(built.matches) == 2 and all(len(row) == 2 for row in built.matches)
    assert len(built.accesses) == 4
    assert built.accesses[0].proposition_adds == {"p"}
    assert built.accesses[-1].proposition_deletes == {"p"}
    assert not built.accesses[0].proposition_reads
    constraints = n.planning_temporal_happening_order(grid) + built.constraints
    constraints += n.planning_temporal_interference(built.accesses)
    body = emit(model, constraints, profile)
    equivalent(body, z3.And(z3.Bool("a0"), z3.Bool("a1"),
                           z3.Real("t0") == z3.RealVal("1/8"), z3.Real("t1") == 100))


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_symbolic_stable_goal_makespan_complete_relation(profile):
    model = n.HirModel()
    grid = [n.HirTemporalHappening(boolean(True), real(time)) for time in [2, 5]]
    goals = [model.declare(f"g{i}", n.HirSort.boolean()) for i in range(3)]
    last = model.declare("last", n.HirSort.real())
    span = model.declare("span", n.HirSort.real())
    built = n.planning_stable_goal_makespan(grid, goals, last)
    actual = emit(model, built.constraints + [n._hir_op("eq", [span, built.time])], profile)
    a, b, c = z3.Bools("g0 g1 g2")
    endpoint, objective = z3.Reals("last span")
    # Independent truth-table expansion over all goal samples and last action
    # boundaries; all feasible source valuations retain their exact makespan.
    branches = []
    for mask in range(8):
        values = [bool(mask & (1 << i)) for i in range(3)]
        for last_time in [0, 2, 5]:
            candidates = [time for i, time in enumerate([0, 2, 5])
                          if time >= last_time and all(values[i:])]
            if candidates:
                branches.append(z3.And(a == values[0], b == values[1], c == values[2],
                                       endpoint == last_time, objective == min(candidates)))
    equivalent(actual, z3.Or(*branches))


@pytest.mark.parametrize("time", ["0", "-1/8"])
def test_nonpositive_timed_event_is_an_infeasible_relation(time):
    model = n.HirModel()
    grid = [n.HirTemporalHappening(boolean(True), real(time))]
    built = n.planning_timed_initial_literals(grid, [n.HirTimedInitialLiteral(real(time), "p")])
    equivalent(emit(model, built.constraints, "default"), z3.BoolVal(False))


@pytest.mark.parametrize("bad", ["time", "proposition", "goal-sort", "goal-count", "end-sort"])
def test_timed_initial_api_rejects_type_and_shape_errors(bad):
    with pytest.raises(ValueError):
        if bad in ["time", "proposition"]:
            n.HirTimedInitialLiteral(boolean(True) if bad == "time" else real(1),
                                     "" if bad == "proposition" else "p")
        else:
            n.planning_stable_goal_makespan([], [] if bad == "goal-count" else
                [real(1) if bad == "goal-sort" else boolean(True)],
                boolean(True) if bad == "end-sort" else real(0))
