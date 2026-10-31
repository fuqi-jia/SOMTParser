"""Complete temporal relations through the native HIR Python API."""
from pathlib import Path
import json
import os

import pytest
import z3
from somtparser import _somtparser as n


PROFILES = ["default", "ground", "quantified"]
EVIDENCE = Path(os.environ["TEMPORAL_BINDING_EVIDENCE"]) if "TEMPORAL_BINDING_EVIDENCE" in os.environ else None
QUERY = 0


def boolean(value):
    return n._hir_literal(n.HirSort.boolean(), "true" if value else "false")


def real(value):
    return n._hir_literal(n.HirSort.real(), str(value))


def integer(value=1):
    return n._hir_literal(n.HirSort.integer(), str(value))


def variable(model, name, *, bool_sort=False):
    sort = n.HirSort.boolean() if bool_sort else n.HirSort.real()
    return model.declare(name, sort)


def fixed_grid():
    return [n.HirTemporalHappening(boolean(True), real(i)) for i in (1, 2, 3)]


def samples(model, prefix=""):
    start = [variable(model, f"{prefix}p{i}", bool_sort=True) for i in range(3)]
    end = [variable(model, f"{prefix}q{i}", bool_sort=True) for i in range(3)]
    intervals = [variable(model, f"{prefix}r{i}", bool_sort=True) for i in range(2)]
    return n.HirTemporalConditionSamples(start, end, intervals)


def emit(model, constraints=(), profile="default"):
    for expression in constraints:
        model.constrain(expression)
    assert model.validate() == []
    result = model.translate(profile=profile, dialect=n.OmtDialect.Z3)
    assert result.ok, result.diagnostic_items
    text = result.to_smt2(dialect=n.OmtDialect.Z3)
    target = z3.Optimize()
    target.from_string(text)
    assert len(target.objectives()) == 0
    return z3.And(*target.assertions()), text


def check(expected, *conditions, script=None):
    global QUERY
    QUERY += 1
    solver = z3.Solver()
    solver.set(timeout=0)
    solver.add(*conditions)
    actual = solver.check()
    if EVIDENCE is not None:
        EVIDENCE.mkdir(exist_ok=True)
        stem = EVIDENCE / f"temporal-binding-{QUERY:04d}"
        stem.with_suffix(".smt2").write_text(solver.to_smt2())
        stem.with_suffix(".json").write_text(json.dumps(dict(expected=str(expected), actual=str(actual),
            solver_timeout_ms=0, witness=str(solver.model()) if actual == z3.sat else None), indent=2) + "\n")
        if script is not None:
            stem.with_suffix(".target.smt2").write_text(script)
    assert actual == expected


def source_cases(start, end, prefix="", with_samples=True):
    """Source oracle enumerates all six legal endpoint pairs on a three-event trace."""
    rows = []
    for first in range(3):
        for last in range(first, 3):
            clauses = [start == first + 1, end == last + 1]
            if with_samples:
                clauses += [z3.Bool(f"{prefix}p{first}"), z3.Bool(f"{prefix}q{last}")]
                clauses += [z3.Bool(f"{prefix}r{i}") for i in range(first, last)]
            rows.append(z3.And(*clauses))
    return z3.Or(*rows)


@pytest.mark.parametrize("profile", PROFILES)
def test_rational_time_complete_guarded_relation(profile):
    model = n.HirModel()
    time = variable(model, "time")
    active = variable(model, "active", bool_sort=True)
    numerator = model.declare("numerator", n.HirSort.integer())
    denominator = model.declare("denominator", n.HirSort.integer())
    coordinate = n.HirRationalTimeCoordinate(time, numerator, denominator)
    actual, script = emit(model, n.planning_temporal_rational_time(coordinate, active), profile)
    top, bottom = z3.Ints("numerator denominator")
    expected = z3.Implies(z3.Bool("active"), z3.And(bottom > 0, z3.Real("time") * bottom == top))
    check(z3.unsat, z3.Xor(actual, expected), script=script)
    # The integer witnesses remain ordinary typed HIR expressions.
    assert repr(coordinate.time.sort) == "Real"
    assert repr(coordinate.numerator.sort) == repr(coordinate.denominator.sort) == "Int"


@pytest.mark.parametrize("active,time,numerator,denominator,satisfiable", [
    (True, "1/7", 1, 7, True), (True, "1/2", 2, 4, True),
    (True, "-1/7", -1, 7, True), (True, "0", 0, 1, True),
    (True, "1/1208925819614629174706183", 1, 1208925819614629174706183, True),
    (True, "3", 3626777458843887524118549, 1208925819614629174706183, True),
    (True, "1/7", 1, 8, False), (True, "0", 0, 0, False),
    (True, "-1/7", 1, -7, False), (False, "13/5", 0, 0, True),
    (False, "-2", 123, -7, True),
])
def test_rational_time_has_no_precision_bound_or_implicit_positive_time(active, time, numerator, denominator, satisfiable):
    coordinate = n.HirRationalTimeCoordinate(real(time), integer(numerator), integer(denominator))
    body, text = emit(n.HirModel(), n.planning_temporal_rational_time(coordinate, boolean(active)))
    check(z3.sat if satisfiable else z3.unsat, body, script=text)


@pytest.mark.parametrize("field", ["time", "numerator", "denominator", "active", "array_time"])
def test_rational_time_rejects_wrong_scalar_sorts_and_shapes(field):
    model = n.HirModel()
    args = dict(time=real(1), numerator=integer(1), denominator=integer(1))
    active = boolean(True)
    if field == "active":
        active = real(1)
    elif field == "array_time":
        args["time"] = model.declare("times", n.HirSort.array(n.HirSort.integer(), n.HirSort.real()))
    else:
        args[field] = boolean(True) if field == "time" else real(1)
    with pytest.raises(ValueError, match="must have (Bool|Int|Real) sort"):
        coordinate = n.HirRationalTimeCoordinate(**args)
        n.planning_temporal_rational_time(coordinate, active)


@pytest.mark.parametrize("profile", PROFILES)
def test_happening_order_complete_relation_and_unconstrained_inactive_suffix(profile):
    model = n.HirModel()
    active = [variable(model, f"a{i}", bool_sort=True) for i in range(3)]
    time = [variable(model, f"t{i}") for i in range(3)]
    grid = [n.HirTemporalHappening(a, t) for a, t in zip(active, time)]
    actual, script = emit(model, n.planning_temporal_happening_order(grid), profile)
    a = [z3.Bool(f"a{i}") for i in range(3)]
    t = [z3.Real(f"t{i}") for i in range(3)]
    alternatives = []
    for length in range(4):
        clauses = [value == (i < length) for i, value in enumerate(a)]
        clauses += [t[i] > 0 for i in range(length)]
        clauses += [t[i] < t[i + 1] for i in range(length - 1)]
        alternatives.append(z3.And(*clauses))
    check(z3.unsat, z3.Xor(actual, z3.Or(*alternatives)), script=script)
    check(z3.sat, actual, *[z3.Not(value) for value in a], *[value == -7 for value in t])


@pytest.mark.parametrize("profile", PROFILES)
def test_durative_complete_relation_exact_duration_and_zero_duration(profile):
    model = n.HirModel()
    active = variable(model, "active", bool_sort=True)
    start, end, duration = [variable(model, name) for name in ("start", "end", "duration")]
    built = n.planning_temporal_durative_occurrence(fixed_grid(),
        n.HirDurativeOccurrence(active, start, end), samples(model))
    constraints = built.constraints + [n._hir_op("eq", [duration, built.duration])]
    actual, script = emit(model, constraints, profile)
    s, e, d = z3.Reals("start end duration")
    expected = z3.And(d == e - s, z3.Implies(z3.Bool("active"), source_cases(s, e)))
    check(z3.unsat, z3.Xor(actual, expected), script=script)
    check(z3.sat, actual, z3.Bool("active"), s == 2, e == 2,
          z3.Bool("p1"), z3.Bool("q1"), z3.Not(z3.Bool("r1")))
    check(z3.unsat, actual, z3.Bool("active"), s == 3, e == 1)


@pytest.mark.parametrize("profile", PROFILES)
def test_history_guard_is_an_expression_and_does_not_require_its_condition(profile):
    model = n.HirModel()
    active = variable(model, "active", bool_sort=True)
    start, end = variable(model, "start"), variable(model, "end")
    occurrence = n.HirDurativeOccurrence(active, start, end)
    condition = samples(model)
    out = variable(model, "guard", bool_sort=True)
    guard = n.planning_temporal_effect_guard(fixed_grid(), occurrence, condition, n.TemporalEffectEndpoint.END)
    bare = n.planning_temporal_durative_occurrence(fixed_grid(), occurrence)
    actual, script = emit(model, bare.constraints + [n._hir_op("eq", [out, guard])], profile)
    s, e = z3.Reals("start end")
    valid = source_cases(s, e, with_samples=False)
    holds = source_cases(s, e)
    expected = z3.And(z3.Implies(z3.Bool("active"), valid),
        z3.Bool("guard") == z3.And(z3.Bool("active"), holds))
    check(z3.unsat, z3.Xor(actual, expected), script=script)
    check(z3.sat, actual, z3.Bool("active"), s == 1, e == 3,
          z3.Not(z3.Bool("p0")), z3.Not(z3.Bool("guard")))


@pytest.mark.parametrize("profile", PROFILES)
def test_overlapping_occurrences_keep_distinct_start_and_interval_history(profile):
    model = n.HirModel()
    condition = samples(model)
    first = n.HirDurativeOccurrence(boolean(True), real(1), real(3))
    second = n.HirDurativeOccurrence(boolean(True), real(2), real(3))
    constraints = []
    for name, occurrence in [("first", first), ("second", second)]:
        out = variable(model, name, bool_sort=True)
        guard = n.planning_temporal_effect_guard(fixed_grid(), occurrence, condition, n.TemporalEffectEndpoint.END)
        constraints.append(n._hir_op("eq", [out, guard]))
    actual, script = emit(model, constraints, profile)
    p0, p1, q2, r0, r1, first_guard, second_guard = z3.Bools("p0 p1 q2 r0 r1 first second")
    expected = z3.And(first_guard == z3.And(p0, q2, r0, r1), second_guard == z3.And(p1, q2, r1))
    check(z3.unsat, z3.Xor(actual, expected), script=script)
    check(z3.sat, actual, p0, z3.Not(p1), q2, r0, r1, first_guard, z3.Not(second_guard))
    check(z3.sat, actual, p1, q2, z3.Not(r0), r1, z3.Not(first_guard), second_guard)


@pytest.mark.parametrize("owner_a,owner_b,conflict", [("", "", True), ("same", "same", False),
    ("left", "right", True), ("same", "", True), ("", "same", True)])
def test_owner_ids_group_one_endpoint_only(owner_a, owner_b, conflict):
    model = n.HirModel()
    a, b = variable(model, "a", bool_sort=True), variable(model, "b", bool_sort=True)
    t, u = variable(model, "t"), variable(model, "u")
    left = n.HirTemporalEndpointAccess(a, t, proposition_reads={"p(a,b)"}, owner_id=owner_a)
    right = n.HirTemporalEndpointAccess(b, u, proposition_adds={"p(a,b)"}, owner_id=owner_b)
    actual, script = emit(model, n.planning_temporal_interference([left, right]))
    expected = z3.Not(z3.And(z3.Bool("a"), z3.Bool("b"), z3.Real("t") == z3.Real("u"))) if conflict else z3.BoolVal(True)
    check(z3.unsat, z3.Xor(actual, expected), script=script)
    assert left.owner_id == owner_a and right.owner_id == owner_b


@pytest.mark.parametrize("left,right,conflict", [
    ({"proposition_reads": {"p"}}, {"proposition_deletes": {"p"}}, True),
    ({"proposition_adds": {"p"}}, {"proposition_deletes": {"p"}}, True),
    ({"proposition_adds": {"p"}}, {"proposition_adds": {"p"}}, False),
    ({"proposition_deletes": {"p"}}, {"proposition_deletes": {"p"}}, False),
    ({"numeric_reads": {"x"}}, {"numeric_writes": {"x"}, "additive_writes": {"x"}}, True),
    ({"numeric_writes": {"x"}}, {"numeric_writes": {"x"}}, True),
    ({"numeric_writes": {"x"}, "additive_writes": {"x"}}, {"numeric_writes": {"x"}}, True),
    ({"numeric_writes": {"x"}, "additive_writes": {"x"}}, {"numeric_writes": {"x"}, "additive_writes": {"x"}}, False),
    ({"numeric_writes": {"x"}}, {"numeric_writes": {"y"}}, False),
    ({"proposition_reads": {"p(a,b)"}}, {"proposition_adds": {"p(ab)"}}, False),
])
def test_endpoint_access_conflict_relation_in_both_directions(left, right, conflict):
    for reverse in (False, True):
        model = n.HirModel()
        a, b = variable(model, "a", bool_sort=True), variable(model, "b", bool_sort=True)
        t, u = variable(model, "t"), variable(model, "u")
        accesses = [n.HirTemporalEndpointAccess(a, t, **left), n.HirTemporalEndpointAccess(b, u, **right)]
        actual, script = emit(model, n.planning_temporal_interference(accesses[::-1] if reverse else accesses))
        expected = z3.Not(z3.And(z3.Bool("a"), z3.Bool("b"), z3.Real("t") == z3.Real("u"))) if conflict else z3.BoolVal(True)
        check(z3.unsat, z3.Xor(actual, expected), script=script)


@pytest.mark.parametrize("field", ["at_start", "at_end", "over_all"])
@pytest.mark.parametrize("builder", ["occurrence", "guard"])
def test_bad_sample_lengths_raise_before_any_model_append(field, builder):
    model = n.HirModel()
    before = emit(model)[1]
    condition = n.HirTemporalConditionSamples(**{field: [boolean(True)]})
    occurrence = n.HirDurativeOccurrence(boolean(True), real(1), real(3))
    with pytest.raises(ValueError, match="sample count"):
        if builder == "occurrence":
            n.planning_temporal_durative_occurrence(fixed_grid(), occurrence, condition)
        else:
            n.planning_temporal_effect_guard(fixed_grid(), occurrence, condition, n.TemporalEffectEndpoint.END)
    assert emit(model)[1] == before


@pytest.mark.parametrize("future", ["at_end", "over_all"])
def test_start_effect_refuses_future_samples(future):
    count = 3 if future == "at_end" else 2
    condition = n.HirTemporalConditionSamples(**{future: [boolean(True)] * count})
    occurrence = n.HirDurativeOccurrence(boolean(True), real(1), real(3))
    with pytest.raises(ValueError, match="start effect cannot depend"):
        n.planning_temporal_effect_guard(fixed_grid(), occurrence, condition, n.TemporalEffectEndpoint.START)


def test_start_guard_uses_selected_pre_state_and_empty_grid_inactive_occurrence():
    model = n.HirModel()
    condition = n.HirTemporalConditionSamples(at_start=[boolean(False), boolean(True), boolean(False)])
    occurrence = n.HirDurativeOccurrence(boolean(True), real(2), real(3))
    guard = n.planning_temporal_effect_guard(fixed_grid(), occurrence, condition, n.TemporalEffectEndpoint.START)
    body, text = emit(model, [guard])
    check(z3.unsat, z3.Not(body), script=text)
    for active in (False, True):
        occurrence = n.HirDurativeOccurrence(boolean(active), real(0), real(0))
        result = n.planning_temporal_durative_occurrence([], occurrence)
        body, text = emit(n.HirModel(), result.constraints)
        check(z3.sat if not active else z3.unsat, body, script=text)
    assert n.planning_temporal_happening_order([]) == n.planning_temporal_interference([]) == []


@pytest.mark.parametrize("kind,field", [("happening", "active"), ("happening", "time"),
    ("occurrence", "active"), ("occurrence", "start"), ("occurrence", "end"),
    ("sample", "at_start"), ("sample", "at_end"), ("sample", "over_all"),
    ("access", "active"), ("access", "time")])
def test_wrong_expression_sorts_are_explicit_errors(kind, field):
    with pytest.raises(ValueError, match="must have (Bool|Real) sort"):
        if kind == "sample":
            n.HirTemporalConditionSamples(**{field: [integer()]})
        else:
            args = dict(active=boolean(True), **({"start": real(1), "end": real(3)} if kind == "occurrence" else {"time": real(1)}))
            args[field] = integer()
            constructor = {"happening": n.HirTemporalHappening, "occurrence": n.HirDurativeOccurrence,
                           "access": n.HirTemporalEndpointAccess}[kind]
            constructor(**args)


def test_additive_subset_and_python_parameter_types_are_checked():
    with pytest.raises(ValueError, match="subset"):
        n.HirTemporalEndpointAccess(boolean(True), real(1), additive_writes={"x"})
    for bad in (None, True, 1, "1"):
        with pytest.raises(TypeError):
            n.HirTemporalHappening(boolean(True), bad)
    with pytest.raises(TypeError):
        n.HirTemporalEndpointAccess(boolean(True), real(1), owner_id=7)
    with pytest.raises(TypeError):
        n.HirTemporalEndpointAccess(boolean(True), real(1), numeric_reads={7})
    with pytest.raises(TypeError):
        n.planning_temporal_happening_order([None])
    with pytest.raises(TypeError):
        n.planning_temporal_interference([object()])
    with pytest.raises(TypeError):
        n.planning_temporal_effect_guard(fixed_grid(), n.HirDurativeOccurrence(boolean(True), real(1), real(3)),
            n.HirTemporalConditionSamples(), "END")
    with pytest.raises(TypeError):
        n.HirDurativeOccurrence(boolean(True), real(1))
    with pytest.raises(TypeError):
        n.planning_temporal_happening_order([], unexpected=True)
    with pytest.raises(TypeError):
        n.HirRationalTimeCoordinate(real(1), 1, integer(1))


def test_returned_collections_are_copies_and_records_are_read_only():
    condition = n.HirTemporalConditionSamples(at_start=[boolean(True)] * 3)
    condition.at_start.clear()
    assert len(condition.at_start) == 3
    endpoint = n.HirTemporalEndpointAccess(boolean(True), real(1), numeric_reads={"x"}, owner_id="a")
    endpoint.numeric_reads.clear()
    assert endpoint.numeric_reads == {"x"}
    with pytest.raises(AttributeError):
        endpoint.owner_id = "changed"
    result = n.planning_temporal_durative_occurrence(fixed_grid(),
        n.HirDurativeOccurrence(boolean(True), real("1"), real("3")), condition)
    count = len(result.constraints)
    result.constraints.clear()
    assert len(result.constraints) == count and count > 0
    body, text = emit(n.HirModel(), [n._hir_op("eq", [result.duration, real(2)])])
    check(z3.unsat, z3.Not(body), script=text)
