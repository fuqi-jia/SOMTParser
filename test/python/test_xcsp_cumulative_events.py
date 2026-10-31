"""XCSP integer-time cumulative lowering against an independent time grid."""
import pytest
import z3
import somtparser as sp


def source(origins, lengths, heights, condition, *, variables=None, ends=None,
           objective=None, group=False):
    variables = variables or {name: "-2..2" for name in
                             ("s0", "s1", "d0", "d1", "h0", "h1", "b")}
    declarations = "".join(f'<var id="{name}">{domain}</var>'
                           for name, domain in variables.items())
    cumulative = ("<cumulative><origins>" + " ".join(origins)
                  + "</origins><lengths>" + " ".join(map(str, lengths))
                  + "</lengths><heights>" + " ".join(map(str, heights))
                  + "</heights>" + ("<ends>" + " ".join(ends) + "</ends>" if ends else "")
                  + "<condition>" + condition + "</condition></cumulative>")
    if group:
        cumulative = ("<group>" + cumulative.replace("s0", "%0").replace("s1", "%1")
                      + "<args>s0 s1</args><args>s1 s0</args></group>")
    return (f'<instance format="XCSP3" type="{"COP" if objective else "CSP"}">'
            + "<variables>" + declarations + "</variables><constraints>" + cumulative
            + "</constraints>" + ("<objectives>" + objective + "</objectives>" if objective else "")
            + "</instance>")


def translate(xml):
    result = sp.translate(source=xml, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = result.to_smt2(sp.OmtDialect.Z3)
    assert "(forall " not in target
    assert "integer-time-events" in result.report.to_json()
    return target, result


def compare(condition, value, bound):
    return {"le": lambda: value <= bound, "lt": lambda: value < bound,
            "ge": lambda: value >= bound, "gt": lambda: value > bound,
            "eq": lambda: value == bound, "ne": lambda: value != bound,
            "in_interval": lambda: z3.And(value >= -1, value <= 1),
            "notin_interval": lambda: z3.Or(value < -1, value > 1),
            "in_set": lambda: z3.Or(value == -2, value == 0, value == 2),
            "notin_set": lambda: z3.And(value != -2, value != 0, value != 2),
            "in_empty": lambda: z3.BoolVal(False),
            "notin_empty": lambda: z3.BoolVal(True)}[condition]()


CONDITIONS = [(op, f"({op},b)") for op in ("le", "lt", "ge", "gt", "eq", "ne")] + [
    ("in_interval", "(in,-1..1)"), ("notin_interval", "(notin,-1..1)"),
    ("in_set", "(in,{-2,0,2})"), ("notin_set", "(notin,set(-2,0,2))"),
    ("in_empty", "(in,{})"), ("notin_empty", "(notin,{})")]


@pytest.mark.parametrize("kind,condition", CONDITIONS)
@pytest.mark.parametrize("context", ["positive", "negative", "reified"])
def test_all_conditions_and_boolean_contexts_match_time_grid(kind, condition, context):
    target, _ = translate(source(["s0", "s1"], ["d0", "d1"], ["h0", "h1"], condition))
    terms = {name: z3.Int(name) for name in ("s0", "s1", "d0", "d1", "h0", "h1", "b")}
    actual = z3.And(*z3.parse_smt2_string(target))
    # Starts and durations each range over -2..2. Before -2 and at t>=4
    # every interval is empty; this independent grid covers negative starts,
    # the zero-load tail, and every integer point at which a task can be active.
    expected = z3.And(*[compare(kind, z3.Sum(*[
        z3.If(z3.And(terms[f"s{i}"] <= t, t < terms[f"s{i}"] + terms[f"d{i}"]),
              terms[f"h{i}"], 0) for i in range(2)]), terms["b"])
        for t in range(-2, 5)])
    if context == "negative":
        actual, expected = z3.Not(actual), z3.Not(expected)
    elif context == "reified":
        flag = z3.Bool("flag")
        actual, expected = (flag == actual), (flag == expected)
    solver = z3.Solver()
    solver.add(*[z3.And(value >= -2, value <= 2) for value in terms.values()])
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("starts,lengths,heights,condition,expected", [
    ([-3, -2], [1, 1], [5, 7], "(le,0)", False), # Negative events still constrain.
    ([-1, 2], [2, 0], [3, 7], "(le,2)", False),  # Initial activity at zero.
    ([0, 1], [1, 2], [3, 3], "(le,3)", True),   # Simultaneous start/end.
    ([0, 0], [0, 1], [99, 1], "(le,1)", True),  # Empty zero-duration interval.
    ([0, 0], [-1, 1], [99, 1], "(le,1)", True), # Negative duration stays empty.
    ([0, 0], [3, 1], [3, -3], "(le,0)", False), # Departure raises signed load.
    ([0, 0], [1, 1], [1, 1], "(ge,1)", False),  # Zero-load infinite tail.
    ([-3, -2], [1, 1], [5, 7], "(eq,0)", False),
    ([-3, -2], [2, 2], [1, 1], "(le,1)", False), # Only negative-time overlap.
    ([10**18, 10**18+1], [2, 2], [1, 1], "(le,1)", False), # No fixed horizon.
])
def test_event_boundaries_and_signed_values(starts, lengths, heights, condition, expected):
    variables = {f"s{i}": str(value) for i, value in enumerate(starts)}
    target, _ = translate(source(["s0", "s1"], lengths, heights, condition, variables=variables))
    actual = z3.And(*z3.parse_smt2_string(target))
    solver = z3.Solver(); solver.add(actual)
    assert solver.check() == (z3.sat if expected else z3.unsat)
    # Also compare the complete old all-Int quantified relation, rather than
    # relying only on the finite-grid oracle used by the symbolic controls.
    time = z3.Int("independent_old_time")
    load = z3.Sum(*[z3.If(z3.And(start <= time, time < start + length), height, 0)
                    for start, length, height in zip(starts, lengths, heights)])
    operator, bound = condition[1:-1].split(",")
    old = z3.And(*[z3.Int(f"s{i}") == value for i, value in enumerate(starts)],
                 z3.ForAll([time], compare(operator, load, int(bound))))
    solver = z3.Solver(); solver.add(z3.Xor(actual, old))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("negated", [False, True])
def test_large_shared_load_preserves_signed_events_and_private_symbols(negated):
    repetitions = 32
    variables = {name: "-2..2" for name in ("s0", "s1", "d0", "d1", "h0", "h1", "b")}
    variables["__somt_xcsp_group_0"] = "7"
    variables["__somt_xcsp_group_1_p0"] = "8"
    target, result = translate(source(["s0", "s1"] * repetitions,
        ["d0", "d1"] * repetitions, ["h0", "h1"] * repetitions,
        "(le,b)", variables=variables))
    assert "integer-time-events-shared-load" in result.report.to_json()
    assert "(define-fun " in target
    assert len(target) < 100000
    terms = {name: z3.Int(name) for name in variables}
    actual = z3.And(*z3.parse_smt2_string(target))
    expected = z3.And(*[repetitions * z3.Sum(*[
        z3.If(z3.And(terms[f"s{i}"] <= t, t < terms[f"s{i}"] + terms[f"d{i}"]),
              terms[f"h{i}"], 0) for i in range(2)]) <= terms["b"] for t in range(-2, 5)])
    solver = z3.Solver()
    solver.add(*[z3.And(terms[name] >= -2, terms[name] <= 2)
                 for name in variables if not name.startswith("__")])
    solver.add(terms["__somt_xcsp_group_0"] == 7, terms["__somt_xcsp_group_1_p0"] == 8)
    solver.add(z3.Xor(z3.Not(actual) if negated else actual,
                     z3.Not(expected) if negated else expected))
    assert solver.check() == z3.unsat


def test_optional_ends_and_objective_are_preserved():
    variables = {"s0": "0..3", "s1": "0..3", "e0": "0..5", "e1": "0..5"}
    target, _ = translate(source(["s0", "s1"], [2, 2], [1, 1], "(le,1)",
        variables=variables, ends=["e0", "e1"], objective="<minimize type=\"sum\"><list>e0 e1</list></minimize>"))
    optimizer = z3.Optimize(); optimizer.from_string(target)
    assert optimizer.check() == z3.sat
    model = optimizer.model(); e0, e1, s0, s1 = z3.Ints("e0 e1 s0 s1")
    assert model.eval(e0 + e1).as_long() == 6
    assert model.eval(e0 == s0 + 2) == z3.BoolVal(True)
    assert model.eval(e1 == s1 + 2) == z3.BoolVal(True)


def test_group_arguments_do_not_share_task_values():
    variables = {"s0": "0..2", "s1": "0..2"}
    target, _ = translate(source(["s0", "s1"], [1, 2], [1, 1], "(le,1)",
                                variables=variables, group=True))
    s0, s1 = z3.Ints("s0 s1")
    actual = z3.And(*z3.parse_smt2_string(target))
    expected = z3.And(z3.Or(s0+1 <= s1, s1+2 <= s0),
                      z3.Or(s1+1 <= s0, s0+2 <= s1))
    solver = z3.Solver(); solver.add(s0 >= 0, s0 <= 2, s1 >= 0, s1 <= 2,
                                   z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_empty_xcsp_task_list_keeps_existing_shape_rejection():
    result = sp.translate(source=source([], [], [], "(le,0)", variables={"x": "0"}), language="xcsp3")
    assert not result.ok
