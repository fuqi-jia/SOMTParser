"""Native OMT snapshot export: ordered costs, solver behavior and reimport.

Run against the newly built runtime on the experiment server. These regressions
intentionally fail against the frozen runtime that omitted arithmetic goals.
dump_smt2 is a current-state snapshot, not a replay of historical queries/scopes.
"""
import re

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("goals", [
    "(minimize x)",
    "(minimize x)(maximize y)",
    "(assert-soft p :weight 3 :id first)(minimize x)"
    "(assert-soft (not p) :weight 1 :id first)(maximize y)",
])
def test_gomt_output_reimports_and_preserves_ordered_costs(goals):
    source = ("(set-option :opt.priority lex)"
              "(declare-const x Int)(declare-const y Int)(declare-const p Bool)"
              "(assert (and (<= 0 x) (<= x 4) (= y (- 4 x))))"
              + goals + "(check-sat)(get-objectives)")
    parser = sp.parse(source)
    output = parser.dump_smt2(dialect=sp.OmtDialect.Gomt)
    assert "(set-option :enable-omt true)" in output
    assert output.count("(optimize-sat ") == 1
    assert "(check-sat)" not in output
    assert "(get-objectives)" not in output
    assert "(get-value (" in output
    restored = sp.parse(output)
    vendor = restored.dump_smt2(dialect=sp.OmtDialect.Z3)
    assert_same_problem(source, vendor)
    assert optimum_values(load_optimizer(source), z3.Int("x"), z3.Int("y")) == \
        optimum_values(load_optimizer(vendor), z3.Int("x"), z3.Int("y"))


@pytest.mark.parametrize("dialect", [sp.OmtDialect.Z3, sp.OmtDialect.OptiMathSAT, sp.OmtDialect.Gomt])
def test_translation_retains_objective_response_in_each_dialect(tmp_path, dialect):
    source = "(declare-const x Int)(assert (>= x 2))(minimize x)(check-sat)(get-objectives)"
    path = tmp_path / "goal.smt2"
    path.write_text(source)
    result = sp.translate(path=str(path), language="smtlib2", dialect=dialect)
    assert result.ok, result.diagnostic_items
    output = result.to_smt2(dialect)
    if dialect == sp.OmtDialect.Gomt:
        assert output.count("(optimize-sat ") == 1
        assert "(check-sat)" not in output
        assert "(get-value (" in output
    else:
        assert output.count("(check-sat)") == 1
        assert "(get-objectives)" in output
        if dialect == sp.OmtDialect.OptiMathSAT:
            assert output.count("(set-option :produce-models true)") == 1
            assert output.index("(set-option :produce-models true)") < output.index("(declare-")
    restored = sp.parse(output)
    assert_same_problem(source, restored.dump_smt2(dialect=sp.OmtDialect.Z3))


def load_optimizer(text):
    optimizer = z3.Optimize()
    optimizer.set(timeout=10000)
    optimizer.from_string(text)
    return optimizer


def assert_unsat(formula):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(formula)
    assert solver.check() == z3.unsat, solver.reason_unknown()


def assert_same_problem(source, output):
    """Compare the complete hard relation and ordered, signed cost functions.

    Checking only SAT or the final optimum could miss a reversed goal, a changed
    soft weight, or an objective permutation with the same attainable optimum.
    Optimize.objectives() represents maximize as a negated minimization cost.
    """
    original, exported = load_optimizer(source), load_optimizer(output)
    assert_unsat(z3.Xor(z3.And(*original.assertions()), z3.And(*exported.assertions())))
    old_costs, new_costs = original.objectives(), exported.objectives()
    assert len(old_costs) == len(new_costs)
    for before, after in zip(old_costs, new_costs):
        assert_unsat(before != after)
    return original, exported


def directions(parser):
    return [(objective.is_minimize, objective.is_maximize) for objective in parser.objectives]


def snapshot(source):
    parser = sp.parse(source)
    output = parser.dump_smt2()
    reread = sp.parse(output)
    assert len(reread.objectives) == len(parser.objectives)
    assert directions(reread) == directions(parser)
    assert len(reread.soft_assertions) == len(parser.soft_assertions)
    assert_same_problem(source, output)
    return parser, output, reread


def optimum_values(optimizer, *variables):
    assert optimizer.check() == z3.sat, optimizer.reason_unknown()
    return tuple(optimizer.model().eval(variable, model_completion=True).as_long() for variable in variables)


@pytest.mark.parametrize("direction,expected", [("minimize", 0), ("maximize", 7)])
def test_single_goal_direction_and_optimum_survive_two_exports(direction, expected):
    source = f"""
    (set-logic QF_LIA)
    (declare-const x Int)
    (assert (and (<= 0 x) (<= x 7)))
    ({direction} x)
    (check-sat)(get-objectives)
    """
    parser, first, reread = snapshot(source)
    assert len(parser.objectives) == 1
    assert directions(reread) == [(direction == "minimize", direction == "maximize")]
    second = reread.dump_smt2()
    for text in (source, first, second):
        assert optimum_values(load_optimizer(text), z3.Int("x")) == (expected,)
    assert_same_problem(first, second)


@pytest.mark.parametrize("goals,expected", [
    ("(minimize x)(minimize y)", (0, 4)),
    ("(minimize y)(minimize x)", (4, 0)),
])
def test_lexicographic_goal_order_changes_the_optimum_and_is_preserved(goals, expected):
    source = f"""
    (set-option :opt.priority lex)
    (declare-const x Int)(declare-const y Int)
    (assert (and (>= x 0) (>= y 0) (= (+ x y) 4)))
    {goals}(check-sat)(get-objectives)
    """
    _, output, reread = snapshot(source)
    assert directions(reread) == [(True, False), (True, False)]
    for text in (source, output):
        assert optimum_values(load_optimizer(text), *z3.Ints("x y")) == expected


@pytest.mark.parametrize("soft_first,expected", [(False, 0), (True, 1)])
def test_soft_and_minimize_interleaving_preserves_lexicographic_priority(soft_first, expected):
    soft = "(assert-soft (not p) :weight 9 :id preference)"
    arithmetic = "(minimize x)"
    ordered = soft + arithmetic if soft_first else arithmetic + soft
    source = f"""
    (set-option :opt.priority lex)
    (declare-const x Int)(declare-const p Bool)
    (assert (and (>= x 0) (<= x 5) (= p (= x 0))))
    {ordered}(check-sat)(get-objectives)
    """
    _, output, reread = snapshot(source)
    assert len(reread.objectives) == len(reread.soft_assertions) == 1
    for text in (source, output):
        assert optimum_values(load_optimizer(text), z3.Int("x")) == (expected,)


def test_later_member_of_a_soft_group_keeps_its_first_objective_position():
    source = """
    (set-option :opt.priority lex)
    (declare-const x Int)(declare-const y Int)
    (declare-const p Bool)(declare-const q Bool)
    (assert (and (>= x 0) (<= x 3) (>= y 0) (<= y 3)
                 (= p (= x 0)) (= q (= y 0))))
    (assert-soft p :weight 9 :id first)
    (minimize x)
    (assert-soft q :weight 5 :id second)
    (maximize y)
    (assert-soft (not q) :weight 2 :id first)
    (check-sat)(get-objectives)
    """
    _, output, reread = snapshot(source)
    original, exported = assert_same_problem(source, output)
    assert len(original.objectives()) == len(exported.objectives()) == 4
    assert directions(reread) == [(True, False), (False, True)]
    assert len(reread.soft_assertions) == 3
    for optimizer in (original, exported):
        assert optimum_values(optimizer, *z3.Ints("x y")) == (0, 3)


@pytest.mark.parametrize("left_weight,right_weight", [
    ("9", "4"), ("9007199254740993", "9007199254740992"), ("3.5", "0.5"),
])
def test_same_group_weights_remain_one_exact_cost(left_weight, right_weight):
    source = f"""
    (declare-const p Bool)
    (assert-soft p :weight {left_weight} :id same)
    (assert-soft (not p) :weight {right_weight} :id same)
    (check-sat)(get-objectives)
    """
    _, output, reread = snapshot(source)
    assert len(reread.soft_assertions) == 2
    assert set(reread.grouped_soft_assertions) == {"same"}
    for text in (source, output):
        optimizer = load_optimizer(text)
        assert len(optimizer.objectives()) == 1
        assert optimizer.check() == z3.sat, optimizer.reason_unknown()
        assert z3.is_true(optimizer.model().eval(z3.Bool("p")))
        cost = optimizer.model().eval(optimizer.objectives()[0])
        assert z3.is_true(z3.simplify(cost == z3.RealVal(right_weight)))


def priority_source(priority):
    return f"""
    (set-option :opt.priority {priority})
    (declare-const x Int)(declare-const y Int)
    (assert (and (>= x 0) (>= y 0) (= (+ x y) 4)))
    (minimize x)(minimize y)(check-sat)(get-objectives)
    """


def pareto_front(text):
    optimizer = load_optimizer(text)
    points = set()
    for _ in range(10):
        status = optimizer.check()
        if status == z3.unsat:
            return points
        assert status == z3.sat, optimizer.reason_unknown()
        point = tuple(optimizer.model().eval(value).as_long() for value in z3.Ints("x y"))
        assert point not in points, "priority must remain pareto, not repeat a lexicographic optimum"
        points.add(point)
    pytest.fail("finite Pareto front did not terminate")


def test_pareto_option_preserves_the_complete_finite_front():
    source = priority_source("pareto")
    _, output, reread = snapshot(source)
    expected = {(value, 4 - value) for value in range(5)}
    for text in (source, output, reread.dump_smt2()):
        assert pareto_front(text) == expected


def test_box_option_preserves_independent_objective_bounds():
    source = priority_source("box")
    _, output, reread = snapshot(source)
    for text in (source, output, reread.dump_smt2()):
        optimizer = load_optimizer(text)
        assert optimizer.check() == z3.sat, optimizer.reason_unknown()
        # These goals are both minimize. Their handles are reconstructed in the
        # source order after Optimize.from_string, which does not return handles.
        bounds = [z3.OptimizeObjective(optimizer, index, False) for index in range(2)]
        assert [bound.lower().as_long() for bound in bounds] == [0, 0]
        assert [bound.upper().as_long() for bound in bounds] == [0, 0]


@pytest.mark.parametrize("logging", [False, True])
def test_terminal_get_objectives_stays_after_check_and_before_exit(logging):
    source = """
    (declare-const x Int)(assert (and (>= x 0) (<= x 3)))
    (minimize x)(check-sat)(get-objectives)(exit)
    """
    parser = sp.Parser()
    parser.set_command_logging(logging)
    parser.parse_string(source)
    for _ in range(2):
        output = parser.dump_smt2()
        commands = re.findall(r"\(\s*(check-sat|get-objectives|exit)\b", output)
        assert commands == ["check-sat", "get-objectives", "exit"]
        assert output.index("(minimize") < output.index("(check-sat")
        assert_same_problem(source, output)
        parser = sp.parse(output)


def test_file_dump_matches_string_dump_and_can_be_reimported(tmp_path):
    source = """
    (declare-const x Int)(declare-const p Bool)
    (assert (and (>= x 0) (<= x 3) (= p (= x 0))))
    (maximize x)(assert-soft p :weight 7 :id preference)
    (check-sat)(get-objectives)
    """
    parser, output, _ = snapshot(source)
    destination = tmp_path / "native-omt.smt2"
    assert parser.dump_smt2(str(destination)) == str(destination)
    assert destination.read_text() == output
    reread = sp.parse_file(str(destination))
    assert directions(reread) == [(False, True)]
    assert len(reread.soft_assertions) == 1
    assert_same_problem(source, reread.dump_smt2())


def test_popped_goals_and_soft_preferences_are_not_resurrected():
    source = """
    (declare-const x Int)(declare-const y Int)
    (assert (and (>= x 0) (<= x 3) (>= y 0) (<= y 3)))
    (minimize x)
    (push 1)
    (maximize y)
    (assert-soft (= y 3) :weight 99 :id scoped)
    (pop 1)
    (check-sat)(get-objectives)
    """
    parser = sp.parse(source)
    output = parser.dump_smt2()
    reread = sp.parse(output)
    # Optimize.from_string collects objectives across textual push/pop on some
    # Z3 versions; use the actual incremental API for this scoped oracle.
    x, y = z3.Ints("x y")
    oracle = z3.Optimize()
    oracle.add(x >= 0, x <= 3, y >= 0, y <= 3)
    oracle.minimize(x)
    oracle.push()
    oracle.maximize(y)
    oracle.add_soft(y == 3, weight=99, id="scoped")
    oracle.pop()
    exported = load_optimizer(output)
    assert_unsat(z3.Xor(z3.And(*oracle.assertions()), z3.And(*exported.assertions())))
    assert len(oracle.objectives()) == len(exported.objectives()) == 1
    assert_unsat(oracle.objectives()[0] != exported.objectives()[0])
    assert directions(parser) == directions(reread) == [(True, False)]
    assert len(parser.soft_assertions) == len(reread.soft_assertions) == 0
    assert not re.search(r"\(\s*(push|pop|maximize|assert-soft)\b", output)
    # Only the final active state is exported. No historical command replay is
    # required or desirable for this snapshot API.
    assert len(load_optimizer(output).objectives()) == 1
    assert optimum_values(load_optimizer(output), z3.Int("x")) == (0,)
