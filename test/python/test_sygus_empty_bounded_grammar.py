"""An empty bounded search space is UNSAT; malformed source remains an error."""

import pytest
import somtparser as sp
import z3


def translate(source, depth=0):
    return sp.translate(source=source, language="sygus", profile="bmc",
                        options={"grammar_depth": str(depth)})


def status(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


@pytest.mark.parametrize("sort,leaf", [
    ("Bool", "true"), ("Int", "0"), ("String", '"a"'),
    ("(_ BitVec 4)", "#b0000"),
])
def test_depth_exhaustion_does_not_invent_a_definition(sort, leaf):
    source = (f"(set-logic ALL) (synth-fun f () {sort} "
              f"((Start {sort} (Next)) (Next {sort} ({leaf})))) "
              f"(constraint (= f {leaf})) (check-synth)")
    result = translate(source)
    assert status(result) == z3.unsat
    choice = next(c for c in result.report.choices
                  if c.strategy == "empty-bounded-grammar")
    assert "grammar_depth=0" in choice.rationale
    assert "candidate_" not in result.to_smt2()
    assert status(translate(source, depth=1)) == z3.sat


def test_one_empty_grammar_makes_joint_synthesis_unsatisfiable():
    source = ("(set-logic LIA) (declare-var x Int) "
              "(synth-fun f ((a Int)) Int ((Start Int (Next)) (Next Int (a)))) "
              "(synth-fun g ((a Int)) Int ((Start Int (a)))) "
              "(constraint (= (f x) (g x))) (check-synth)")
    assert status(translate(source)) == z3.unsat
    assert status(translate(source, depth=1)) == z3.sat


@pytest.mark.parametrize("tail", [
    "(constraint (+ f 1)) (check-synth)",
    "(constraint (= f missing)) (check-synth)",
    "(define-fun bad () Bool (+ f 1)) (constraint true) (check-synth)",
    "(synth-fun g () Int ((Start Int (true)))) (constraint true) (check-synth)",
])
def test_empty_search_space_does_not_hide_source_errors(tail):
    source = ("(set-logic LIA) (synth-fun f () Int "
              "((Start Int (Next)) (Next Int (0)))) " + tail)
    result = translate(source)
    assert not result.ok
    assert result.diagnostic_items


def test_unproductive_grammar_has_no_finite_bounded_witness():
    source = ("(set-logic LIA) (synth-fun f () Int ((Start Int (Start)))) "
              "(constraint (= f 0)) (check-synth)")
    assert status(translate(source, depth=4)) == z3.unsat
