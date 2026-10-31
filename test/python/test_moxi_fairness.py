"""Fair infinite traces checked against finite graph cycles, not the encoding."""
import itertools
import pytest
import z3
import somtparser as sp


def translate(source, depth=2):
    result = sp.translate(source=source, language="moxi", profile="bmc",
                          options={"bmc_depth": str(depth)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and not result.report.fidelity.complete
    assert any(c.strategy == "bmc-fair-lasso" for c in result.report.choices)
    return result


def satisfiable(source, depth=2):
    result = translate(source, depth)
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    verdict = solver.check()
    assert verdict != z3.unknown
    return verdict == z3.sat


def source_for(edges, initial, fairness):
    def value(b):
        return "true" if b else "false"
    terms = [f"(and (= x {value(a)}) (= x' {value(b)}))" for a, b in edges]
    transition = "(or " + " ".join(terms) + ")" if terms else "false"
    conditions = " ".join(f":fairness (f{i} (= x {value(v)}))" for i, v in enumerate(fairness))
    names = " ".join(f"f{i}" for i in range(len(fairness)))
    return (f"(define-system s :output ((x Bool)) :init (= x {value(initial)}) :trans {transition})\n"
            f"(check-system s :output ((x Bool)) {conditions} :query (q ({names})))")


def graph_has_fair_path(edges, initial, fairness):
    reachable = {initial}
    while True:
        expanded = reachable | {b for a, b in edges if a in reachable}
        if expanded == reachable:
            break
        reachable = expanded
    # In a graph with two vertices these are all strongly connected cyclic
    # components. Every required state must recur in one reachable component.
    cycles = [{v} for v in (0, 1) if (v, v) in edges]
    if (0, 1) in edges and (1, 0) in edges:
        cycles.append({0, 1})
    return any(c & reachable and set(fairness) <= c for c in cycles)


@pytest.mark.parametrize("mask", range(16))
def test_all_boolean_transition_graphs(mask):
    possible = list(itertools.product((0, 1), repeat=2))
    edges = {edge for bit, edge in enumerate(possible) if mask & (1 << bit)}
    for initial, fairness in itertools.product((0, 1), [(0,), (1,), (0, 1)]):
        assert satisfiable(source_for(edges, initial, fairness)) == graph_has_fair_path(edges, initial, fairness)


def test_fairness_must_recur_not_only_hold_in_prefix():
    # true -> false -> false: the initial true cannot discharge GF true.
    assert not satisfiable(source_for({(1, 0), (0, 0)}, 1, (1,)))


def test_primed_input_fairness_and_loop_closure():
    source = """(define-system s :input ((i Bool)) :trans (= i' (not i)))
    (check-system s :input ((j Bool)) :fairness (f j') :query (q (f)))"""
    assert not satisfiable(source, 0)
    assert satisfiable(source, 1)


def test_reachability_can_hold_before_the_fair_loop():
    source = """(define-system s :output ((x Bool)) :init x :trans (not x'))
    (check-system s :output ((x Bool)) :reachable (r x)
     :fairness (f (not x)) :query (q (r f)))"""
    assert satisfiable(source)


def test_nonperiodic_integer_trace_is_not_claimed_impossible():
    source = """(define-system s :output ((x Int)) :init (= x 0) :trans (= x' (+ x 1)))
    (check-system s :output ((x Int)) :fairness (f true) :query (q (f)))"""
    result = translate(source)
    assert not satisfiable(source)
    assert "nonperiodic" in next(c.rationale for c in result.report.choices if c.strategy == "bmc-fair-lasso")
