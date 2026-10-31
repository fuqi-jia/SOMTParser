from pathlib import Path

import z3

import somtparser as sp


FIXTURES = (
    Path(__file__).parents[2]
    / "languages"
    / "syntcomp"
    / "instances"
    / "ok"
)


def _translate(name):
    source = (FIXTURES / name).read_text(encoding="utf-8")
    result = sp.translate(source=source, language="syntcomp")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


def _check(name):
    result = _translate(name)
    script = result.to_smt2()
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(script))
    return result, solver.check()


def test_official_finite_tlsf_temporal_formula_exports_complete_smt():
    result = _translate("syft_2_068.tlsf")
    text = result.to_smt2()
    parser = sp.Parser()
    parser.parse_string(text)
    assert parser.assertions
    assert "forall" in text
    assert "__somt_syntcomp_ltl_win_" in text
    assert "__somt_syntcomp_ltl_rank_" in text
    assert not result.report.fidelity.bounds


def test_finite_mealy_observes_current_input_but_moore_does_not():
    _, mealy = _check("finite_mealy_copy.tlsf")
    _, moore = _check("finite_moore_copy.tlsf")
    assert mealy == z3.sat
    assert moore == z3.unsat


def test_finite_eventually_output_can_terminate_after_acceptance():
    _, mealy = _check("finite_mealy_eventually_output.tlsf")
    _, moore = _check("finite_moore_eventually_output.tlsf")
    assert mealy == z3.sat
    assert moore == z3.sat


def test_temporal_mealy_strategy_observes_the_whole_current_input_tuple():
    # Strong next forces the finite-game path instead of the legacy stateless
    # truth table. The two-input xor cannot be chosen by a Moore controller.
    for semantics, expected in [("Mealy", z3.sat), ("Moore", z3.unsat)]:
        source = f'''INFO {{
          TITLE: "finite causal two-input response"
          SEMANTICS: Finite,{semantics}
          TARGET: {semantics}
        }}
        MAIN {{
          INPUTS {{ i; j; }} OUTPUTS {{ o; }}
          GUARANTEES {{ (o <-> ((i && !j) || (!i && j))) && X[!] true; }}
        }}'''
        result = sp.translate(source=source, language="syntcomp")
        assert result.ok, [d.message for d in result.diagnostic_items]
        script = result.to_smt2()
        if semantics == "Mealy":
            assert "(Array Bool (Array Bool Bool))" in script
        solver = z3.Solver()
        solver.set(timeout=5000)
        solver.add(z3.parse_smt2_string(script))
        assert solver.check() == expected


def test_finite_weak_and_strong_next_use_distinct_end_conditions():
    _, weak_next = _check("finite_weak_next.tlsf")
    _, weak_next_false = _check("finite_weak_next_false.tlsf")
    _, strong_next = _check("finite_strong_next.tlsf")
    _, impossible_strong_next = _check("finite_strong_next_false.tlsf")
    assert weak_next == z3.sat
    assert weak_next_false == z3.sat
    assert strong_next == z3.sat
    assert impossible_strong_next == z3.unsat


def test_finite_invariant_assumption_may_depend_on_outputs():
    _, status = _check("finite_output_dependent_assumption.tlsf")
    assert status == z3.sat


def test_initially_and_preset_are_not_conditioned_on_assumptions():
    _, status = _check("finite_preset_is_independent_of_assumptions.tlsf")
    assert status == z3.unsat


def test_empty_guarantee_and_output_sections_default_to_true():
    _, status = _check("finite_empty_specification.tlsf")
    assert status == z3.sat
