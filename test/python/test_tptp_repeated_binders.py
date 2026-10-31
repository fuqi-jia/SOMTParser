"""Semantic checks for repeated source variables in TPTP binder lists."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def test_duplicate_universal_binder_matches_single_universal_semantically():
    source = (
        "fof(repeated, axiom, ![X,X] : p(X)).\n"
        "fof(single, conjecture, ![Y] : p(Y)).\n"
    )
    result = sp.translate(source=source, language="tptp")
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = result.to_smt2()
    assert "tptp_shadow_" in target
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(target))
    # The axiom and conjecture are equivalent; a sound refutation encoding is
    # therefore inconsistent. This checks meaning, not just parser acceptance.
    assert solver.check() == z3.unsat


def test_repeated_name_in_nested_list_does_not_capture_outer_occurrences():
    source = (
        "fof(nested, axiom, ![X] : (p(X) & (?[X,X] : q(X)) & r(X))).\n"
        "fof(reference, conjecture, ![Y] : (p(Y) & (?[Z] : q(Z)) & r(Y))).\n"
    )
    result = sp.translate(source=source, language="tptp")
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = result.to_smt2()
    assert target.count("tptp_shadow_") >= 2
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(target))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("constant", ["tptp_shadow_1", "'tptp_shadow_1'"])
@pytest.mark.parametrize("quantifiers", ["![X,X]", "![X] : ![X]"])
def test_alpha_renaming_does_not_capture_a_source_constant(constant, quantifiers):
    source = (
        f"fof(singleton, axiom, {quantifiers} : X = {constant}).\n"
        "fof(all_equal, conjecture, ![Y,Z] : Y = Z).\n"
    )
    result = sp.translate(source=source, language="tptp")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    # The axiom forces a singleton universe. Capturing the source constant
    # instead turns it into X=X and admits a two-element countermodel.
    assert solver.check() == z3.unsat
