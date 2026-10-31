from fractions import Fraction

import pytest
import somtparser as sp
from somtparser._nl_model import ModelError
from somtparser.nl_datasets import (
    exact_number,
    nl4opt_reference,
    normalize_pycsp3_singleton_counts,
)


def record():
    return {
        "order_mapping": {"x": 0, "y": 1},
        "obj_declaration": {
            "type": "objective",
            "direction": "maximize",
            "terms": {"x": "third", "y": "2"},
        },
        "const_declarations": [
            {
                "type": "ratio",
                "var": "x",
                "limit": "35 percent",
                "operator": "LESS_OR_EQUAL",
            },
            {"type": "sum", "limit": "10", "operator": "LESS_OR_EQUAL"},
        ],
    }


def test_exact_coefficients_and_cost_map():
    r = nl4opt_reference(record())
    assert r.objective_scale == 3
    assert r.rows[0] == ((Fraction(13, 20), Fraction(-7, 20)), 0)
    assert r.maximize
    t = sp.translate(source=r.to_lp(), language="lp", dialect=sp.OmtDialect.Z3)
    assert t.ok
    assert "Real" in t.to_smt2(dialect=sp.OmtDialect.Z3)
    assert "maximize" in t.to_smt2(dialect=sp.OmtDialect.Z3)


def test_reference_mutations_not_silently_repaired():
    r = record()
    r["const_declarations"][0]["operator"] = "LESS"
    with pytest.raises(ModelError, match="direction"):
        nl4opt_reference(r)
    r = record()
    r["order_mapping"]["alias"] = 0
    r["obj_declaration"]["terms"]["alias"] = "5"
    with pytest.raises(ModelError, match="duplicate"):
        nl4opt_reference(r)
    with pytest.raises(ModelError, match="unsupported"):
        exact_number("8000 minutes or 9000")


def test_objvar_and_lower_bound():
    r = record()
    r["obj_declaration"] = {
        "type": "objvar",
        "direction": "Minimize",
        "vars": ["x", "y"],
    }
    r["const_declarations"] = [
        {
            "type": "lowerbound",
            "var": "x",
            "limit": "half",
            "operator": "GREATER_OR_EQUAL",
        }
    ]
    ref = nl4opt_reference(r)
    assert ref.rows == (((-1, 0), Fraction(-1, 2)),)
    assert ref.objective == (1, 1) and not ref.maximize
    r["obj_declaration"]["vars"] = []
    with pytest.raises(ModelError, match="no annotated variables"):
        nl4opt_reference(r)


def test_singleton_export_bridge_keeps_nontrivial_condition():
    xml = """<instance format="XCSP3" type="CSP"><variables><var id="x">0..1</var></variables>
    <constraints><group><count><list>%...</list><values>1</values><condition>(eq,1)</condition></count>
    <args>x</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert len(changes) == 1
    t = sp.translate(source=normalized, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert t.ok
    z3 = pytest.importorskip("z3")
    solver = z3.Solver()
    solver.from_string(t.to_smt2(dialect=sp.OmtDialect.Z3))
    solver.push()
    solver.add(z3.Int("x") == 0)
    assert solver.check() == z3.unsat
    solver.pop()
    solver.add(z3.Int("x") == 1)
    assert solver.check() == z3.sat




def test_export_bridge_does_not_drop_reification():
    xml = """<instance><constraints><group><count reifiedBy="b">
    <list>%...</list><values>1</values><condition>(eq,1)</condition></count>
    <args>x</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert not changes and 'reifiedBy="b"' in normalized


def test_singleton_export_bridge_list_parameter_form():
    # PyCSP3's compactor also emits the singleton form <list>%0</list>.
    xml = """<instance format="XCSP3" type="CSP"><variables><array id="x" size="[2]">0..1</array></variables>
    <constraints><group><count><list>%0</list><values>1</values><condition>(ge,1)</condition></count>
    <args>x[0]</args><args>x[1]</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert len(changes) == 2
    assert {c["rule"] for c in changes} == {
        "singleton-count-list-parameter-to-indicator-v1"
    }
    assert "<group>" not in normalized
    t = sp.translate(source=normalized, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert t.ok
    z3 = pytest.importorskip("z3")
    solver = z3.Solver()
    solver.from_string(t.to_smt2(dialect=sp.OmtDialect.Z3))
    solver.push()
    solver.add(z3.Int("x[0]") == 0)
    assert solver.check() == z3.unsat  # ge(indicator, 1) forces x[0] to 1
    solver.pop()
    solver.add(z3.Int("x[0]") == 1, z3.Int("x[1]") == 1)
    assert solver.check() == z3.sat


def test_singleton_export_bridge_keeps_nonvariable_rows():
    # A slice row under a %0 list is not a singleton: with only one row left the
    # group would be invalid, so it is unwrapped into its direct count expansion.
    xml = """<instance format="XCSP3" type="CSP"><variables><array id="x" size="[4]">0..1</array></variables>
    <constraints><group><count><list>%0</list><values>1</values><condition>(le,1)</condition></count>
    <args>x[0]</args><args>x[1..3]</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert {c["rule"] for c in changes} == {
        "singleton-count-list-parameter-to-indicator-v1",
        "count-group-unwrap-v1",
    }
    assert "<group>" not in normalized and "x[1..3]" in normalized
    t = sp.translate(source=normalized, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert t.ok


def test_singleton_export_bridge_aborts_on_inexact_leftover():
    # Two tokens under a %0 list: the frontend would drop the second silently,
    # so the bridge leaves the whole group for the frontend instead.
    xml = """<instance format="XCSP3" type="CSP"><variables><array id="x" size="[3]">0..1</array></variables>
    <constraints><group><count><list>%0</list><values>1</values><condition>(le,1)</condition></count>
    <args>x[0]</args><args>x[1] x[2]</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert not changes and "<group>" in normalized


def test_singleton_export_bridge_condition_parameter_form():
    # (eq,%0): the bound is the row's first token, possibly itself a variable;
    # the frontend's substituteFormals binds %0 before %... takes the tail.
    # The two-variable row is unwrapped into the direct count the group means.
    xml = """<instance format="XCSP3" type="CSP"><variables><array id="x" size="[3]">0..1</array>
    <array id="aux" size="[1]">0..1</array></variables>
    <constraints><group><count><list>%...</list><values>1</values><condition>(eq,%0)</condition></count>
    <args>aux[0] x[2]</args><args>aux[0] x[0] x[1]</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert len(changes) == 2
    assert changes[0]["rule"] == "count-group-unwrap-v1"
    assert changes[1]["rule"] == "singleton-count-condition-parameter-to-indicator-v1"
    assert changes[1]["expression"] == "eq(if(eq(x[2],1),1,0),aux[0])"
    assert "<group>" not in normalized
    assert "(eq,aux[0])" in normalized and "x[0] x[1]" in normalized
    t = sp.translate(source=normalized, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert t.ok
    z3 = pytest.importorskip("z3")
    solver = z3.Solver()
    solver.from_string(t.to_smt2(dialect=sp.OmtDialect.Z3))
    solver.push()
    solver.add(z3.Int("x[2]") == 0, z3.Int("aux[0]") == 1)
    assert solver.check() == z3.unsat  # count is 0, so the bound variable must be 0
    solver.pop()
    solver.add(z3.Int("x[2]") == 1, z3.Int("aux[0]") == 1, z3.Int("x[0]") == 1)
    solver.add(z3.Int("x[1]") == 0)
    assert solver.check() == z3.sat


def test_singleton_export_bridge_condition_parameter_literal_bound():
    xml = """<instance format="XCSP3" type="CSP"><variables><array id="x" size="[1]">0..1</array></variables>
    <constraints><group><count><list>%...</list><values>1</values><condition>(eq,%0)</condition></count>
    <args>2 x[0]</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert len(changes) == 1 and changes[0]["expression"] == "eq(if(eq(x[0],1),1,0),2)"
    t = sp.translate(source=normalized, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert t.ok
    z3 = pytest.importorskip("z3")
    solver = z3.Solver()
    solver.from_string(t.to_smt2(dialect=sp.OmtDialect.Z3))
    assert solver.check() == z3.unsat  # a singleton list cannot reach a count of 2


def test_singleton_export_bridge_parameter_pair_form():
    # The compactor's paired form: %0 list (variable first) and %1 bound.
    xml = """<instance format="XCSP3" type="CSP"><variables><array id="x" size="[2]">0..1</array>
    <array id="aux" size="[2]">0..1</array></variables>
    <constraints><group><count><list>%0</list><values>1</values><condition>(eq,%1)</condition></count>
    <args>x[0] aux[0]</args><args>x[1] aux[1]</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert len(changes) == 2
    assert {c["rule"] for c in changes} == {
        "singleton-count-parameter-pair-to-indicator-v1"
    }
    assert changes[0]["expression"] == "eq(if(eq(x[0],1),1,0),aux[0])"
    assert "<group>" not in normalized
    t = sp.translate(source=normalized, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert t.ok
    z3 = pytest.importorskip("z3")
    solver = z3.Solver()
    solver.from_string(t.to_smt2(dialect=sp.OmtDialect.Z3))
    solver.push()
    solver.add(z3.Int("x[0]") == 0, z3.Int("aux[0]") == 1)
    assert solver.check() == z3.unsat  # the bound variable tracks the indicator
    solver.pop()
    solver.add(z3.Int("x[0]") == 1, z3.Int("aux[0]") == 1)
    solver.add(z3.Int("x[1]") == 0, z3.Int("aux[1]") == 0)
    assert solver.check() == z3.sat


def test_singleton_export_bridge_parameter_pair_unwrap_and_abort():
    # A leftover slice row unwraps into the direct count the group expands to.
    xml = """<instance format="XCSP3" type="CSP"><variables><array id="x" size="[3]">0..1</array>
    <array id="aux" size="[2]">0..2</array></variables>
    <constraints><group><count><list>%0</list><values>1</values><condition>(eq,%1)</condition></count>
    <args>x[0] aux[0]</args><args>x[1..2] aux[1]</args></group></constraints></instance>"""
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert {c["rule"] for c in changes} == {
        "singleton-count-parameter-pair-to-indicator-v1",
        "count-group-unwrap-v1",
    }
    assert "<group>" not in normalized and "x[1..2]" in normalized
    t = sp.translate(source=normalized, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert t.ok
    # Three tokens under the pair form: the group is left untouched instead.
    xml = xml.replace("<args>x[1..2] aux[1]</args>", "<args>x[1] x[2] aux[1]</args>")
    normalized, changes = normalize_pycsp3_singleton_counts(xml)
    assert not changes and "<group>" in normalized
