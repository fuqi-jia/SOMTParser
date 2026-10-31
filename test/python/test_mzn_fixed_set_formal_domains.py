"""Focused checks for fixed-set formal typing and nominal domains."""

import z3
import somtparser as sp


def test_empty_concrete_int_set_actual_is_context_typed():
    source = """
function bool: keep(set of int: values) = true;
constraint keep({});
solve satisfy;
"""
    translated = sp.translate(source=source, language="minizinc")
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    assert z3.parse_smt2_string(translated.to_smt2(sp.OmtDialect.Z3))


def test_named_range_set_formal_rejects_out_of_domain_member():
    source = """
set of int: SMALL = 1..3;
function bool: accepts_small(set of SMALL: values) = true;
constraint accepts_small({4});
solve satisfy;
"""
    translated = sp.translate(source=source, language="minizinc")
    assert not translated.ok
    assert any("finite domain" in item.message for item in translated.diagnostic_items)


def test_named_enum_set_formal_rejects_different_enum_identity():
    source = """
enum NODE = {n0, n1};
enum EDGE = {e0, e1};
function bool: accepts_node(set of NODE: values) = true;
constraint accepts_node({e0});
solve satisfy;
"""
    translated = sp.translate(source=source, language="minizinc")
    assert not translated.ok
    assert any("finite domain" in item.message for item in translated.diagnostic_items)
