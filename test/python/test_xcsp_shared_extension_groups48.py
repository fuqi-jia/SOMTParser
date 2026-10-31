"""Exhaustive source-relation checks for shared XCSP extension-group bodies."""
from itertools import product
import re

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _translation(source):
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    helper = re.search(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(", script)
    assert helper, script
    # Small cases emit one direct assertion per row; this verifies that the
    # optimized helper is actually applied, not merely declared.
    assert re.search(r"\(assert\s+\(" + re.escape(helper.group(1)) + r"\s", script), script
    return result, script, z3.parse_smt2_string(script)


def _fallback_assertions(source):
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    assert "__somt_xcsp_group_" not in script
    return z3.parse_smt2_string(script)


def _semantic_assertions(source):
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    return z3.parse_smt2_string(result.to_smt2())


def _exhaustive(assertions, names, domains, expected):
    variables = [z3.Int(name) for name in names]
    for values in product(*(domains[name] for name in names)):
        solver = z3.Solver()
        solver.add(*assertions)
        solver.add(*(variable == value for variable, value in zip(variables, values)))
        answer = solver.check()
        assert answer == (z3.sat if expected(dict(zip(names, values))) else z3.unsat), (
            dict(zip(names, values)), answer)


def test_varying_domains_fall_back_exactly_for_arrays_aliases_wildcards_and_outliers():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">1..2</var>'
              '<array id="base" size="[2]">0..2</array>'
              '<array id="copy" size="[2]" as="base"/>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              '<supports>(0,*)(2,1)(99,99)</supports></extension>'
              '<args>x y</args><args>copy[0] copy[1]</args>'
              '<args>base[1] copy[0]</args></group></constraints></instance>')
    assertions = _fallback_assertions(source)
    names = ["x", "y", "base[0]", "base[1]", "copy[0]", "copy[1]"]
    domains = {"x": range(0, 2), "y": range(1, 3),
               "base[0]": range(0, 3), "base[1]": range(0, 3),
               "copy[0]": range(0, 3), "copy[1]": range(0, 3)}
    table = {(0, 0), (0, 1), (0, 2), (2, 1), (99, 99)}
    scopes = [("x", "y"), ("copy[0]", "copy[1]"), ("base[1]", "copy[0]")]
    _exhaustive(assertions, names, domains, lambda a: all(
        (a[left], a[right]) in table for left, right in scopes))


def test_uniform_domain_group_shares_domain_aware_factored_relation():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var>'
              '<var id="z">0..2</var></variables><constraints><group>'
              '<extension><list>%0 %1</list>'
              '<supports>(0,1)(1,0)(0,2)(2,0)(1,2)(2,1)</supports></extension>'
              '<args>x y</args><args>y z</args><args>z x</args>'
              '</group></constraints></instance>')
    _, _, assertions = _translation(source)
    _exhaustive(assertions, ["x", "y", "z"],
                {name: range(3) for name in ("x", "y", "z")},
                lambda assignment: len({assignment["x"], assignment["y"],
                                         assignment["z"]}) == 3)


def test_repeated_formal_slot_is_preserved_in_shared_body():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="a">0..2</var><var id="b">0..2</var><var id="c">0..2</var>'
              '</variables><constraints><group><extension><list>%0 %0</list>'
              '<supports>(1,1)</supports></extension><args>a</args><args>b</args>'
              '<args>c</args></group></constraints></instance>')
    assertions = _semantic_assertions(source)
    _exhaustive(assertions, ["a", "b", "c"],
                {name: range(3) for name in ("a", "b", "c")},
                lambda assignment: all(assignment[name] == 1 for name in ("a", "b", "c")))


def test_alias_pattern_change_falls_back_and_preserves_unsat_result():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '<var id="a">0..1</var></variables><constraints><group>'
              '<extension><list>%0 %1</list><supports>(0,1)(1,0)</supports></extension>'
              '<args>x y</args><args>a a</args></group></constraints></instance>')
    assertions = _fallback_assertions(source)
    _exhaustive(assertions, ["x", "y", "a"],
                {name: range(2) for name in ("x", "y", "a")},
                lambda assignment: False)


def test_varying_domain_conflicts_fallback_and_out_of_domain_rows_are_exact():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">1..2</var><var id="z">0..2</var>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              '<conflicts>(0,1)(1,2)(99,99)</conflicts></extension>'
              '<args>x y</args><args>y z</args><args>x z</args></group>'
              '</constraints></instance>')
    assertions = _fallback_assertions(source)
    names = ["x", "y", "z"]
    domains = {"x": range(2), "y": range(1, 3), "z": range(3)}
    forbidden = {(0, 1), (1, 2), (99, 99)}
    scopes = [("x", "y"), ("y", "z"), ("x", "z")]
    _exhaustive(assertions, names, domains, lambda a: all(
        (a[left], a[right]) not in forbidden for left, right in scopes))


@pytest.mark.parametrize("table_kind,table,expected", [
    ("supports", "(0,*)(2,4)(99,99)",
     lambda a, left, right: a[left] == 0 or (a[left], a[right]) == (2, 4)),
    ("conflicts", "(0,2)(99,99)",
     lambda a, left, right: (a[left], a[right]) != (0, 2)),
])
def test_sparse_domain_shared_tables_preserve_wildcards_and_outliers(
        table_kind, table, expected):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0 2 4</var><var id="y">0 2 4</var>'
              '<var id="z">0 2 4</var></variables><constraints><group>'
              f'<extension><list>%0 %1</list><{table_kind}>{table}</{table_kind}></extension>'
              '<args>x y</args><args>y z</args><args>z x</args>'
              '</group></constraints></instance>')
    _, _, assertions = _translation(source)
    _exhaustive(assertions, ["x", "y", "z"],
                {name: (0, 2, 4) for name in ("x", "y", "z")},
                lambda assignment: all(expected(assignment, left, right)
                                       for left, right in (("x", "y"), ("y", "z"),
                                                           ("z", "x"))))


def test_shared_group_can_still_make_the_model_unsatisfiable():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              '<supports>(9,9)</supports></extension><args>x y</args>'
              '<args>y x</args></group></constraints></instance>')
    assertions = _semantic_assertions(source)
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.unsat


def test_helper_binders_avoid_source_variable_names():
    colliding_name = "__somt_xcsp_group_0_p0"
    source = (f'<instance format="XCSP3" type="CSP"><variables>'
              f'<var id="{colliding_name}">0..1</var><var id="x">0..1</var>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              '<supports>(0,1)</supports></extension>'
              f'<args>{colliding_name} x</args><args>x {colliding_name}</args>'
              '</group></constraints></instance>')
    _, script, assertions = _translation(source)
    declaration = re.search(
        r"\(define-fun\s+__somt_xcsp_group_\d+\s+\(\(([^\s()]+)\s+Int\)", script)
    assert declaration, script
    assert declaration.group(1).strip("|") != colliding_name
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.unsat


def test_generated_helper_symbols_avoid_quoted_bare_name_collisions():
    binder_collision = "|__somt_xcsp_group_1_p0|"
    function_collision = "|__somt_xcsp_group_0|"
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              f'<var id="{function_collision}">0..1</var>'
              f'<var id="{binder_collision}">0..1</var>'
              '<var id="x">0..1</var></variables><constraints><group>'
              '<extension><list>%0 %1</list><supports>(0,1)</supports></extension>'
              f'<args>{binder_collision} x</args><args>x {binder_collision}</args>'
              '</group></constraints></instance>')
    _, script, assertions = _translation(source)
    assert "(define-fun __somt_xcsp_group_0 " not in script
    assert "(define-fun __somt_xcsp_group_1 " in script
    emitted_binder = re.search(
        r"\(define-fun\s+__somt_xcsp_group_1\s+\(\(([^\s()]+)\s+Int\)", script)
    assert emitted_binder and emitted_binder.group(1).strip("|") != binder_collision.strip("|")
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.unsat


def test_percent_ellipsis_uses_ordinary_expansion_fallback():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '</variables><constraints><group><extension><list>%0 %...</list>'
              '<supports>(0,1)</supports></extension><args>x y</args>'
              '<args>y x</args></group></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    assert "__somt_xcsp_group_" not in script
    assertions = z3.parse_smt2_string(script)
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.unsat


def test_formal_bearing_table_attributes_fall_back():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              '<supports marker="%0">(0,1)</supports></extension>'
              '<args>x y</args><args>y x</args></group></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    assert "__somt_xcsp_group_" not in result.to_smt2()


@pytest.mark.parametrize("table", ["(0,1", "(0)"])
def test_malformed_or_wrong_arity_tuples_are_rejected(table):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              f'<supports>{table}</supports></extension><args>x y</args>'
              '<args>y x</args></group></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert not result.ok
    assert result.diagnostic_items


def test_bad_group_argument_arity_falls_back_to_existing_error():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              '<supports>(0,1)</supports></extension><args>x</args><args>y</args>'
              '</group></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert not result.ok
    assert result.diagnostic_items


@pytest.mark.parametrize(
    "table_kind,table,allowed",
    [("supports", "1 3..4", {1, 3, 4}),
     ("conflicts", "1 3..4", {0, 2, 5}),
     ("supports", "*", set(range(6))),
     ("conflicts", "*", set())],
)
def test_unary_group_tables_keep_bare_value_range_and_wildcard_semantics(
        table_kind, table, allowed):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..5</var><var id="y">0..5</var>'
              f'</variables><constraints><group><extension><list>%0</list>'
              f'<{table_kind}>{table}</{table_kind}></extension>'
              '<args>x</args><args>y</args></group></constraints></instance>')
    assertions = _fallback_assertions(source)
    _exhaustive(assertions, ["x", "y"],
                {"x": range(6), "y": range(6)},
                lambda assignment: assignment["x"] in allowed
                and assignment["y"] in allowed)


@pytest.mark.parametrize("table_kind,expected_sat", [("supports", False), ("conflicts", True)])
def test_empty_numeric_table_keeps_existing_semantics_without_helper(table_kind, expected_sat):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              f'</variables><constraints><group><extension><list>%0 %1</list>'
              f'<{table_kind}></{table_kind}></extension><args>x y</args>'
              '<args>y x</args></group></constraints></instance>')
    assertions = _fallback_assertions(source)
    solver = z3.Solver()
    solver.add(*assertions)
    assert (solver.check() == z3.sat) is expected_sat


def test_complete_cartesian_table_is_folded_without_helper():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              '<supports>(0,0)(0,1)(1,0)(1,1)</supports></extension>'
              '<args>x y</args><args>y x</args></group></constraints></instance>')
    assertions = _fallback_assertions(source)
    _exhaustive(assertions, ["x", "y"], {"x": range(2), "y": range(2)},
                lambda assignment: True)
