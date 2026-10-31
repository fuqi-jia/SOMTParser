"""Exact HIR-function sharing for repeated ordinary XCSP extension tables."""
from itertools import product
import re

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _translate(source):
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    return script, z3.parse_smt2_string(script)


def _exhaustive(assertions, names, domains, expected):
    variables = [z3.Int(name) for name in names]
    for values in product(*(domains[name] for name in names)):
        assignment = dict(zip(names, values))
        solver = z3.Solver()
        solver.add(*assertions)
        solver.add(*(variable == value for variable, value in zip(variables, values)))
        answer = solver.check()
        assert answer == (z3.sat if expected(assignment) else z3.unsat), assignment


def test_repeated_support_and_conflict_tables_share_exact_definitions():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var>'
              '<var id="z">0..2</var></variables><constraints>'
              '<extension><list>x y</list><supports>'
              '(0,1)(1,0)(0,2)(2,0)(1,2)(2,1)</supports></extension>'
              '<extension><list>y z</list><supports>'
              '(0,1)(1,0)(0,2)(2,0)(1,2)(2,1)</supports></extension>'
              '<extension><list>x z</list><conflicts>(0,0)(1,1)</conflicts></extension>'
              '<extension><list>y z</list><conflicts>(0,0)(1,1)</conflicts></extension>'
              '</constraints></instance>')
    script, assertions = _translate(source)
    helpers = re.findall(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(", script)
    assert len(helpers) == 2, script
    for helper in helpers:
        assert script.count("(" + helper + " ") >= 2, script
    _exhaustive(assertions, ["x", "y", "z"],
                {name: range(3) for name in ("x", "y", "z")},
                lambda a: (a["x"] != a["y"] and a["y"] != a["z"]
                           and not (a["x"] == a["z"] and a["x"] in (0, 1))))


def test_same_table_with_different_domains_is_not_shared():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '<var id="z">0..2</var></variables><constraints>'
              '<extension><list>x y</list><supports>(0,1)(1,0)</supports></extension>'
              '<extension><list>x z</list><supports>(0,1)(1,0)</supports></extension>'
              '</constraints></instance>')
    script, assertions = _translate(source)
    assert "__somt_xcsp_group_" not in script
    _exhaustive(assertions, ["x", "y", "z"],
                {"x": range(2), "y": range(2), "z": range(3)},
                lambda a: a["x"] != a["y"]
                and (a["x"], a["z"]) in {(0, 1), (1, 0)})


def test_same_table_with_different_alias_patterns_is_not_shared():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '<var id="z">0..1</var></variables><constraints>'
              '<extension><list>x y</list><supports>(0,1)(1,0)</supports></extension>'
              '<extension><list>z z</list><supports>(0,1)(1,0)</supports></extension>'
              '</constraints></instance>')
    script, assertions = _translate(source)
    assert "__somt_xcsp_group_" not in script
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.unsat


def test_cell_specific_array_domains_allow_only_matching_scope_signatures():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="a" size="[4]">'
              '<domain for="a[0..1]">0..1</domain>'
              '<domain for="a[2..3]">0..2</domain>'
              '</array></variables><constraints>'
              '<extension><list>a[0] a[2]</list>'
              '<supports>(0,1)(1,0)</supports></extension>'
              '<extension><list>a[1] a[3]</list>'
              '<supports>(0,1)(1,0)</supports></extension>'
              '<extension><list>a[0] a[1]</list>'
              '<supports>(0,1)(1,0)</supports></extension>'
              '<extension><list>a[2] a[3]</list>'
              '<supports>(0,1)(1,0)</supports></extension>'
              '</constraints></instance>')
    script, assertions = _translate(source)
    # The first two scopes have the same mixed domain vector and share. The
    # final two have different per-position domains and stay expanded.
    helpers = re.findall(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(", script)
    assert len(helpers) == 1, script
    assert script.count("(" + helpers[0] + " ") == 2, script
    names = [f"a[{i}]" for i in range(4)]
    domains = {"a[0]": range(2), "a[1]": range(2),
               "a[2]": range(3), "a[3]": range(3)}
    _exhaustive(assertions, names, domains,
                lambda a: (a["a[0]"], a["a[2]"]) in {(0, 1), (1, 0)}
                and (a["a[1]"], a["a[3]"]) in {(0, 1), (1, 0)}
                and (a["a[0]"], a["a[1]"]) in {(0, 1), (1, 0)}
                and (a["a[2]"], a["a[3]"]) in {(0, 1), (1, 0)})


def test_block_memo_does_not_capture_interleaved_slide_or_group_instances():
    support = "(0,0)(0,1)(1,0)"
    source = (f'<instance format="XCSP3" type="CSP"><variables>'
              f'<var id="a">0..1</var><var id="b">0..1</var>'
              f'<var id="c">0..1</var><var id="u">0..2</var>'
              f'<var id="v">0..2</var></variables><constraints>'
              f'<block>'
              f'<extension><list>a b</list><supports>{support}</supports></extension>'
              f'</block>'
              f'<slide><list>u v</list><extension><list>%0 %1</list>'
              f'<supports>{support}</supports></extension></slide>'
              f'<block><extension><list>b c</list><supports>{support}</supports>'
              f'</extension></block>'
              f'<group><extension><list>%0 %1</list><supports>{support}'
              f'</supports></extension><args>u v</args><args>v u</args></group>'
              f'</constraints></instance>')
    script, assertions = _translate(source)
    helpers = re.findall(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(", script)
    assert len(helpers) >= 1, script
    # One ordinary helper serves only the two block constraints; the group
    # may have its own helper, while the slide instance is expanded directly.
    assert any(script.count("(" + helper + " ") == 2 for helper in helpers), script
    _exhaustive(assertions, ["a", "b", "c", "u", "v"],
                {"a": range(2), "b": range(2), "c": range(2),
                 "u": range(3), "v": range(3)},
                lambda x: all((x[left], x[right]) in {(0, 0), (0, 1), (1, 0)}
                              for left, right in (("a", "b"), ("b", "c"),
                                                  ("u", "v"), ("u", "v"),
                                                  ("v", "u"))))


def test_unique_table_stays_on_existing_lowering_path():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var>'
              '</variables><constraints><extension><list>x y</list>'
              '<supports>(0,1)(1,0)(0,2)(2,0)(1,2)(2,1)</supports>'
              '</extension></constraints></instance>')
    script, assertions = _translate(source)
    assert "__somt_xcsp_group_" not in script
    _exhaustive(assertions, ["x", "y"],
                {"x": range(3), "y": range(3)}, lambda a: a["x"] != a["y"])


def test_malformed_repeated_table_still_reports_error():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..1</var><var id="y">0..1</var>'
              '</variables><constraints>'
              '<extension><list>x y</list><supports>(0)</supports></extension>'
              '<extension><list>y x</list><supports>(0)</supports></extension>'
              '</constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert not result.ok
    assert result.diagnostic_items


def test_file_owned_repeated_table_text_survives_earlier_node_erasure(tmp_path):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var>'
              '<var id="z">0..2</var></variables><constraints>'
              '<extension><list>x y</list>'
              '<supports>(0,1)(1,0)(0,2)(2,0)(1,2)(2,1)</supports></extension>'
              '<extension><list>y z</list>'
              '<supports>(0,1)(1,0)(0,2)(2,0)(1,2)(2,1)</supports></extension>'
              '</constraints></instance>')
    path = tmp_path / "owned-repeated-table.xml"
    path.write_text(source)
    result = sp.translate(path=str(path), language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    assert re.search(r"\(define-fun __somt_xcsp_group_\d+\s+\(", script), script
    assertions = z3.parse_smt2_string(script)
    _exhaustive(assertions, ["x", "y", "z"],
                {name: range(3) for name in ("x", "y", "z")},
                lambda a: a["x"] != a["y"] and a["y"] != a["z"])
