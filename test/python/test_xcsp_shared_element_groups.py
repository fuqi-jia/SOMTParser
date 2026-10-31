"""Exhaustive checks for shared indexed-element XCSP group lowering."""
from itertools import product
import re

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _assertions(source):
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    return script, z3.parse_smt2_string(script)


def _equivalent_on_all_assignments(left, right, names, domains, expected):
    symbols = {name: z3.Int(name) for name in names}
    solvers = [z3.Solver(), z3.Solver()]
    for solver, assertions in zip(solvers, (left, right)):
        solver.add(*assertions)
    for values in product(*(domains[name] for name in names)):
        assignment = dict(zip(names, values))
        observed = []
        for solver in solvers:
            solver.push()
            solver.add(*(symbols[name] == assignment[name] for name in names))
            status = solver.check()
            assert status in (z3.sat, z3.unsat), solver.reason_unknown()
            observed.append(status == z3.sat)
            solver.pop()
        assert observed == [expected(assignment)] * 2, (assignment, observed)


def _array_value(assignment, index):
    return assignment[f"x[0][{index}]"]


def test_shared_slice_element_captures_decision_variables_and_matches_expansion():
    prefix = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="x" size="[1][3]">0..1</array>'
              '<var id="i">-1..3</var><var id="j">-1..3</var>'
              '<var id="v">0..1</var><var id="w">0..1</var>'
              '</variables><constraints>')
    suffix = ('<extension><list>x[0][0] v</list><supports>(0,0)(1,1)</supports>'
              '</extension></constraints></instance>')
    shared = (prefix + '<group><element><list>x[0][]</list><index>%0</index>'
              '<value>%1</value></element><args>i v</args><args>j w</args></group>'
              + suffix)
    expanded = (prefix + '<element><list>x[0][]</list><index>i</index><value>v</value>'
                '</element><element><list>x[0][]</list><index>j</index><value>w</value>'
                '</element>' + suffix)
    shared_script, shared_assertions = _assertions(shared)
    _, expanded_assertions = _assertions(expanded)
    helper = re.search(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(", shared_script)
    assert helper, shared_script
    # Both calls may share one asserted conjunction after consuming lowering.
    assert len(re.findall(r"\(" + re.escape(helper.group(1)) + r"\s", shared_script)) == 2
    # The helper must keep the dynamic list cells as global model operands.
    for cell in ("x[0][0]", "x[0][1]", "x[0][2]"):
        assert cell in shared_script, shared_script
    names = ["x[0][0]", "x[0][1]", "x[0][2]", "i", "j", "v", "w"]
    domains = {name: range(2) for name in names[:3] + ["v", "w"]}
    domains.update({"i": range(-1, 4), "j": range(-1, 4)})

    def expected(a):
        supported = ((a["x[0][0]"] == 0 and a["v"] == 0)
                     or (a["x[0][0]"] == 1 and a["v"] == 1))
        first = 0 <= a["i"] < 3 and _array_value(a, a["i"]) == a["v"]
        second = 0 <= a["j"] < 3 and _array_value(a, a["j"]) == a["w"]
        return supported and first and second

    _equivalent_on_all_assignments(shared_assertions, expanded_assertions,
                                   names, domains, expected)


def test_repeated_list_variables_and_index_value_alias_are_preserved():
    prefix = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="a">0..2</var><var id="b">0..2</var>'
              '<var id="i">-1..3</var><var id="j">-1..3</var>'
              '</variables><constraints>')
    shared = (prefix + '<group><element><list>a a b</list><index>%0</index><value>%1</value>'
              '</element><args>i i</args><args>j j</args></group>'
              '</constraints></instance>')
    expanded = (prefix + '<element><list>a a b</list><index>i</index><value>i</value>'
                '</element><element><list>a a b</list><index>j</index><value>j</value>'
                '</element></constraints></instance>')
    script, assertions = _assertions(shared)
    _, expanded_assertions = _assertions(expanded)
    helper = re.search(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(", script)
    assert helper, script
    declaration = re.search(r"\(define-fun\s+" + re.escape(helper.group(1))
                            + r"\s+\((.*?)\)\s+Bool", script, re.S)
    assert declaration and len(re.findall(r"\([^()]+\s+Int\)", declaration.group(1))) == 1
    names = ["a", "b", "i", "j"]
    domains = {"a": range(3), "b": range(3), "i": range(-1, 4), "j": range(-1, 4)}

    def expected(a):
        def selected(index):
            return 0 <= index < 3 and (a["a"] if index < 2 else a["b"]) == index
        return selected(a["i"]) and selected(a["j"])

    _equivalent_on_all_assignments(assertions, expanded_assertions,
                                   names, domains, expected)


@pytest.mark.parametrize("rows", [
    '<args>x[0][0] v</args><args>i w</args>',
    '<args>i x[0][0]</args><args>j v</args>',
])
def test_list_global_that_aliases_one_row_operand_stays_global(rows):
    prefix = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="x" size="[1][3]">0..1</array>'
              '<var id="i">0..1</var><var id="j">0..1</var>'
              '<var id="v">0..1</var><var id="w">0..1</var>'
              '</variables><constraints>')
    shared = (prefix + '<group><element><list>x[0][]</list><index>%0</index>'
              '<value>%1</value></element>' + rows + '</group></constraints></instance>')
    if rows.startswith('<args>x[0][0]'):
        expanded = (prefix + '<element><list>x[0][]</list><index>x[0][0]</index>'
                    '<value>v</value></element><element><list>x[0][]</list><index>i</index>'
                    '<value>w</value></element></constraints></instance>')
    else:
        expanded = (prefix + '<element><list>x[0][]</list><index>i</index>'
                    '<value>x[0][0]</value></element><element><list>x[0][]</list>'
                    '<index>j</index><value>v</value></element></constraints></instance>')
    script, actual = _assertions(shared)
    _, reference = _assertions(expanded)
    assert re.search(r"\(define-fun __somt_xcsp_group_\d+\s+\(", script), script
    names = ["x[0][0]", "x[0][1]", "x[0][2]", "i", "j", "v", "w"]
    domains = {name: range(2) for name in names}

    def expected(a):
        first = _array_value(a, a["x[0][0]"]) == a["v"] \
            if rows.startswith('<args>x[0][0]') else _array_value(a, a["i"]) == a["x[0][0]"]
        second = _array_value(a, a["i"]) == a["w"] \
            if rows.startswith('<args>x[0][0]') else _array_value(a, a["j"]) == a["v"]
        return first and second

    _equivalent_on_all_assignments(actual, reference, names, domains, expected)


def test_alias_mismatch_and_first_rank_forms_fall_back_exactly():
    prefix = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="x" size="[1][3]">0..1</array>'
              '<var id="i">0..2</var><var id="v">0..2</var>'
              '<var id="j">0..2</var><var id="w">0..2</var>'
              '</variables><constraints>')
    mismatch = (prefix + '<group><element><list>x[0][]</list><index>%0</index><value>%1</value>'
                '</element><args>i v</args><args>j j</args></group></constraints></instance>')
    mismatch_ref = (prefix + '<element><list>x[0][]</list><index>i</index><value>v</value>'
                    '</element><element><list>x[0][]</list><index>j</index><value>j</value>'
                    '</element></constraints></instance>')
    mismatch_script, mismatch_assertions = _assertions(mismatch)
    # Alias-mismatched rows cannot share the specialized group prototype, but
    # the positional helper is valid: list cells, index, and value are separate
    # formals, so the second call may safely pass j for both final arguments.
    mismatch_helpers = re.findall(
        r"\(define-fun __somt_xcsp_group_\d+\s+\((.*?)\)\s+Bool",
        mismatch_script, re.S)
    assert len(mismatch_helpers) == 1
    assert len(re.findall(r"\([^()]+\s+Int\)", mismatch_helpers[0])) == 5
    _, mismatch_reference = _assertions(mismatch_ref)
    names = ["x[0][0]", "x[0][1]", "x[0][2]", "i", "v", "j", "w"]
    domains = {name: range(2) for name in names[:3]}
    domains.update({name: range(3) for name in names[3:]})

    def mismatch_expected(a):
        return _array_value(a, a["i"]) == a["v"] \
            and _array_value(a, a["j"]) == a["j"]

    _equivalent_on_all_assignments(mismatch_assertions, mismatch_reference,
                                   names, domains, mismatch_expected)

    ranked = (prefix + '<group><element><list>x[0][]</list><index rank="first">%0</index>'
              '<value>%1</value></element><args>i v</args><args>j w</args>'
              '</group></constraints></instance>')
    ranked_ref = (prefix + '<element><list>x[0][]</list><index rank="first">i</index>'
                  '<value>v</value></element><element><list>x[0][]</list>'
                  '<index rank="first">j</index><value>w</value></element>'
                  '</constraints></instance>')
    ranked_script, ranked_assertions = _assertions(ranked)
    assert "__somt_xcsp_group_" not in ranked_script
    _, ranked_reference = _assertions(ranked_ref)

    def ranked_expected(a):
        first_v = next((k for k in range(3) if _array_value(a, k) == a["v"]), None)
        first_w = next((k for k in range(3) if _array_value(a, k) == a["w"]), None)
        return a["i"] == first_v and first_v is not None \
            and a["j"] == first_w and first_w is not None

    _equivalent_on_all_assignments(ranked_assertions, ranked_reference,
                                   names, domains, ranked_expected)


def test_nonzero_start_index_and_rank_last_fall_back_exactly():
    start_prefix = ('<instance format="XCSP3" type="CSP"><variables>'
                    '<array id="x" size="[1][3]">0..1</array>'
                    '<var id="i">1..3</var><var id="j">1..3</var>'
                    '<var id="v">0..1</var><var id="w">0..1</var>'
                    '</variables><constraints>')
    start_group = (start_prefix + '<group><element><list startIndex="1">x[0][]</list>'
                   '<index>%0</index><value>%1</value></element><args>i v</args>'
                   '<args>j w</args></group></constraints></instance>')
    start_ref = (start_prefix + '<element><list startIndex="1">x[0][]</list>'
                 '<index>i</index><value>v</value></element><element>'
                 '<list startIndex="1">x[0][]</list><index>j</index><value>w</value>'
                 '</element></constraints></instance>')
    start_script, start_assertions = _assertions(start_group)
    # The positional helper also preserves the nonzero list origin; only the
    # specialized captured-list group helper requires a zero start index.
    start_helpers = re.findall(
        r"\(define-fun __somt_xcsp_group_\d+\s+\((.*?)\)\s+Bool",
        start_script, re.S)
    assert len(start_helpers) == 1
    assert len(re.findall(r"\([^()]+\s+Int\)", start_helpers[0])) == 5
    _, start_reference = _assertions(start_ref)
    names = ["x[0][0]", "x[0][1]", "x[0][2]", "i", "j", "v", "w"]
    domains = {name: range(2) for name in names[:3] + ["v", "w"]}
    domains.update({"i": range(1, 4), "j": range(1, 4)})

    def start_expected(a):
        return _array_value(a, a["i"] - 1) == a["v"] \
            and _array_value(a, a["j"] - 1) == a["w"]

    _equivalent_on_all_assignments(start_assertions, start_reference,
                                   names, domains, start_expected)

    rank_prefix = ('<instance format="XCSP3" type="CSP"><variables>'
                   '<var id="a">0..2</var><var id="b">0..2</var>'
                   '<var id="i">0..2</var><var id="j">0..2</var>'
                   '</variables><constraints>')
    rank_group = (rank_prefix + '<group><element><list>a a b</list>'
                  '<index rank="last">%0</index><value>%1</value></element>'
                  '<args>i i</args><args>j j</args></group></constraints></instance>')
    rank_ref = (rank_prefix + '<element><list>a a b</list><index rank="last">i</index>'
                '<value>i</value></element><element><list>a a b</list>'
                '<index rank="last">j</index><value>j</value></element>'
                '</constraints></instance>')
    rank_script, rank_assertions = _assertions(rank_group)
    assert "__somt_xcsp_group_" not in rank_script
    _, rank_reference = _assertions(rank_ref)
    rank_names = ["a", "b", "i", "j"]
    rank_domains = {name: range(3) for name in rank_names}

    def rank_expected(a):
        def last(index):
            matches = [k for k, item in enumerate((a["a"], a["a"], a["b"]))
                       if item == index]
            return bool(matches) and index == matches[-1]
        return last(a["i"]) and last(a["j"])

    _equivalent_on_all_assignments(rank_assertions, rank_reference,
                                   rank_names, rank_domains, rank_expected)


def test_cached_fresh_names_respect_global_function_and_parameter_collisions():
    prefix = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="x" size="[1][3]">0..1</array>'
              '<var id="__somt_xcsp_group_0">0..1</var>'
              '<var id="__somt_xcsp_group_1_p0">0..1</var>'
              '<var id="i">0..2</var><var id="j">0..2</var>'
              '<var id="v">0..1</var><var id="w">0..1</var>'
              '</variables><constraints>')
    shared = (prefix + '<group><element><list>x[0][]</list><index>%0</index>'
              '<value>%1</value></element><args>i v</args><args>j w</args>'
              '</group></constraints></instance>')
    expanded = (prefix + '<element><list>x[0][]</list><index>i</index><value>v</value>'
                '</element><element><list>x[0][]</list><index>j</index><value>w</value>'
                '</element></constraints></instance>')
    script, shared_assertions = _assertions(shared)
    _, expanded_assertions = _assertions(expanded)
    helper = re.search(r"\(define-fun (__somt_xcsp_group_\d+)\s+\((.*?)\)\s+Bool",
                       script, re.S)
    assert helper, script
    # A fresh counter may skip both the function and its formal namespace.
    assert helper.group(1) not in {"__somt_xcsp_group_0", "__somt_xcsp_group_1_p0"}
    # The first formal candidate would shadow the deliberately declared source
    # global; the cache must preserve the same collision avoidance as the scan.
    assert not re.search(r"\(\s*__somt_xcsp_group_1_p0\s+Int\s*\)",
                         helper.group(2))

    names = ["x[0][0]", "x[0][1]", "x[0][2]", "i", "j", "v", "w",
             "__somt_xcsp_group_0", "__somt_xcsp_group_1_p0"]
    domains = {name: range(2) for name in names[:3] + ["v", "w",
                                                        "__somt_xcsp_group_0",
                                                        "__somt_xcsp_group_1_p0"]}
    domains.update({"i": range(3), "j": range(3)})

    def expected(a):
        return a[f"x[0][{a['i']}]"] == a["v"] \
            and a[f"x[0][{a['j']}]"] == a["w"]

    _equivalent_on_all_assignments(shared_assertions, expanded_assertions,
                                   names, domains, expected)
