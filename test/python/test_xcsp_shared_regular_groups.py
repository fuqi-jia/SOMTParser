"""Semantic equivalence checks for factored XCSP3 regular groups."""
import itertools
import re

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


_NFA = ('(s,0,a)(s,0,b)(s,0,a)(s,1,b)(a,0,f)(b,1,f)')
_ACCEPTED = {(0, 0), (0, 1), (1, 1)}


def _translation(constraints, declarations):
    source = ('<instance format="XCSP3" type="CSP"><variables>' + declarations
              + '</variables><constraints>' + constraints
              + '</constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    return script, z3.parse_smt2_string(script)


def _same_relation_on_all_assignments(left, right, names, domains, expected):
    symbols = {name: z3.Int(name) for name in names}
    solvers = []
    for assertions in (left, right):
        solver = z3.Solver()
        solver.add(*assertions)
        solvers.append(solver)
    for values in itertools.product(*(domains[name] for name in names)):
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


def test_nondeterministic_regular_group_is_one_pure_shared_word_predicate():
    declarations = ('<var id="x">0..1</var><var id="y">0..1</var>'
                    '<var id="z">1..2</var><var id="w">0..1</var>')
    regular = ('<regular><list>%...</list><transitions>' + _NFA
               + '</transitions><start>s</start><final>f</final></regular>')
    group = ('<group>' + regular + '<args>x y</args><args>z w</args>'
             '<args>x x</args></group>')
    expanded = ('<regular><list>x y</list><transitions>' + _NFA
                + '</transitions><start>s</start><final>f</final></regular>'
                '<regular><list>z w</list><transitions>' + _NFA
                + '</transitions><start>s</start><final>f</final></regular>'
                '<regular><list>x x</list><transitions>' + _NFA
                + '</transitions><start>s</start><final>f</final></regular>')
    script, shared = _translation(group, declarations)
    _, reference = _translation(expanded, declarations)
    helper = re.search(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(", script)
    assert helper, script
    assert len(re.findall(r"\(" + re.escape(helper.group(1)) + r"\s", script)) == 3
    # No row-specific existential reachability witnesses are shared by calls.
    assert "__somt_xcsp3_aux_" not in script
    names = ["x", "y", "z", "w"]
    domains = {"x": range(2), "y": range(2), "z": range(1, 3), "w": range(2)}

    def expected(a):
        return (a["x"], a["y"]) in _ACCEPTED \
            and (a["z"], a["w"]) in _ACCEPTED \
            and (a["x"], a["x"]) in _ACCEPTED

    _same_relation_on_all_assignments(shared, reference, names, domains, expected)


def test_unreachable_final_state_stays_unsatisfiable_and_empty_word_stays_rejected():
    declarations = '<var id="x">0..1</var><var id="y">0..1</var>'
    unreachable = ('<group><regular><list>%...</list><transitions>'
                   '(s,0,s)(u,0,f)</transitions><start>s</start><final>f</final>'
                   '</regular><args>x</args><args>y</args></group>')
    script, assertions = _translation(unreachable, declarations)
    solver = z3.Solver()
    solver.add(*assertions)
    assert solver.check() == z3.unsat
    # This zero-width group row denotes an empty regular word, which the
    # established languageConstraint currently rejects. The optimization must
    # fall back and preserve that frontend behavior rather than inventing a
    # different empty-word policy.
    empty = ('<group><regular><list>%...</list><transitions>(s,0,f)</transitions>'
             '<start>s</start><final>f</final></regular><args></args><args>x</args>'
             '</group>')
    source = ('<instance format="XCSP3" type="CSP"><variables>' + declarations
              + '</variables><constraints>' + empty + '</constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert not result.ok
    assert any("empty variable list" in diagnostic.message for diagnostic in result.diagnostic_items)


def test_different_row_alias_patterns_keep_independent_word_actuals():
    declarations = ('<var id="x">0..1</var><var id="y">0..1</var>'
                    '<var id="z">0..1</var>')
    group = ('<group><regular><list>%...</list><transitions>' + _NFA
             + '</transitions><start>s</start><final>f</final></regular>'
             '<args>x y</args><args>z z</args></group>')
    expanded = ('<regular><list>x y</list><transitions>' + _NFA
                + '</transitions><start>s</start><final>f</final></regular>'
                '<regular><list>z z</list><transitions>' + _NFA
                + '</transitions><start>s</start><final>f</final></regular>')
    script, shared = _translation(group, declarations)
    _, reference = _translation(expanded, declarations)
    assert re.search(r"\(define-fun __somt_xcsp_group_\d+\s+\(", script), script
    names = ["x", "y", "z"]
    domains = {name: range(2) for name in names}

    def expected(a):
        return (a["x"], a["y"]) in _ACCEPTED and (a["z"], a["z"]) in _ACCEPTED

    _same_relation_on_all_assignments(shared, reference, names, domains, expected)


def test_generated_word_parameters_do_not_shadow_source_variables():
    collision = "__somt_xcsp_group_0_p0"
    declarations = ('<var id="x">0..1</var><var id="y">0..1</var>'
                    '<var id="z">0..1</var><var id="' + collision
                    + '">0..1</var>')
    group = ('<group><regular><list>%...</list><transitions>' + _NFA
             + '</transitions><start>s</start><final>f</final></regular>'
             '<args>' + collision + ' x</args><args>z y</args></group>')
    expanded = ('<regular><list>' + collision + ' x</list><transitions>' + _NFA
                + '</transitions><start>s</start><final>f</final></regular>'
                '<regular><list>z y</list><transitions>' + _NFA
                + '</transitions><start>s</start><final>f</final></regular>')
    script, shared = _translation(group, declarations)
    _, reference = _translation(expanded, declarations)
    helper = re.search(r"\(define-fun (__somt_xcsp_group_\d+)\s+\(([^)]*)\)", script)
    assert helper, script
    assert not re.search(r"\(\(\s*" + re.escape(collision) + r"\s", script), script
    names = ["x", "y", "z", collision]
    domains = {name: range(2) for name in names}

    def expected(a):
        return (a[collision], a["x"]) in _ACCEPTED \
            and (a["z"], a["y"]) in _ACCEPTED

    _same_relation_on_all_assignments(shared, reference, names, domains, expected)


def test_branching_nfa_keeps_shared_reachability_across_forty_positions():
    # Two indistinguishable accepting paths at every letter: exponentially
    # many paths, but a linear-sized shared recurrence. The exact language is
    # 0^40 for each row, giving an independent formula for the entire relation.
    width = 40
    declarations = (f'<array id="x" size="[{width}]">0..1</array>'
                    f'<array id="y" size="[{width}]">0..1</array>')
    group = ('<group><regular><list>%...</list><transitions>'
             '(s,0,a)(s,0,b)(a,0,a)(a,0,b)(b,0,a)(b,0,b)'
             '</transitions><start>s</start><final>a</final></regular>'
             '<args>x[]</args><args>y[]</args></group>')
    _, assertions = _translation(group, declarations)
    expected = z3.And(*(z3.Int(f"{row}[{i}]") == 0
                        for row in ("x", "y") for i in range(width)))
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*assertions), expected))
    assert solver.check() == z3.unsat, solver.reason_unknown()
