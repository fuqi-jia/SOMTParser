"""D7: the Horn-clause cross-check.

docs/open-questions-2026-08-13.md §D7 / docs/languages/boogie.md §4.6: emit
Horn clauses from the SAME parse and check the two routes agree on the corpus.
The point is §4.1: a VC-generation bug is invisible from outside the frontend,
and a second route through a different encoding solved by a different engine
(z3's Spacer, not plain z3) makes the intermediate a checkable artefact.

  route A: boogie -> our VC  -> SMT-LIB -> z3 (Solver)
  route B: boogie -> Horn    -> CHC-COMP text -> z3 Fixedpoint (Spacer)

sat means "a counterexample exists" on BOTH routes (boogie.md §2.4), so the
agreement is direct. A disagreement fails the test and names the program.
The corpus is test_boogie_verdicts.py's -- the ok fixtures plus the programs
that MUST fail to verify, which is where a route bug would hide.

Format validation: the emitted text (with the CHC-COMP query clause appended)
is also re-parsed by our own chc frontend, so the emission is checked against
the CHC-COMP shape rules in tree.
"""

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp
from test_boogie_verdicts import VERDICT_CORPUS

# `call forall` with a wildcard denotes a quantified lemma assumption, which
# is not a Horn clause -- the chc route refuses it by name and the comparison
# is skipped, on the record here.
ROUTE_B_EXCLUDED = {"call_forall": "quantified lemma assumption is not a Horn clause"}


def verdict_direct(source):
    t = sp.translate(source=source, language="boogie")
    assert t.ok, t.diagnostic_items[0].message if t.diagnostic_items else "no model"
    solver = z3.Solver()
    solver.set("timeout", 20000)
    solver.from_string(t.to_smt2())
    return solver.check()


def horn_verdict(chc_text):
    """Solve the emitted clause set with z3's Fixedpoint (Spacer).

    The relations are Bool-valued declared functions; each clause is
    `forall vars. body => head` with the head a relation application or
    `false`. Quantified binders become declared rule variables; relation
    applications are registered. The query is the false-headed clause's
    antecedent's relation (the emitter's `error!`)."""
    fp = z3.Fixedpoint()
    fp.set("engine", "spacer")
    fp.set("timeout", 60000)
    rels = {}

    # Every Bool-returning declare-fun is a relation, wherever it appears --
    # a relation that never heads a clause (an unreachable point) must still
    # be registered or z3 rejects the rule that references it. The domain
    # sorts need a real parse: `(Array Int Int)` has nested parens.
    import re

    def parse_sort(s):
        s = s.strip()
        if s == "Int":
            return z3.IntSort()
        if s == "Bool":
            return z3.BoolSort()
        m = re.fullmatch(r"\(Array\s+(.+)\)", s)
        assert m, f"unexpected sort: {s}"
        inner = m.group(1)
        depth = 0
        for i, ch in enumerate(inner):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            elif ch == " " and depth == 0:
                return z3.ArraySort(parse_sort(inner[:i]), parse_sort(inner[i + 1:]))
        raise AssertionError(f"malformed array sort: {s}")

    def split_toplevel(txt):
        out = []
        j = 0
        while j < len(txt):
            while j < len(txt) and txt[j] == " ":
                j += 1
            if j >= len(txt):
                break
            start = j
            depth = 0
            while j < len(txt) and (txt[j] != " " or depth > 0):
                if txt[j] == "(":
                    depth += 1
                elif txt[j] == ")":
                    depth -= 1
                j += 1
            out.append(txt[start:j])
        return out

    for line in chc_text.splitlines():
        if not line.startswith("(declare-fun"):
            continue
        m = re.match(r"\(declare-fun\s+(\S+)\s*\((.*)\)\s*(\S+)\s*\)\s*$", line)
        assert m, line
        nm, dom_txt, result = m.group(1), m.group(2), m.group(3)
        if result != "Bool":
            continue
        dom = [parse_sort(s) for s in split_toplevel(dom_txt)]
        fdecl = z3.Function(nm, *dom, z3.BoolSort())
        rels[nm] = fdecl
        fp.register_relation(fdecl)

    def rel_of(app):
        d = app.decl()
        nm = d.name()
        assert nm in rels, f"relation {nm} never declared"
        return rels[nm]

    query_rel = None
    for f in z3.parse_smt2_string(chc_text):
        body = f
        consts = []
        if z3.is_quantifier(body):
            for i in range(body.num_vars()):
                consts.append(z3.Const(f"v{i}!{body.var_name(i)}", body.var_sort(i)))
            body = z3.substitute_vars(body.body(), *reversed(consts))
        if consts:
            fp.declare_var(*consts)
        if not z3.is_implies(body):
            # a bare fact: forall vars. (rel args) -- the body IS the
            # application, with the binders already substituted inside; a
            # literal `true` is a folded vacuous clause.
            if z3.is_true(body):
                continue
            assert z3.is_app(body), f"not a Horn clause: {f}"
            rel_of(body)
            fp.fact(body)
            continue
        ante, head = body.arg(0), body.arg(1)
        if z3.is_false(head):
            # the CHC-COMP query clause; the emitter's convention is that the
            # query is the error! relation.
            query_rel = "error!"
            continue
        rel_of(head)
        parts = []
        if not z3.is_true(ante):
            parts = list(ante.children()) if z3.is_and(ante) else [ante]
        fp.add_rule(head, parts)
    assert query_rel == "error!", f"no error! query clause: {chc_text}"
    return fp.query(rels[query_rel])


def chc_script(source):
    t = sp.translate(source=source, language="boogie", options={"chc": "1"})
    return t


@pytest.mark.parametrize("name,source,expected", VERDICT_CORPUS,
                         ids=[c[0] for c in VERDICT_CORPUS])
def test_boogie_chc_crosscheck(name, source, expected):
    route_a = verdict_direct(source)

    tb = chc_script(source)
    if name in ROUTE_B_EXCLUDED:
        # The named route-B refusal, pinned so a silent change in what the
        # Horn route cannot express shows up here.
        assert not tb.ok
        assert any("not a Horn clause" in d.message for d in tb.diagnostic_items)
        return
    assert tb.ok, f"chc emission failed: {tb.diagnostic_items[0].message if tb.diagnostic_items else ''}"

    text = tb.to_smt2()
    # The format check: our own chc frontend validates the CHC-COMP shape (the
    # query clause is the emitter's own, final). Its 2023-03-31 reading
    # accepts only predicate (Bool-returning) declare-funs, so a script whose
    # program has background constants or functions -- `axiom_div`'s g -- is
    # refused with exactly that message; z3 reads those fine.
    horn_text = text.replace("(set-logic ALL)", "(set-logic HORN)", 1)
    fmt = sp.translate(source=horn_text, language="chc")
    if not fmt.ok:
        assert any("must return Bool" in d.message for d in fmt.diagnostic_items), (
            "emitted text is not CHC-COMP-shaped: "
            + (fmt.diagnostic_items[0].message if fmt.diagnostic_items else ""))

    route_b = horn_verdict(text)
    assert route_a == route_b, (
        f"route disagreement on {name}: VC+z3 says {route_a}, Horn+Spacer says "
        f"{route_b}\n--- Horn clauses ---\n{text}")
