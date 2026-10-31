"""Separate implementation contracts, independently checked by Z3.

The optional probe runs a frozen C++ frontend without rebuilding the Python
extension. Both paths produce the same SMT-LIB entry point.
"""
import os
import subprocess

import pytest

z3 = pytest.importorskip("z3")


def script(source, horn=False):
    probe = os.environ.get("SOMTPARSER_BOOGIE_PROBE")
    if probe:
        result = subprocess.run([probe, "chc" if horn else "vc"], input=source,
                                text=True, capture_output=True, timeout=30)
        assert result.returncode == 0, result.stderr
        return result.stdout
    import somtparser as sp
    translated = sp.translate(source=source, language="boogie",
                              options={"chc": "1"} if horn else {})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    return translated.to_smt2()


CASES = [
    ("before_declaration", "implementation P(b:int) returns(s:int) { s:=b+1; } "
     "procedure P(a:int) returns(r:int); ensures r==a+1;", True),
    ("renamed_requires", "procedure P(a:int) returns(r:int); requires a>0; ensures r>0; "
     "implementation P(b:int) returns(s:int) { s:=b; }", True),
    ("renamed_bad_ensures", "procedure P(a:int) returns(r:int); requires a>0; ensures r>a; "
     "implementation P(b:int) returns(s:int) { s:=b; }", False),
    ("swapped_names", "procedure P(x,y:int) returns(z:int); requires x<y; ensures z==x; "
     "implementation P(y,x:int) returns(w:int) { assert y<x; w:=y; }", True),
    ("swapped_bad", "implementation P(y,x:int) returns(w:int) { w:=x; } "
     "procedure P(x,y:int) returns(z:int); requires x<y; ensures z==x;", False),
    ("checked_call_requires", "procedure P(x:int); requires x>0; "
     "implementation P(a:int) { assert a>0; } procedure Q() { call P(0); }", False),
    ("free_requires_ignored_at_call", "procedure P(x:int); free requires x>0; "
     "implementation P(a:int) { assert a>0; } procedure Q() { call P(0); }", True),
    ("free_ensures_body", "procedure P() returns(r:int); free ensures r>0; "
     "implementation P() returns(s:int) { s:=0; }", True),
    ("free_ensures_call", "procedure P() returns(r:int); free ensures r>0; "
     "implementation P() returns(s:int) { s:=0; } "
     "procedure Q() { var x:int; call x:=P(); assert x>0; }", True),
    ("old_globals", "var g:int; procedure P(x:int) returns(r:int); modifies g; "
     "ensures g==old(g)+x && r==old(g); "
     "implementation P(y:int) returns(s:int) { s:=g; g:=g+y; }", True),
    ("call_frame", "var g,h:int; procedure P(); modifies g; ensures g==old(g)+1; "
     "implementation P() { g:=g+1; } procedure Q() modifies g; "
     "requires g==0 && h==7; { call P(); assert g==1 && h==7; }", True),
    ("call_havoc", "var g:int; procedure P(); modifies g; "
     "implementation P() { g:=1; } procedure Q() modifies g; requires g==0; "
     "{ call P(); assert g==0; }", False),
    ("two_implementations", "procedure P() returns(r:int); ensures r==1; "
     "implementation P() returns(s:int) { s:=1; } "
     "implementation P() returns(s:int) { s:=2; }", False),
    ("inline_and_separate", "procedure P() returns(r:int) ensures r==1; { r:=1; } "
     "implementation P() returns(s:int) { s:=2; }", False),
    ("independent_labels", "procedure P(); "
     "implementation P() { var a:int; L: a:=1; assert a==1; } "
     "implementation P() { var a:bool; L: a:=true; assert a; }", True),
    ("prefix_counterexample", "procedure P(); implementation P() { assert false; assume false; } "
     "implementation P() { assume false; }", False),
    ("return_ensures", "procedure P() returns(r:int); ensures r>0; "
     "implementation P() returns(s:int) { s:=0; return; s:=1; }", False),
    ("old_output_identity", "procedure P() returns(r:int); ensures old(r)==2; "
     "implementation P() returns(s:int) { s:=2; }", True),
    ("map_output", "procedure P(m:[int]int) returns(r:[int]int); ensures r[2]==m[1]; "
     "implementation P(a:[int]int) returns(b:[int]int) { b:=a; b[2]:=a[1]; }", True),
    ("loop_contract", "procedure P(n:int) returns(r:int); requires n>=0; ensures r==n; "
     "implementation P(k:int) returns(s:int) { s:=0; "
     "while(s<k) invariant 0<=s && s<=k; { s:=s+1; } }", True),
]


@pytest.mark.parametrize("horn", [False, True], ids=["vc", "horn"])
@pytest.mark.parametrize("name,source,verified", CASES, ids=[c[0] for c in CASES])
def test_implementation_contract(name, source, verified, horn):
    solver = z3.SolverFor("HORN") if horn else z3.Solver()
    solver.set(timeout=10000)
    # Independent SMT-LIB parsing is part of the check, including all sorts.
    solver.from_string(script(source, horn))
    expected = (z3.sat if verified else z3.unsat) if horn else (z3.unsat if verified else z3.sat)
    assert solver.check() == expected, name


def test_renamed_contract_source_counterexample():
    source = next(c[1] for c in CASES if c[0] == "swapped_bad")
    solver = z3.Solver()
    solver.from_string(script(source))
    assert solver.check() == z3.sat
    model = solver.model()
    first = model.eval(z3.Int("y"), model_completion=True).as_long()
    second = model.eval(z3.Int("x"), model_completion=True).as_long()
    # Execute the source body w:=x on the model's implementation arguments;
    # declaration formals (x,y) correspond positionally to body formals (y,x).
    assert first < second
    source_result = second
    assert source_result != first


@pytest.mark.parametrize("horn", [False, True], ids=["vc", "horn"])
def test_quantifier_shadows_declaration_formal(horn):
    source = ("procedure P(x:int) returns(r:int); ensures "
              "(forall x:int :: x==x) && r==x; "
              "implementation P(y:int) returns(z:int) { z:=y; }")
    solver = z3.SolverFor("HORN") if horn else z3.Solver()
    solver.set(timeout=10000)
    solver.from_string(script(source, horn))
    assert solver.check() == (z3.sat if horn else z3.unsat)
