"""Explicit frame inference, checked against independent VC/Horn decisions."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def translate(source, *, horn=False, infer=True):
    options = {"chc": "1"} if horn else {}
    if infer:
        options["infer_modifies"] = "1"
    return sp.translate(source=source, language="boogie", options=options)


def check(source, verified, *, horn=False):
    result = translate(source, horn=horn)
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.SolverFor("HORN") if horn else z3.Solver()
    solver.set(timeout=10000)
    solver.from_string(result.to_smt2())
    expected = (z3.sat if verified else z3.unsat) if horn else (z3.unsat if verified else z3.sat)
    assert solver.check() == expected, solver.reason_unknown()
    return result


CASES = [
    ("direct_write", "var g:int; procedure P() ensures g==1; {g:=1;}", True),
    ("parallel_write", "var g,h:int; procedure P() ensures g==2 && h==1; "
     "{g,h:=1,2; g,h:=h,g;}", True),
    ("havoc_counterexample", "var g:int; procedure P() requires g==0; "
     "{havoc g; assert g==0;}", False),
    ("map_deep_lhs", "var m:[int][int]int; procedure P() requires m[2][4]==9; "
     "{m[2][3]:=7; assert m[2][3]==7 && m[2][4]==9;}", True),
    ("call_result_global", "var g,h:int; procedure Value() returns(r:int); ensures r==3; "
     "procedure Main() requires h==7; {call g:=Value(); assert g==3 && h==7;}", True),
    ("transitive_frame", "var g,h:int; procedure Main() requires g==0 && h==7; "
     "{call Middle(); assert g==1 && h==7;} "
     "procedure Middle() ensures g==old(g)+1; {call Leaf();} "
     "procedure Leaf() ensures g==old(g)+1; {g:=g+1;}", True),
    ("transitive_counterexample", "var g,h:int; procedure Main() requires g==0 && h==7; "
     "{call Middle(); assert g==0 && h==7;} "
     "procedure Middle() ensures g==1; {call Leaf();} "
     "procedure Leaf() ensures g==1; {g:=1;}", False),
    ("external_declared_effect", "var g,h:int; procedure External(); modifies g; ensures g==1; "
     "procedure Main() requires h==7; {call External(); assert g==1 && h==7;}", True),
    ("implementation_before_declaration", "implementation B(v:int) {g:=v;} "
     "procedure Main() {call B(3); assert g==3;} "
     "procedure B(x:int); ensures g==x; var g:int;", True),
    ("branch_union", "var g,h,k:int; procedure Branch(b:bool) "
     "ensures k==old(k); {if(b){g:=1;}else{h:=2;}} "
     "procedure Main(b:bool) requires k==9; {call Branch(b); assert k==9;}", True),
    ("loop_body", "var g:int; procedure P(n:int) requires n>=0; ensures g==n; "
     "{g:=0; while(g<n) invariant 0<=g && g<=n; {g:=g+1;}}", True),
    ("goto_body", "var g:int; procedure P() ensures g==1; "
     "{goto Update; End: return; Update: g:=1; goto End;}", True),
    ("local_writes_are_not_global_effects", "var g:int; procedure P() "
     "{var x:int; x:=3; havoc x;} procedure Main() requires g==7; "
     "{call P(); assert g==7;}", True),
    ("multiple_implementations_union", "var g,h,k:int; procedure P(); "
     "implementation P(){g:=1;} implementation P(){h:=2;} "
     "procedure Main() requires k==7; {call P(); assert k==7;}", True),
    ("recursive_closure", "var g,h:int; procedure Main(n:int) requires h==8; "
     "{call P(n); assert h==8;} procedure P(n:int) "
     "{if(n>0){call Q(n-1);}} procedure Q(n:int) "
     "{g:=1; if(n>0){call P(n-1);}}", True),
    ("free_only_external_permission", "var g:int; procedure P(); free modifies g; "
     "procedure Main() requires g==7; {call P(); assert g==7;}", True),
    ("actual_write_under_free_clause", "var g:int; procedure P(); free modifies g; "
     "ensures g==1; implementation P(){g:=1;} "
     "procedure Main() requires g==0; {call P(); assert g==0;}", False),
    ("free_call_effect", "var g:int; procedure P(); requires false; modifies g; ensures g==1; "
     "procedure Main(){free call P(); assert g==1;}", True),
]


@pytest.mark.parametrize("horn", [False, True], ids=["vc", "horn"])
@pytest.mark.parametrize("name,source,verified", CASES, ids=[c[0] for c in CASES])
def test_inferred_frames_preserve_program_decisions(name, source, verified, horn):
    check(source, verified, horn=horn)


def reports(result):
    return {c.site.rsplit(":", 1)[-1]: c.rationale for c in result.report.choices
            if c.strategy == "call-graph-modifies-fixed-point"}


def test_recursive_multiple_implementation_frames_report_actual_fixed_point():
    source = ("var g,h,k:int; procedure P(); procedure Q(); "
              "implementation P(){call Q();} implementation Q(){g:=1; call P();} "
              "implementation Q(){h:=2;} procedure ReadOnly(){assert k==k;}")
    result = translate(source)
    assert result.ok, [d.message for d in result.diagnostic_items]
    rows = reports(result)
    assert "direct global writes={}" in rows["P"]
    assert "direct global writes={g, h}" in rows["Q"]
    assert "checked frame={g, h}" in rows["P"]
    assert "checked frame={g, h}" in rows["Q"]
    assert "checked frame={}" in rows["ReadOnly"]


def test_explicit_larger_contract_frame_is_not_narrowed_to_body_writes():
    # Modular VC call semantics must still havoc explicitly declared h, even
    # though this one implementation only writes g. Narrowing the declaration
    # would falsely verify the caller's h==0 assertion.
    result = check("var g,h:int; procedure P(); modifies h; implementation P(){g:=1;} "
                   "procedure Main() requires h==0; {call P(); assert h==0;}", False)
    assert "declared checked={h}" in reports(result)["P"]
    assert "checked frame={g, h}" in reports(result)["P"]


@pytest.mark.parametrize("horn", [False, True], ids=["vc", "horn"])
@pytest.mark.parametrize("source", [
    "var g:int; procedure P(){g:=1;}",
    "var g:int; procedure P(); modifies g; procedure Main(){call P();}",
])
def test_default_still_rejects_missing_frame(source, horn):
    result = translate(source, horn=horn, infer=False)
    assert not result.ok
    assert any("modifies" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("option", ["", "0", "true", "2"])
def test_invalid_option_value_is_rejected(option):
    result = sp.translate(source="procedure P(){}", language="boogie",
                          options={"infer_modifies": option})
    assert not result.ok
    assert any("infer_modifies" in d.message for d in result.diagnostic_items)


INVALID = [
    ("constant_write", "const c:int; procedure P(){c:=1;}", "immutable"),
    ("undeclared_write", "procedure P(){g:=1;}", "declared"),
    ("formal_write", "procedure P(x:int){x:=1;}", "input"),
    ("local_shadow", "var g:int; procedure P(){var g:int; g:=1;}", "shadow"),
    ("invalid_frame", "const c:int; procedure P(); modifies c; procedure Main(){}", "mutable global"),
    ("duplicate_declared_frame", "var g:int; procedure P() modifies g,g; {g:=1;}", "more than once"),
    ("undeclared_call", "procedure P(){call Missing();}", "undeclared"),
    ("undeclared_implementation", "implementation P(){}", "no procedure declaration"),
    ("async", "procedure P(); procedure Main(){async call P();}", "async"),
]


@pytest.mark.parametrize("name,source,message", INVALID, ids=[c[0] for c in INVALID])
def test_inference_does_not_disable_source_errors(name, source, message):
    result = translate(source)
    assert not result.ok
    assert any(message in d.message for d in result.diagnostic_items)


def test_inference_scope_is_per_translation_and_default_report_has_no_inference():
    source = "var g:int; procedure P(){g:=1;}"
    assert translate(source).ok
    default = translate(source, infer=False)
    assert not default.ok
    explicit = translate("var g:int; procedure P() modifies g; {g:=1;}", infer=False)
    assert explicit.ok
    assert not reports(explicit)
