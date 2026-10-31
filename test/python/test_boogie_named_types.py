"""Nominal types and alias resolution, with independent VC satisfiability."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

CASES = [
    ("copy", "type Ref;procedure P(x:Ref) returns(y:Ref) ensures y==x; {y:=x;}", "unsat"),
    ("forward", "procedure P(x:Ref) returns(y:Ref) ensures y==x; {y:=x;} type Ref;", "unsat"),
    ("forward_alias", "type Handle=Ref;procedure P(x:Handle) returns(y:Ref) ensures y==x; {y:=x;} type Ref;", "unsat"),
    ("alias_chain", "type A=B;type B=C;type C=int;procedure P(x:A) returns(y:C) ensures y==x+1; {y:=x+1;}", "unsat"),
    ("alias_bad_post", "type A=int;procedure P(x:A) returns(y:int) ensures y==x; {y:=x+1;}", "sat"),
    ("grouped_nominal", "type Ref,Field;const r:Ref;const f:Field;procedure P(){assert r==r && f==f;}", "unsat"),
    ("unique", "type Ref;const unique a,b:Ref;procedure P(){assert a!=b;}", "unsat"),
    ("unique_alias", "type Ref;type Handle=Ref;const unique a:Ref;const unique b:Handle;procedure P(){assert a!=b;}", "unsat"),
    ("no_implicit_unique", "type Ref;const a,b:Ref;procedure P(){assert a!=b;}", "sat"),
    ("no_implicit_singleton", "type Ref;const a,b:Ref;procedure P(){assert a==b;}", "sat"),
    ("havoc", "type Ref;const unique a,b:Ref;procedure P(){var x:Ref;x:=a;havoc x;assert x==a;}", "sat"),
    ("global_old", "type Ref;var g:Ref;procedure P(x:Ref) returns(y:Ref) modifies g;ensures y==old(g) && g==x;{y:=g;g:=x;}", "unsat"),
    ("named_function", "type Ref;function f(x:Ref):Ref {x} procedure P(x:Ref){assert f(x)==x;}", "unsat"),
    ("map_alias", "type Ref;type Memory=[Ref]int;procedure P(a:Memory,x:Ref) returns(b:Memory) ensures b[x]==7;{b:=a;b[x]:=7;}", "unsat"),
    ("quantifier", "type Ref;procedure P(){assert (forall x:Ref :: x==x);}", "unsat"),
    ("call_contract", "type Ref;procedure Copy(x:Ref) returns(y:Ref);ensures y==x;procedure P(x:Ref){var y:Ref;call y:=Copy(x);assert y==x;}", "unsat"),
    ("extern_annotation", "type {:extern} Ref;procedure P(x:Ref){assert x==x;}", "unsat"),
    ("unused_nominal", "type Ref;procedure P(){assert true;}", "unsat"),
]


@pytest.mark.parametrize("name,source,expected", CASES, ids=[r[0] for r in CASES])
def test_named_type_semantics(name, source, expected):
    translated = sp.translate(source=source, language="boogie")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    assert str(solver.check()) == expected, solver.reason_unknown()


REJECTIONS = [
    ("nominal_mismatch", "type A,B;procedure P(x:A) returns(y:B){y:=x;}"),
    ("duplicate", "type A;type A;procedure P(){}"),
    ("cycle", "type A=B;type B=A;procedure P(){}"),
    ("recursive_map_alias", "type A=[int]A;procedure P(){}"),
    ("unknown_alias", "type A=Unknown;procedure P(){}"),
    ("builtin_redeclaration", "type int;procedure P(){}"),
    ("parameterized_type", "type Map K V;procedure P(){}"),
    ("semantic_attribute", 'type {:builtin "RoundingMode"} R;procedure P(){}'),
    ("datatype_attribute", 'type {:datatype} D;procedure P(){}'),
    ("malformed_alias", "type A=int int;procedure P(){}"),
]


@pytest.mark.parametrize("name,source", REJECTIONS, ids=[r[0] for r in REJECTIONS])
def test_invalid_or_unimplemented_type_declaration_is_explicit(name, source):
    translated = sp.translate(source=source, language="boogie")
    assert not translated.ok
    assert translated.diagnostic_items


@pytest.mark.parametrize("source", [CASES[0][1], CASES[2][1], CASES[7][1], CASES[11][1]])
def test_named_type_horn_output_parses_completely(source):
    translated = sp.translate(source=source, language="boogie", options={"chc": "1"})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    z3.parse_smt2_string(translated.to_smt2(), ctx=context)
