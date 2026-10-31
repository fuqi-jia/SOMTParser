"""Complete extensional arrays for Boogie's interpreted map operations."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def check_vc(source, expected):
    translated = sp.translate(source=source, language="boogie")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    text = translated.to_smt2()
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(text, ctx=context))
    assert str(solver.check()) == expected, solver.reason_unknown()
    return text


CONSTANT_CASES = [
    ('function {:builtin "MapConst"} C(bool):[int]bool; procedure P(i:int){assert C(true)[i];}', "unsat"),
    ('function {:builtin "MapConst"} C(bool):[int]bool; procedure P(i:int){assert C(false)[i];}', "sat"),
    ('function {:builtin "MapConst"} C(int):[int]int; procedure P(i:int,v:int){assert C(v)[i]==v;}', "unsat"),
    ('function {:builtin "MapConst"} C(real):[int]real; procedure P(i:int,v:real){assert C(v)[i]==v;}', "unsat"),
    ('function {:builtin "MapConst"} C(bv8):[bv8]bv8; procedure P(i:bv8){assert C(255bv8)[i]==255bv8;}', "unsat"),
    ('type Ref; function {:builtin "MapConst"} C(Ref):[Ref]Ref; procedure P(i:Ref,v:Ref){assert C(v)[i]==v;}', "unsat"),
    ('function {:builtin "MapConst"} C([int]int):[bool][int]int; procedure P(m:[int]int){assert C(m)[true]==m;}', "unsat"),
    ('function {:builtin "MapConst"} C(int):[int]int; procedure P(m:[int]int,v:int){assume (forall i:int :: m[i]==v);assert C(v)==m;}', "unsat"),
]


@pytest.mark.parametrize("source,expected", CONSTANT_CASES)
def test_constant_map_preserves_every_cell_and_whole_array(source, expected):
    text = check_vc(source, expected)
    assert "(as const (Array " in text
    assert "(declare-fun C " not in text


BOOL_MAPS = ('function {:builtin "MapImp"} I([int]bool,[int]bool):[int]bool;'
             'function {:builtin "MapConst"} C(bool):[int]bool;')
IMPLICATION_CASES = [
    "procedure P(a:[int]bool,b:[int]bool,i:int){assert I(a,b)[i]==(a[i] ==> b[i]);}",
    "procedure P(a:[int]bool){assert I(a,a)==C(true);}",
    "procedure P(a:[int]bool){assert I(C(false),a)==C(true);}",
    "procedure P(a:[int]bool){assert I(C(true),a)==a;}",
    "procedure P(){assert (forall a:[int]bool,b:[int]bool,i:int :: I(a,b)[i]==(a[i] ==> b[i]));}",
    "procedure P(a:[int]bool,b:[int]bool,i:int,j:int){assume i!=j;assert I(a[i:=true],b[i:=false])[i]==false && I(a[i:=true],b[i:=false])[j]==I(a,b)[j];}",
]


@pytest.mark.parametrize("body", IMPLICATION_CASES)
def test_implication_map_including_array_equality_and_bound_operands(body):
    text = check_vc(BOOL_MAPS + body, "unsat")
    assert "forall" in text and "select" in text and "=>" in text


def test_implication_map_counterexample_with_finite_index_domain():
    # A SAT control over the entire finite array domain, not selected cells
    # without the global definition. It detects vacuous/inconsistent axioms.
    text = check_vc('function {:builtin "MapImp"} I([bool]bool,[bool]bool):[bool]bool;'
                    'procedure P(a:[bool]bool,b:[bool]bool){'
                    'assume a[false] && !b[false];assert I(a,b)[false];}', "sat")
    prefix = ('function {:builtin "MapImp"} I([bool]bool,[bool]bool):[bool]bool;'
              'function {:builtin "MapConst"} C(bool):[bool]bool;')
    assert "forall" not in text and "(declare-fun I " not in text
    # Both cells and the complete array remain exact, including bound indices.
    check_vc(prefix + 'procedure P(a:[bool]bool,b:[bool]bool){'
             'assume a==b;assert I(a,b)==C(true);}', "unsat")
    check_vc(prefix + 'procedure P(a:[bool]bool,b:[bool]bool){'
             'assert (forall i:bool :: I(a,b)[i]==(a[i] ==> b[i]));}', "unsat")


INVALID_SIGNATURES = [
    'function {:builtin "MapConst"} C(int):[int]bool;',
    'function {:builtin "MapConst"} C(bool,bool):[int]bool;',
    'function {:builtin "MapImp"} I([int]bool,[bool]bool):[int]bool;',
    'function {:builtin "MapImp"} I([int]bool,[int]bool):[bool]bool;',
    'function {:builtin "MapImp"} I([int]int,[int]int):[int]int;',
]


@pytest.mark.parametrize("declaration", INVALID_SIGNATURES)
def test_interpreted_map_signature_must_match(declaration):
    translated = sp.translate(source=declaration + "procedure P(){}", language="boogie")
    assert not translated.ok
    assert any("signature" in d.message for d in translated.diagnostic_items)


def test_implication_array_axiom_is_not_mislabeled_as_horn():
    translated = sp.translate(source=BOOL_MAPS + "procedure P(){}", language="boogie",
                              options={"chc": "1"})
    assert not translated.ok
    assert any("not a Horn clause" in d.message for d in translated.diagnostic_items)
