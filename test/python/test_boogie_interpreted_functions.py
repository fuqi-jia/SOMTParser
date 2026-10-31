"""Semantic function attributes and the generated SMACK expression grammar.

VC satisfiability is checked independently after complete SMT parsing. A SAT
negative control for every concrete operator prevents tests that only detect
syntactically valid output or a vacuously inconsistent translation.
"""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

# (attribute, argument types, result type, actual terms, source expected value)
OPERATORS = [
    ("bvadd", "bv8,bv8", "bv8", "255bv8,1bv8", "0bv8"),
    ("bvsub", "bv8,bv8", "bv8", "0bv8,1bv8", "255bv8"),
    ("bvmul", "bv8,bv8", "bv8", "128bv8,2bv8", "0bv8"),
    ("bvudiv", "bv8,bv8", "bv8", "255bv8,2bv8", "127bv8"),
    ("bvurem", "bv8,bv8", "bv8", "255bv8,2bv8", "1bv8"),
    ("bvsdiv", "bv8,bv8", "bv8", "249bv8,3bv8", "254bv8"),
    ("bvsrem", "bv8,bv8", "bv8", "249bv8,3bv8", "255bv8"),
    ("bvsmod", "bv8,bv8", "bv8", "249bv8,3bv8", "2bv8"),
    ("bvneg", "bv8", "bv8", "1bv8", "255bv8"),
    ("bvnot", "bv8", "bv8", "15bv8", "240bv8"),
    ("bvand", "bv8,bv8", "bv8", "170bv8,15bv8", "10bv8"),
    ("bvor", "bv8,bv8", "bv8", "160bv8,15bv8", "175bv8"),
    ("bvxor", "bv8,bv8", "bv8", "170bv8,15bv8", "165bv8"),
    ("bvnand", "bv8,bv8", "bv8", "170bv8,15bv8", "245bv8"),
    ("bvnor", "bv8,bv8", "bv8", "160bv8,15bv8", "80bv8"),
    ("bvxnor", "bv8,bv8", "bv8", "170bv8,15bv8", "90bv8"),
    ("bvshl", "bv8,bv8", "bv8", "129bv8,1bv8", "2bv8"),
    ("bvlshr", "bv8,bv8", "bv8", "129bv8,1bv8", "64bv8"),
    ("bvashr", "bv8,bv8", "bv8", "129bv8,1bv8", "192bv8"),
    ("bvult", "bv8,bv8", "bool", "255bv8,1bv8", "false"),
    ("bvule", "bv8,bv8", "bool", "255bv8,255bv8", "true"),
    ("bvugt", "bv8,bv8", "bool", "255bv8,1bv8", "true"),
    ("bvuge", "bv8,bv8", "bool", "255bv8,255bv8", "true"),
    ("bvslt", "bv8,bv8", "bool", "255bv8,1bv8", "true"),
    ("bvsle", "bv8,bv8", "bool", "255bv8,255bv8", "true"),
    ("bvsgt", "bv8,bv8", "bool", "255bv8,1bv8", "false"),
    ("bvsge", "bv8,bv8", "bool", "255bv8,255bv8", "true"),
    ("concat", "bv4,bv8", "bv12", "10bv4,18bv8", "2578bv12"),
    ("(_ zero_extend 8)", "bv8", "bv16", "255bv8", "255bv16"),
    ("(_ sign_extend 8)", "bv8", "bv16", "255bv8", "65535bv16"),
    ("(_ extract 7 4)", "bv8", "bv4", "171bv8", "10bv4"),
    ("bv2int", "bv8", "int", "255bv8", "255"),
    ("sbv_to_int", "bv8", "int", "255bv8", "-1"),
    ("(_ int2bv 8)", "int", "bv8", "-1", "255bv8"),
    ("div", "int,int", "int", "-7,3", "-3"),
    ("mod", "int,int", "int", "-7,-3", "2"),
    ("rem", "int,int", "int", "-7,3", "2"),
    ("rem", "int,int", "int", "-7,-3", "-2"),
    ("bvudiv", "bv8,bv8", "bv8", "1bv8,0bv8", "255bv8"),
    ("bvshl", "bv8,bv8", "bv8", "1bv8,8bv8", "0bv8"),
    ("(_ zero_extend 0)", "bv8", "bv8", "255bv8", "255bv8"),
]


def check_vc(source, expected):
    translated = sp.translate(source=source, language="boogie")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    assert str(solver.check()) == expected, solver.reason_unknown()
    return translated.to_smt2()


@pytest.mark.parametrize("operator,arguments,result,terms,value", OPERATORS)
@pytest.mark.parametrize("negate", [False, True], ids=["valid", "counterexample"])
def test_interpreted_operator_semantics(operator, arguments, result, terms, value, negate):
    attribute = "bvbuiltin" if operator.startswith("bv") and operator not in {"bv2int"} else "builtin"
    relation = "!=" if negate else "=="
    source = (
        f'function {{:{attribute} "{operator}"}} $op({arguments}):{result};'
        f"procedure P(){{assert $op({terms}){relation}({value});}}"
    )
    smt = check_vc(source, "sat" if negate else "unsat")
    assert "(declare-fun $op" not in smt
    assert "(declare-fun |$op|" not in smt


SEMANTICS = [
    ("forward_function", "function f(x:int):int {g(x)} function g(x:int):int {x+1} procedure P(x:int){assert f(x)==x+1;}", "unsat"),
    ("forward_constant", "function f():int {c} const c:int; axiom c==7; procedure P(){assert f()==7;}", "unsat"),
    ("forward_wrong_post", "function f(x:int):int {g(x)} function g(x:int):int {x+1} procedure P(){assert f(0)==0;}", "sat"),
    ("function_scope", "function f(x:int):int {g(x)} function g(x:int):int {x+1} procedure P(x:int){assert f(x)==x+1;}", "unsat"),
    ("generated_names", "const $0.foo:int; axiom $0.foo==0; procedure $P.main() {var .tmp#x:int; .tmp#x:=$0.foo+1; assert .tmp#x==1;}", "unsat"),
    ("bv_literal_spacing", "procedure P(){assert 000255 bv8==255bv8;}", "unsat"),
    ("wide_literal", "procedure P(){assert 340282366920938463463374607431768211455bv128!=0bv128;}", "unsat"),
    ("concat_order", "procedure P(){assert 1bv4 ++ 2bv4 == 18bv8;}", "unsat"),
    ("concat_grouping", "procedure P(){assert 1bv4 ++ 2bv4 ++ 3bv4 == 291bv12;}", "unsat"),
    ("extract_upper_excluded", "procedure P(x:bv16){assert (x[16:8] ++ x[8:0])==x;}", "unsat"),
    ("extract_value", "procedure P(){assert (171bv8)[8:4]==10bv4 && (171bv8)[4:0]==11bv4;}", "unsat"),
    ("extract_counterexample", "procedure P(x:bv16){assert (x[8:0] ++ x[16:8])==x;}", "sat"),
    ("store_value", "procedure P(m:[int]int){assert m[1:=7][1]==7;}", "unsat"),
    ("store_frame", "procedure P(m:[int]int){assert m[1:=7][2]==m[2];}", "unsat"),
    ("store_not_mutation", "procedure P(m:[int]int){var n:[int]int;n:=m[1:=7];assert m[1]==7;}", "sat"),
    ("store_overwrite", "procedure P(m:[int]int){assert m[1:=7][1:=9][1]==9;}", "unsat"),
    ("nested_store", "procedure P(m:[int][int]int){assert m[1:=m[1][2:=7]][1][2]==7;}", "unsat"),
    ("annotation_order", 'function {:inline} {:bvbuiltin "bvadd"} {:source "foo"} f(bv8,bv8):bv8;procedure P(){assert f(255bv8,1bv8)==0bv8;}', "unsat"),
    ("rem_zero_totalized", 'function {:builtin "rem"} r(int,int):int;procedure P(x:int){assert r(x,0)==x mod 0;}', "unsat"),
    ("mod_zero_not_forced", 'function {:builtin "mod"} r(int,int):int;procedure P(x:int){assert r(x,0)==0;}', "sat"),
    ("function_formal_hint", 'function f({:source "x"} x:int):int {x} procedure P(){assert f(2)==2;}', "unsat"),
]


@pytest.mark.parametrize("name,source,expected", SEMANTICS, ids=[row[0] for row in SEMANTICS])
def test_generated_expression_semantics(name, source, expected):
    check_vc(source, expected)


REJECTIONS = [
    ('function {:bvbuiltin "mystery"} f(bv8):bv8;procedure P(){}', "unsupported builtin"),
    ('function {:builtin "MapImp"} f([int]int,[int]int):[int]int;procedure P(){}', "signature"),
    ('function {:bvbuiltin "bvadd"} f(int,int):int;procedure P(){}', "signature"),
    ('function {:bvbuiltin "bvadd"} f(bv8,bv16):bv8;procedure P(){}', "signature"),
    ('function {:bvbuiltin "bvadd"} f(bv8,bv8):bv16;procedure P(){}', "signature"),
    ('function {:bvbuiltin "bvult"} f(bv8,bv8):bv8;procedure P(){}', "signature"),
    ('function {:builtin "(_ int2bv 0)"} f(int):bv8;procedure P(){}', "signature"),
    ('function {:bvbuiltin "(_ extract 8 0)"} f(bv8):bv8;procedure P(){}', "signature"),
    ('function {:bvbuiltin "(_ extract 1 2)"} f(bv8):bv1;procedure P(){}', "signature"),
    ('function {:bvbuiltin "(_ zero_extend 1) trailing"} f(bv8):bv9;procedure P(){}', "signature"),
    ('function {:bvbuiltin "bvadd"} {:builtin "bvsub"} f(bv8,bv8):bv8;procedure P(){}', "duplicate"),
    ('function {:bvbuiltin 12} f(bv8):bv8;procedure P(){}', "operator string"),
    ('function {:bvbuiltin "bvnot"} f(x:bv8):bv8 {x} procedure P(){}', "defining body"),
    ('function {:bvbuiltin "bvnot"} f(bv8):bv8;procedure P(){assert f(1)==0bv8;}', "argument"),
    ('procedure P(){assert 256bv8==0bv8;}', "out-of-range"),
    ('procedure P(){assert 0bv0==0bv0;}', "invalid width"),
    ('procedure P(x:bv999999999999999999999999999999){}', "width"),
    ('procedure P(x:bv8oops){}', "width"),
    ('procedure P(x:bv8){assert x[9:0]==x;}', "extraction"),
    ('procedure P(x:bv8){assert x[4:4]==x;}', "extraction"),
    ('procedure P(x:bv8){assert x[1:2]==x;}', "extraction"),
    ('procedure P(x:bv8,n:int){assert x[n:0]==x;}', "extraction"),
    ('procedure P(m:[int]int){assert m[1:=true][1]==0;}', ""),
    ('procedure P(){assert 1 ++ 2 == 3;}', "concatenation"),
    ('function f():int {g} var g:int;procedure P(){}', "mutable global"),
    ('function f(x:int,x:int):int {x} procedure P(){}', "duplicate function parameter"),
]


@pytest.mark.parametrize("source,diagnostic", REJECTIONS)
def test_semantic_attributes_and_invalid_terms_are_never_silently_erased(source, diagnostic):
    translated = sp.translate(source=source, language="boogie")
    assert not translated.ok
    assert any(diagnostic in d.message for d in translated.diagnostic_items)


# Exact lines from Corral/SMACK test_list.bpl; see packaged component provenance.
SMACK_COMPONENT = 'type i8 = int;\ntype i64 = int;\ntype ref = i64;\nconst $1.ref: ref;\naxiom ($1.ref == 1);\nfunction {:inline} $p2i.ref.i8(p: ref) returns (i8) { $trunc.i64.i8(p) }\nfunction {:inline} $add.ref(p1: ref, p2: ref) returns (ref) { $add.i64(p1, p2) }\nfunction {:inline} $add.i64(i1: i64, i2: i64) returns (i64) {i1 + i2}\nfunction {:inline} $trunc.i64.i8(i: i64) returns (i8) {i}\nfunction {:inline} $load.bytes.bv16(M: [ref] bv8, p: ref) returns (bv16){ M[$add.ref(p, $1.ref)] ++ M[p] }\nfunction {:inline} $store.bytes.bv16(M:[ref]bv8, p:ref, v:bv16) returns ([ref]bv8) {M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]}\n'


@pytest.mark.parametrize("wrong", [False, True], ids=["valid", "counterexample"])
def test_original_smack_memory_helpers(wrong):
    # Little-endian store/load roundtrip and the unchanged integer abstraction:
    # this original generator's i64 -> i8 helper is identity, not modulo 256.
    assertion = "$load.bytes.bv16($store.bytes.bv16(m,p,v),p)==v && $p2i.ref.i8(257)==257"
    if wrong:
        assertion = "$p2i.ref.i8(257)==1"
    check_vc(SMACK_COMPONENT + "procedure $qualification(m:[ref]bv8,p:ref,v:bv16){assert " + assertion + ";}",
             "sat" if wrong else "unsat")


@pytest.mark.parametrize("operator", ["bvadd", "bvslt"])
def test_interpreted_builtin_horn_script_parses(operator):
    result = "bool" if operator == "bvslt" else "bv8"
    source = f'function {{:bvbuiltin "{operator}"}} f(bv8,bv8):{result};procedure P(){{assert f(1bv8,2bv8)==f(1bv8,2bv8);}}'
    translated = sp.translate(source=source, language="boogie", options={"chc":"1"})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    z3.parse_smt2_string(translated.to_smt2(), ctx=context)
