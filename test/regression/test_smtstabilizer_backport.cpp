// Regression tests for the fixes and features brought over from the
// SMTStabilizer fork of SOMTParser (https://github.com/shaowei-cai-group/SMTStabilizer).
//
// Each case below either pins a printer/parser bug that used to produce
// unparsable output, or covers a theory/annotation feature that the parser
// previously rejected outright.

#include <iostream>
#include <string>
#include <vector>

#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

namespace {

// Parse a single expression under the given declarations and print it back.
std::string roundTrip(const std::string& decls, const std::string& expr) {
    ParserPtr parser = newParser();
    if (!decls.empty()) parser->parseStr(decls);
    auto node = parser->mkExpr(expr);
    VERIFY(node);
    return parser->toString(node);
}

// Parse a whole script and print back its first assertion.
std::string firstAssertion(const std::string& script, bool preserve_annotations = false) {
    ParserPtr parser = newParser();
    parser->setOption(std::string("preserve_annotations"),
                      std::string(preserve_annotations ? "true" : "false"));
    parser->parseStr(script);
    auto assertions = parser->getAssertions();
    VERIFY(!assertions.empty());
    return parser->toString(assertions[0]);
}

// Print a term, feed the printed text back to a fresh parser, and print again.
// Every bug fixed here was of the form "we emit something we cannot read back",
// so asserting on the first print alone would not have caught them: the tester
// bug produced (is-nil l), which our own parser happens to accept, and the
// RegLan bug produced a sort spelling it does not.  Returns the printed text.
std::string reparse(const std::string& decls, const std::string& expr) {
    ParserPtr p1 = newParser();
    if (!decls.empty()) p1->parseStr(decls);
    auto n1 = p1->mkExpr(expr);
    VERIFY(n1 && !n1->isErr());
    const std::string once = p1->toString(n1);

    ParserPtr p2 = newParser();
    if (!decls.empty()) p2->parseStr(decls);
    auto n2 = p2->mkExpr(once);
    VERIFY(n2 && !n2->isErr());
    const std::string twice = p2->toString(n2);
    if (once != twice) {
        std::cerr << "FAILED re-parse is not stable\n  input : " << expr
                  << "\n  print : " << once << "\n  again : " << twice << "\n";
        std::abort();
    }
    return once;
}

// A malformed term must be diagnosed rather than accepted or crashing.  The
// parser reports through err_all and then throws, so either an error node or
// an exception counts; silently returning a well-formed node does not.
void expectRejected(const std::string& what, const std::string& decls, const std::string& expr) {
    ParserPtr p = newParser();
    if (!decls.empty()) p->parseStr(decls);
    bool rejected = false;
    try {
        auto n = p->mkExpr(expr);
        rejected = (!n || n->isErr() || n->isUnknown());
    } catch (const std::exception&) {
        rejected = true;
    }
    if (!rejected) {
        std::cerr << "FAILED " << what << ": expected rejection of " << expr << "\n";
        std::abort();
    }
    std::cout << "  ok: rejected " << what << "\n";
}

void expectEq(const std::string& what, const std::string& got, const std::string& want) {
    if (got != want) {
        std::cerr << "FAILED " << what << "\n  got : " << got << "\n  want: " << want << "\n";
        std::abort();
    }
    std::cout << "  ok: " << what << " -> " << got << "\n";
}

// ── A1/A2: bv<->int conversions used to print as UNKNOWN_KIND, and the
// indexed forms lost their ((_ ...) ...) shape entirely. ──────────────────
void test_bv_int_conversions() {
    std::cout << "-- bitvector/integer conversions --\n";
    const std::string bv_decl = "(declare-fun x () (_ BitVec 8))";
    const std::string int_decl = "(declare-fun i () Int)";

    expectEq("bv2int", roundTrip(bv_decl, "(bv2int x)"), "(bv2nat x)");
    expectEq("bv2nat", roundTrip(bv_decl, "(bv2nat x)"), "(bv2nat x)");
    expectEq("int2bv indexed", roundTrip(int_decl, "((_ int2bv 8) i)"), "((_ int2bv 8) i)");
    // B: the indexed nat2bv form used to abort on a 2-parameter assertion.
    expectEq("nat2bv indexed", roundTrip(int_decl, "((_ nat2bv 8) i)"), "((_ nat2bv 8) i)");

    // C3: SMT-LIB 2.7 spellings.
    expectEq("ubv_to_int", roundTrip(bv_decl, "(ubv_to_int x)"), "(ubv_to_int x)");
    expectEq("sbv_to_int", roundTrip(bv_decl, "(sbv_to_int x)"), "(sbv_to_int x)");
}

// ── A3: the regex sort printed as "(RegEx String)", which the parser's own
// sort reader (which accepts "RegLan") could not read back. ───────────────
void test_reglan_sort_round_trips() {
    std::cout << "-- RegLan sort --\n";
    ParserPtr parser = newParser();
    parser->parseStr("(declare-fun r () RegLan)");
    auto vars = parser->getVariables();
    VERIFY(vars.size() == 1);
    const std::string printed = vars[0]->getSort()->toString();
    expectEq("RegLan sort", printed, "RegLan");

    // The printed spelling must parse back into the same sort.
    ParserPtr again = newParser();
    again->parseStr("(declare-fun r2 () " + printed + ")");
    auto vars2 = again->getVariables();
    VERIFY(vars2.size() == 1 && vars2[0]->getSort()->isReg());
}

// ── A4/C4: datatype tester and updater. ───────────────────────────────────
void test_datatype_tester_and_updater() {
    std::cout << "-- datatype tester/updater --\n";
    const std::string decls =
        "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n"
        "(declare-fun l () L)\n";

    // A4: the tester used to print in the legacy (is-nil l) form, which is not
    // SMT-LIB 2.6 syntax; both spellings must parse and print the standard one.
    expectEq("tester indexed input", roundTrip(decls, "((_ is nil) l)"), "((_ is nil) l)");
    expectEq("tester legacy input", roundTrip(decls, "(is-nil l)"), "((_ is nil) l)");

    // C4: ((_ update <selector>) t v) was rejected outright.
    expectEq("updater", roundTrip(decls, "((_ update hd) l 7)"), "((_ update hd) l 7)");
}

// ── C2: tuple theory was entirely missing; (Tuple Int Int) did not parse. ──
void test_tuple_theory() {
    std::cout << "-- tuple theory --\n";
    const std::string decls =
        "(declare-fun t () (Tuple Int Int Bool))\n"
        "(declare-fun u () UnitTuple)\n";

    ParserPtr parser = newParser();
    parser->parseStr(decls);
    for (auto& v : parser->getVariables()) {
        if (v->getName() == "t") {
            expectEq("tuple sort", v->getSort()->toString(), "(Tuple Int Int Bool)");
            VERIFY(v->getSort()->isTuple());
        }
        if (v->getName() == "u") {
            expectEq("unit tuple sort", v->getSort()->toString(), "UnitTuple");
        }
    }

    expectEq("tuple constructor", roundTrip(decls, "(tuple 1 2 true)"), "(tuple 1 2 true)");
    expectEq("tuple.unit", roundTrip(decls, "tuple.unit"), "tuple.unit");
    expectEq("tuple.select", roundTrip(decls, "((_ tuple.select 0) t)"), "((_ tuple.select 0) t)");
    expectEq("tuple.update", roundTrip(decls, "((_ tuple.update 0) t 5)"), "((_ tuple.update 0) t 5)");
    expectEq("tuple.project", roundTrip(decls, "((_ tuple.project 2 0) t)"), "((_ tuple.project 2 0) t)");

    // Element sorts must follow the tuple's field sorts.
    ParserPtr p2 = newParser();
    p2->parseStr(decls);
    auto sel = p2->mkExpr("((_ tuple.select 2) t)");
    VERIFY(sel && sel->getSort()->isBool());
    auto proj = p2->mkExpr("((_ tuple.project 2 0) t)");
    VERIFY(proj && proj->getSort()->toString() == "(Tuple Bool Int)");
}

// ── C1: quantifier annotations were parsed and then dropped, so triggers
// silently vanished from the printed formula. ─────────────────────────────
void test_quantifier_annotations() {
    std::cout << "-- quantifier annotations --\n";
    const std::string script =
        "(declare-fun f (Int) Int)\n"
        "(assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)) :qid myq :weight 5)))\n";

    // Default: annotations are dropped, exactly as before.
    expectEq("annotations dropped by default", firstAssertion(script, false),
             "(forall ((x Int)) (> (f x) 0))");

    // Opt in and they survive the round trip.
    expectEq("annotations preserved", firstAssertion(script, true),
             "(forall ((x Int)) (! (> (f x) 0) :pattern ((f x)) :qid myq :weight 5))");

    const std::string no_pattern =
        "(declare-fun f (Int) Int)\n"
        "(assert (forall ((x Int)) (! (> (f x) 1) :no-pattern (f x))))\n";
    expectEq(":no-pattern preserved", firstAssertion(no_pattern, true),
             "(forall ((x Int)) (! (> (f x) 1) :no-pattern (f x)))");

    // Unknown annotations must still be skipped rather than aborting the parse,
    // in both modes.
    const std::string unknown_kw =
        "(declare-fun f (Int) Int)\n"
        "(assert (forall ((x Int)) (! (> (f x) 2) :lblpos lbl :skolemid sk)))\n";
    expectEq("unknown annotations skipped", firstAssertion(unknown_kw, true),
             "(forall ((x Int)) (> (f x) 2))");

    // :named keeps its existing behaviour: recorded, not wrapped.
    ParserPtr parser = newParser();
    parser->setOption(std::string("preserve_annotations"), std::string("true"));
    parser->parseStr("(declare-fun p () Bool)\n(assert (! p :named a0))\n");
    expectEq(":named unchanged", parser->toString(parser->getAssertions()[0]), "p");
}

// ── D: default logic is ALL, and an unknown logic name falls back to ALL
// instead of disabling every theory. ──────────────────────────────────────
void test_logic_defaults() {
    std::cout << "-- logic defaults --\n";
    ParserPtr parser = newParser();
    expectEq("default logic", parser->getOptions()->getLogic(), "ALL");

    VERIFY(parser->getOptions()->setLogic("QF_LIA"));
    expectEq("explicit logic", parser->getOptions()->getLogic(), "QF_LIA");

    VERIFY(!parser->getOptions()->setLogic("QF_MADE_UP"));
    expectEq("unknown logic falls back", parser->getOptions()->getLogic(), "ALL");
}

// ── Commutative operands get a canonical order; equal-hash ties keep input
// order so the AST is reproducible. ───────────────────────────────────────
void test_stable_commutative_order() {
    std::cout << "-- stable commutative ordering --\n";
    const std::string decls = "(declare-fun a () Int)\n(declare-fun b () Int)\n(declare-fun c () Int)\n";
    const std::string one = roundTrip(decls, "(+ a b c)");
    expectEq("(+ a b c) == (+ c b a)", roundTrip(decls, "(+ c b a)"), one);
    expectEq("(+ a b c) == (+ b c a)", roundTrip(decls, "(+ b c a)"), one);

    // Newly recognised symmetric operators.
    const std::string bv_decls = "(declare-fun x () (_ BitVec 4))\n(declare-fun y () (_ BitVec 4))\n";
    expectEq("bvnand symmetric", roundTrip(bv_decls, "(bvnand y x)"), roundTrip(bv_decls, "(bvnand x y)"));
    expectEq("bvxnor symmetric", roundTrip(bv_decls, "(bvxnor y x)"), roundTrip(bv_decls, "(bvxnor x y)"));

    // Quantifiers must NOT be reordered: the bound-variable list stays first.
    ParserPtr parser = newParser();
    parser->parseStr("(declare-fun f (Int Int) Bool)\n(assert (forall ((x Int) (y Int)) (f x y)))\n");
    expectEq("quantifier shape kept", parser->toString(parser->getAssertions()[0]),
             "(forall ((x Int) (y Int)) (f x y))");
}

// ── C5: small utility additions. ──────────────────────────────────────────
void test_utility_additions() {
    std::cout << "-- utility additions --\n";
    VERIFY(BitVectorUtils::bvIsMaxSigned("#b0111"));
    VERIFY(!BitVectorUtils::bvIsMaxSigned("#b1111"));
    VERIFY(BitVectorUtils::bvIsMinSigned("#b1000"));
    VERIFY(!BitVectorUtils::bvIsMinSigned("#b1001"));
    VERIFY(BitVectorUtils::bvIsMaxUnsigned("#b1111"));
    VERIFY(BitVectorUtils::bvIsNegOne("#b1111"));
    VERIFY(!BitVectorUtils::bvIsNegOne("#b1110"));
    VERIFY(BitVectorUtils::bvCompareToUint("#b0101", 5) == 0);
    VERIFY(BitVectorUtils::bvCompareToUint("#b0101", 6) < 0);
    VERIFY(BitVectorUtils::bvCompareToUint("#b0101", 4) > 0);
    // A value wider than 64 bits with a set high bit exceeds any uint64_t.
    VERIFY(BitVectorUtils::bvCompareToUint("#b1" + std::string(64, '0'), UINT64_MAX) > 0);
    expectEq("mkOnes", BitVectorUtils::mkOnes(Integer(4)), "#b1111");

    expectEq("strUnquote", StringUtils::strUnquote("\"abc\""), "abc");
    expectEq("strUnquote unquoted", StringUtils::strUnquote("abc"), "abc");

    // 64-bit unsigned values must survive without narrowing.
    Integer big(static_cast<unsigned long long>(UINT64_MAX));
    expectEq("Integer(unsigned long long)", big.toString(), "18446744073709551615");
    std::cout << "  ok: utility additions\n";
}

// ── Everything printed here must be readable by us again.  This is the
// property each printer fix is really about; asserting only on the first
// print would miss a spelling our parser cannot consume. ──────────────────
void test_printed_output_reparses() {
    std::cout << "-- printed output re-parses --\n";
    const std::string bv = "(declare-fun x () (_ BitVec 8))";
    const std::string in = "(declare-fun i () Int)";
    // The accepted legacy alias prints canonically, as in the first-print test.
    expectEq("bv2int", reparse(bv, "(bv2int x)"), "(bv2nat x)");
    expectEq("bv2nat", reparse(bv, "(bv2nat x)"), "(bv2nat x)");
    expectEq("ubv_to_int", reparse(bv, "(ubv_to_int x)"), "(ubv_to_int x)");
    expectEq("sbv_to_int", reparse(bv, "(sbv_to_int x)"), "(sbv_to_int x)");
    expectEq("int2bv", reparse(in, "((_ int2bv 8) i)"), "((_ int2bv 8) i)");
    expectEq("nat2bv", reparse(in, "((_ nat2bv 8) i)"), "((_ nat2bv 8) i)");

    const std::string dt =
        "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n"
        "(declare-fun l () L)\n";
    expectEq("tester", reparse(dt, "((_ is nil) l)"), "((_ is nil) l)");
    // The legacy spelling must land on the standard one and stay there.
    expectEq("tester from legacy input", reparse(dt, "(is-nil l)"), "((_ is nil) l)");
    expectEq("updater", reparse(dt, "((_ update hd) l 7)"), "((_ update hd) l 7)");

    const std::string tp = "(declare-fun t () (Tuple Int Int Bool))\n";
    expectEq("tuple", reparse(tp, "(tuple 1 2 true)"), "(tuple 1 2 true)");
    expectEq("tuple.select", reparse(tp, "((_ tuple.select 0) t)"), "((_ tuple.select 0) t)");
    expectEq("tuple.update", reparse(tp, "((_ tuple.update 0) t 5)"), "((_ tuple.update 0) t 5)");
    expectEq("tuple.project", reparse(tp, "((_ tuple.project 2 0) t)"), "((_ tuple.project 2 0) t)");
    expectEq("tuple.unit", reparse(tp, "tuple.unit"), "tuple.unit");

    // A RegLan-sorted declaration must survive being printed and re-declared;
    // this is what the "(RegEx String)" spelling used to break.
    {
        ParserPtr p = newParser();
        p->parseStr("(declare-fun r () RegLan)");
        const std::string sort_text = p->getVariables()[0]->getSort()->toString();
        ParserPtr q = newParser();
        q->parseStr("(declare-fun r () " + sort_text + ")");
        VERIFY(q->getVariables().size() == 1 && q->getVariables()[0]->getSort()->isReg());
        std::cout << "  ok: RegLan declaration re-parses -> " << sort_text << "\n";
    }
}

// ── Malformed uses of the new operators must be diagnosed. ────────────────
void test_new_operators_reject_bad_input() {
    std::cout << "-- new operators reject bad input --\n";
    const std::string tp = "(declare-fun t () (Tuple Int Int))\n(declare-fun b () Bool)\n";
    expectRejected("tuple.select index out of range", tp, "((_ tuple.select 5) t)");
    expectRejected("tuple.select on a non-tuple", tp, "((_ tuple.select 0) b)");
    expectRejected("tuple.update index out of range", tp, "((_ tuple.update 9) t 1)");
    expectRejected("tuple.project index out of range", tp, "((_ tuple.project 7) t)");
    expectRejected("ubv_to_int on a non-bitvector", tp, "(ubv_to_int b)");
    expectRejected("sbv_to_int on a non-bitvector", tp, "(sbv_to_int b)");

    const std::string dt =
        "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n"
        "(declare-fun l () L)\n(declare-fun n () Int)\n";
    expectRejected("update with an unknown selector", dt, "((_ update nosuch) l 7)");
    expectRejected("update on a non-datatype", dt, "((_ update hd) n 7)");
}

// ── The operand canonicalisation must not touch operators whose first child
// is not an operand.  isCommutative deliberately excludes these; this pins
// that decision, because the fork we ported from does list them. ──────────
void test_non_operand_first_child_is_never_reordered() {
    std::cout << "-- rounding mode / bound vars keep their position --\n";
    ParserPtr p = newParser();
    p->parseStr("(declare-fun a () Float32)\n(declare-fun z () Float32)\n");
    // fp.add / fp.mul take the rounding mode as child 0.
    expectEq("fp.add keeps RM first", p->toString(p->mkExpr("(fp.add RNE a z)")), "(fp.add RNE a z)");
    expectEq("fp.add keeps RM first (swapped args)",
             p->toString(p->mkExpr("(fp.add RNE z a)")), "(fp.add RNE z a)");
    expectEq("fp.mul keeps RM first", p->toString(p->mkExpr("(fp.mul RTZ a z)")), "(fp.mul RTZ a z)");

    // Quantifiers keep the bound-variable list as child 0.
    ParserPtr q = newParser();
    q->parseStr("(declare-fun f (Int Int) Bool)\n(assert (forall ((x Int) (y Int)) (f x y)))\n");
    expectEq("forall keeps its binder list",
             q->toString(q->getAssertions()[0]), "(forall ((x Int) (y Int)) (f x y))");

    // fp.min / fp.max are symmetric and take no rounding mode, so they may be
    // reordered -- but consistently.
    expectEq("fp.max is canonicalised",
             p->toString(p->mkExpr("(fp.max z a)")), p->toString(p->mkExpr("(fp.max a z)")));
}

// ── Annotation shapes beyond the single-trigger case. ─────────────────────
void test_annotation_shapes() {
    std::cout << "-- annotation shapes --\n";
    // Several trigger terms inside one :pattern.
    const std::string multi =
        "(declare-fun f (Int) Int)\n(declare-fun g (Int) Int)\n"
        "(assert (forall ((x Int)) (! (> (f x) (g x)) :pattern ((f x) (g x)))))\n";
    expectEq("multiple triggers in one :pattern", firstAssertion(multi, true),
             "(forall ((x Int)) (! (> (f x) (g x)) :pattern ((f x) (g x))))");

    // Several :pattern annotations on one term (alternative trigger sets).
    const std::string alts =
        "(declare-fun f (Int) Int)\n(declare-fun g (Int) Int)\n"
        "(assert (forall ((x Int)) (! (> (f x) (g x)) :pattern ((f x)) :pattern ((g x)))))\n";
    expectEq("alternative trigger sets", firstAssertion(alts, true),
             "(forall ((x Int)) (! (> (f x) (g x)) :pattern ((f x)) :pattern ((g x))))");

    // An annotated term that is not a quantifier body.
    const std::string plain =
        "(declare-fun p () Bool)\n(assert (! p :qid top))\n";
    expectEq("annotation outside a quantifier", firstAssertion(plain, true), "(! p :qid top)");

    // A preserved annotation must survive a print/re-parse cycle, otherwise
    // preserving it only moves the fidelity loss one step later.
    {
        ParserPtr p = newParser();
        p->setOption(std::string("preserve_annotations"), std::string("true"));
        p->parseStr(multi);
        const std::string once = p->toString(p->getAssertions()[0]);
        ParserPtr q = newParser();
        q->setOption(std::string("preserve_annotations"), std::string("true"));
        q->parseStr("(declare-fun f (Int) Int)\n(declare-fun g (Int) Int)\n(assert " + once + ")\n");
        expectEq("annotated formula re-parses", q->toString(q->getAssertions()[0]), once);
    }
}

}  // namespace

int main() {
    std::cout << "======= SMTStabilizer backport regression tests =======\n";
    test_bv_int_conversions();
    test_reglan_sort_round_trips();
    test_datatype_tester_and_updater();
    test_tuple_theory();
    test_quantifier_annotations();
    test_logic_defaults();
    test_stable_commutative_order();
    test_utility_additions();
    test_printed_output_reparses();
    test_new_operators_reject_bad_input();
    test_non_operand_first_child_is_never_reordered();
    test_annotation_shapes();
    std::cout << "All SMTStabilizer backport tests passed.\n";
    return 0;
}
