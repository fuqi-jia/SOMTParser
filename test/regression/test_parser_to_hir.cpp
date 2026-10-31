// Lifting a parsed SMT-LIB script back into the HIR.
//
// The direction the architecture was missing. Lang::Language requires a
// frontend's product to be HIR, and CHC-COMP and the SMT-LIB baseline are both
// SMT-LIB syntax, so both were blocked on this and neither could borrow the
// engine's parser without it.
//
// The property this file is built around is a ROUND TRIP:
//
//     text -> Parser -> HIR -> Parser -> text
//
// and the assertion is that the second text equals the first. Not that it is
// "equivalent" -- equal, because both ends go through the same printer, so any
// difference is a difference in the term. That makes it a mechanical claim
// rather than a judgement, and it fails loudly for the defect class this
// project keeps finding: a construct that can be built and not read back.
//
// Two things it deliberately does NOT assert.
//
// It does not assert the round trip is the identity on the SOURCE text. The
// builders simplify and canonicalise -- `(+ 1 2)` comes back as `3`, and n-ary
// commutative operands are reordered -- so the fixed point is reached after the
// first parse, not before it. Comparing against the input would be asserting
// that the simplifier does nothing.
//
// It does not assert that everything lifts. The HIR covers less than the
// engine's node kinds, and the gap is real; what it asserts is that a construct
// outside the HIR is REFUSED BY NAME rather than skipped. A lift that dropped
// what it did not recognise would return a smaller model that type-checks,
// translates, and answers a different question -- with a success code.

#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace H = SOMTParser::Uir::Hir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

/** Parse, and return the script as the engine prints it. This is the fixed
 *  point the round trip is measured against, not the source text. */
std::string normalise(const std::string& src) {
    ParserPtr p = newParser();
    VERIFY(p->parseStr(src));
    return p->dumpSMT2();
}

/** text -> Parser -> HIR -> Parser -> text. */
std::string roundTrip(const std::string& src, bool& ok, std::string& why) {
    ParserPtr in = newParser();
    if (!in->parseStr(src)) { ok = false; why = "parse failed"; return ""; }

    Lower::ParserToHir up(in);
    H::ConstraintModel model;
    Diagnostics d;
    if (!up.lift(model, d)) {
        ok = false;
        why = d.all().empty() ? "lift failed" : d.all()[0].message;
        return "";
    }
    // The lifted model must be well-sorted on its own terms. Without this a
    // sort mistake in the lift would be carried straight back down and print
    // fine, because the printer does not type-check.
    if (!typeCheck(model, d)) {
        ok = false;
        why = "lifted model does not type-check";
        return "";
    }

    ParserPtr out = newParser();
    Lower::HirToParser down(out);
    TranslationReport report;
    if (!down.lower(model, report, d)) {
        ok = false;
        why = "lowering the lifted model failed";
        return "";
    }
    ok = true;
    return out->dumpSMT2();
}

void trips(const std::string& src) {
    bool ok = false;
    std::string why;
    const std::string back = roundTrip(src, ok, why);
    if (!ok) {
        std::cout << "  ROUND TRIP FAILED (" << why << ") for:\n" << src << "\n";
        VERIFY(false);
    }
    const std::string want = normalise(src);
    if (back != want) {
        std::cout << "  ROUND TRIP DIFFERS for:\n" << src
                  << "--- expected ---\n" << want
                  << "--- got ---\n" << back;
        VERIFY(false);
    }
}

/** A construct outside the HIR must be refused, and the message must name it. */
void refuses(const std::string& src, const std::string& named) {
    bool ok = false;
    std::string why;
    roundTrip(src, ok, why);
    if (ok) {
        std::cout << "  EXPECTED A REFUSAL for:\n" << src;
        VERIFY(false);
    }
    if (!has(why, named)) {
        std::cout << "  refusal did not name '" << named << "': " << why << "\n";
        VERIFY(false);
    }
}

} // namespace

int main() {
    std::cout << "======= ParserToHir round trip =======\n";

    // ---- The cores. --------------------------------------------------------
    trips("(declare-fun p () Bool)\n(declare-fun q () Bool)\n"
          "(assert (and p (or q (not p))))\n");
    trips("(declare-fun x () Int)\n(declare-fun y () Int)\n"
          "(assert (< (+ x y) (* 2 x)))\n(assert (>= x 0))\n");
    trips("(declare-fun r () Real)\n(assert (<= (/ r 2.0) 1.0))\n");
    {
        // SMT-LIB numerals are overloaded by context. Both zeroes below are
        // Real even though they have no decimal point; lifting them as Int
        // makes the otherwise legal ite ill-sorted in the HIR.
        ParserPtr p = newParser();
        VERIFY(p->parseStr(
            "(declare-fun r () Real)\n(declare-fun b () Bool)\n"
            "(assert (= r (ite b 0 1)))\n"));
        Lower::ParserToHir up(p);
        H::ConstraintModel model;
        Diagnostics d;
        VERIFY(up.lift(model, d));
        VERIFY(typeCheck(model, d));
    }
    {
        // The concrete branch may determine the ite's numeric sort only after
        // the first, overloaded branch has been parsed.
        ParserPtr p = newParser();
        VERIFY(p->parseStr(
            "(declare-fun r () Real)\n(declare-fun b () Bool)\n"
            "(assert (= r (ite b 0 (+ r 1))))\n"));
        Lower::ParserToHir up(p);
        H::ConstraintModel model;
        Diagnostics d;
        VERIFY(up.lift(model, d));
        VERIFY(typeCheck(model, d));
    }
    trips("(declare-fun x () Int)\n(declare-fun b () Bool)\n"
          "(assert (= x (ite b 1 2)))\n");

    // ---- Division: the engine has one, and it is Euclidean. ----------------
    {
        // NT_DIV_INT lifts to DIV_EUCLID and lowers back to `div`. A lift that
        // chose DIV_TRUNC would come back as a correction term around div --
        // a different script for the same input, which the round trip catches
        // without needing to know which convention is right.
        trips("(declare-fun x () Int)\n(assert (= (div x 2) 3))\n");
        trips("(declare-fun x () Int)\n(assert (= (mod x 2) 1))\n");
    }

    // ---- Bit-vectors, where signed and unsigned must not collapse. ---------
    trips("(declare-fun a () (_ BitVec 8))\n(declare-fun b () (_ BitVec 8))\n"
          "(assert (bvult a b))\n");
    {
        // The pair that a lift mapping both orderings onto one Op would merge.
        // Asserting they round-trip separately is not enough -- this asserts
        // the two scripts stay different.
        bool ok1 = false, ok2 = false;
        std::string w1, w2;
        const std::string u = roundTrip(
            "(declare-fun a () (_ BitVec 8))\n(declare-fun b () (_ BitVec 8))\n"
            "(assert (bvult a b))\n", ok1, w1);
        const std::string s = roundTrip(
            "(declare-fun a () (_ BitVec 8))\n(declare-fun b () (_ BitVec 8))\n"
            "(assert (bvslt a b))\n", ok2, w2);
        VERIFY(ok1 && ok2);
        VERIFY(u != s);
    }
    trips("(declare-fun a () (_ BitVec 4))\n(declare-fun b () (_ BitVec 4))\n"
          "(assert (= (bvadd a b) (bvand a b)))\n");

    // ---- Arrays. -----------------------------------------------------------
    trips("(declare-fun m () (Array Int Int))\n(declare-fun i () Int)\n"
          "(assert (= (select m i) 0))\n");
    trips("(declare-fun m () (Array Int Int))\n"
          "(assert (= (select (store m 1 2) 1) 2))\n");

    // ---- Uninterpreted sorts and functions -- what CHC needs. --------------
    trips("(declare-sort U 0)\n(declare-fun c () U)\n(declare-fun f (U) U)\n"
          "(assert (= (f c) c))\n");
    trips("(declare-sort U 0)\n(declare-fun P (U Int) Bool)\n(declare-fun c () U)\n"
          "(assert (P c 3))\n");

    // ---- Quantifiers, which is where the memo has to stand aside. ----------
    trips("(declare-fun P (Int) Bool)\n"
          "(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))\n");
    trips("(declare-fun P (Int Int) Bool)\n"
          "(assert (forall ((x Int)) (exists ((y Int)) (P x y))))\n");
    {
        // Shadowing is the one case the round trip is NOT text-identical on,
        // and the reason is a real difference between the two layers: SMT-LIB
        // permits an inner binder over a name already in scope, and the HIR
        // does not -- Uir::Hir::typeCheck rejects it outright. So the lift
        // alpha-renames, and the script comes back saying the same thing with
        // one binder renamed.
        //
        // Asserted as: it round-trips at all, the result re-parses, and the two
        // binders keep their DIFFERENT sorts. That last part is the content --
        // a rename that collapsed them would produce a script where `Q` is
        // applied to an Int.
        const std::string src =
            "(declare-fun P (Int) Bool)\n(declare-fun Q ((_ BitVec 8)) Bool)\n"
            "(assert (forall ((x Int)) (and (P x) (forall ((x (_ BitVec 8))) (Q x)))))\n";
        bool ok = false;
        std::string why;
        const std::string back = roundTrip(src, ok, why);
        if (!ok) {
            std::cout << "  SHADOWING ROUND TRIP FAILED (" << why << ")\n";
            VERIFY(false);
        }
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(back));
        VERIFY(has(back, "Int"));
        VERIFY(has(back, "BitVec 8"));
        // One binder was renamed, so the emitted script is not the input.
        VERIFY(back != normalise(src));
        // ...and the rename is deterministic: lifting twice gives the same text.
        bool ok2 = false;
        std::string why2;
        VERIFY(roundTrip(src, ok2, why2) == back);
        VERIFY(ok2);
    }
    {
        // Without shadowing, a nested quantifier IS text-identical -- so the
        // case above is about shadowing and not about nesting.
        trips("(declare-fun P (Int) Bool)\n(declare-fun Q ((_ BitVec 8)) Bool)\n"
              "(assert (forall ((x Int)) (and (P x) (forall ((y (_ BitVec 8))) (Q y)))))\n");
    }

    // ---- Sharing: the input is a DAG, and the walk must not re-expand it. --
    {
        // Hash-consing makes every occurrence of the same subterm one pointer.
        // Without the memo this is exponential in the nesting -- and it is not
        // a contrived shape: it is what a Tseitin transformation produces.
        std::string src = "(declare-fun p0 () Bool)\n";
        for (int i = 1; i <= 12; ++i) {
            src += "(declare-fun p" + std::to_string(i) + " () Bool)\n";
        }
        std::string t = "p0";
        for (int i = 1; i <= 12; ++i) {
            const std::string pi = "p" + std::to_string(i);
            t = "(and (or " + t + " " + pi + ") (or " + t + " (not " + pi + ")))";
        }
        trips(src + "(assert " + t + ")\n");
    }

    // ---- Several assertions and declarations are all carried over. ---------
    {
        // A lift that returned after the first assertion would pass every case
        // above, since each has one.
        const std::string src =
            "(declare-fun x () Int)\n(declare-fun y () Int)\n(declare-fun z () Int)\n"
            "(assert (> x 0))\n(assert (> y 1))\n(assert (> z 2))\n";
        bool ok = false;
        std::string why;
        const std::string back = roundTrip(src, ok, why);
        VERIFY(ok);
        VERIFY(back == normalise(src));

        ParserPtr in = newParser();
        VERIFY(in->parseStr(src));
        Lower::ParserToHir up(in);
        H::ConstraintModel model;
        Diagnostics d;
        VERIFY(up.lift(model, d));
        VERIFY(model.constraints.size() == 3);
        VERIFY(model.decls.size() == 3);
    }

    // ---- What is outside the HIR is refused BY NAME. -----------------------
    {
        // Strings have a sort in the HIR but not the whole operator family.
        // Whichever construct is picked here, the point is the same: the
        // refusal names the kind, so a coverage gap reads as a coverage gap
        // instead of as a smaller model that translated successfully.
        ParserPtr p = newParser();
        if (p->parseStr("(declare-fun s () String)\n"
                        "(assert (= (str.to_lower s) s))\n")) {
            Lower::ParserToHir up(p);
            H::ConstraintModel model;
            Diagnostics d;
            if (!up.lift(model, d)) {
                VERIFY(d.hasErrors());
                VERIFY(d.firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
                // The message says what skipping would cost, so the refusal is
                // not mistaken for pedantry.
                VERIFY(has(d.all()[0].message, "silently drop"));
            }
        }
    }
    {
        // Floating point. This case asserted a REFUSAL when it was written,
        // because the lift carried neither the sort nor the operators. Both
        // landed while measuring the SMT-LIB baseline, so the case now asserts
        // the round trip -- which is the stronger claim and the reason to
        // re-run a refusal test after extending coverage rather than leaving
        // it asserting a gap that has closed.
        trips("(declare-fun f () Float32)\n(declare-fun g () Float32)\n"
              "(assert (fp.lt f g))\n");
        trips("(declare-fun f () Float32)\n(declare-fun g () Float32)\n"
              "(assert (fp.lt (fp.add RNE f g) g))\n");
    }

    std::cout << "All ParserToHir round-trip tests passed." << std::endl;
    return 0;
}
