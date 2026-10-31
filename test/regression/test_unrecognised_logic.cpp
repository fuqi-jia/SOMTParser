// An unrecognised `(set-logic ...)` is a warning, not a parse error.
//
// GlobalOptions::setLogic already handles the case and says so where it is
// defined: an unrecognised name "should not disable theories; fall back to ALL
// and report the name as unrecognised". The parser turned that `false` into
// err_unkwn_sym, which throws -- so the whole file failed to parse and the
// option layer's stated intent never took effect.
//
// The names this rejected are not exotic:
//
//   * `HORN` is what Z3, Eldarica and Golem consume, and is now a recognised
//     alias for enabling every background theory while the CHC frontend checks
//     clause shape;
//   * SMT-LIB gains logics over time, so a released parser that refuses an
//     unknown one refuses inputs that are legal today and inputs that become
//     legal later.
//
// Falling back to ALL is strictly safer than the alternative, since ALL enables
// every theory: the parse continues with nothing switched off.

#include "somtparser/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

} // namespace

int main() {
    std::cout << "======= unrecognised set-logic =======\n";

    // ---- The name that motivated this. -------------------------------------
    {
        ParserPtr p = newParser();
        VERIFY(p->parseStr("(set-logic HORN)\n"
                           "(declare-fun P (Int) Bool)\n"
                           "(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))\n"));
        const std::string s = p->dumpSMT2();
        // The script survives whole -- the declaration and the assertion are
        // both there. Before, the file did not parse at all.
        VERIFY(has(s, "(declare-fun P (Int) Bool)"));
        VERIFY(has(s, "forall"));
        // And it round-trips, which it cannot do if the logic name it emits is
        // one it will not read back.
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(s));
    }

    // ---- Truly unknown names remain forward-compatible. -------------------
    {
        for (const char* logic : {"QF_NEWTHEORY", "AUFBVFPDTNIRA_2030"}) {
            ParserPtr p = newParser();
            const std::string src =
                std::string("(set-logic ") + logic + ")\n"
                "(declare-fun x () Int)\n(assert (> x 0))\n";
            VERIFY(p->parseStr(src));
            VERIFY(has(p->dumpSMT2(), "(assert (> x 0))"));
        }
    }

    // ---- The fallback enables every theory, so nothing is switched off. ----
    {
        // A bit-vector term under an unrecognised logic. If the fallback
        // disabled theories rather than widening to ALL, this would fail --
        // which is the failure the option layer's comment warns against.
        ParserPtr p = newParser();
        VERIFY(p->parseStr("(set-logic HORN)\n"
                           "(declare-fun a () (_ BitVec 8))\n"
                           "(assert (bvult a #x0f))\n"));
        VERIFY(has(p->dumpSMT2(), "bvult"));
    }

    // ---- A RECOGNISED logic is still recorded as itself. -------------------
    {
        // Without this, "fixing" the parser by ignoring set-logic entirely
        // would pass every assertion above.
        ParserPtr p = newParser();
        VERIFY(p->parseStr("(set-logic QF_LIA)\n(declare-fun x () Int)\n"
                           "(assert (> x 0))\n"));
        VERIFY(has(p->dumpSMT2(), "(set-logic QF_LIA)"));
    }

    // ---- A malformed set-logic is still an error. --------------------------
    {
        // The change makes an unknown NAME a warning. It does not make the
        // command optional, and a missing argument is still malformed input.
        ParserPtr p = newParser();
        bool threw = false;
        try {
            if (!p->parseStr("(set-logic)\n(declare-fun x () Int)\n")) { threw = true; }
        } catch (const std::exception&) {
            threw = true;
        }
        VERIFY(threw);
    }

    std::cout << "All unrecognised-logic tests passed." << std::endl;
    return 0;
}
