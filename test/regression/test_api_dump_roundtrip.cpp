// Everything this library can BUILD, it must be able to READ BACK.
//
// Nine defects with one shape have now been fixed. The first six were found one
// at a time, each by whichever caller happened to reach it first; the last three
// were found deliberately, by sweeping every (command ...) handler in
// base_parser.cpp against the mk* builder it calls and asking which bookkeeping
// the handler does that the builder does not.
//
//   * `fp.to_ieee_bv` was in oper_key_map and in the printer but had no case in
//     parseOper.
//   * `(as set.empty (Set T))` printed in a form the plain-head path did not
//     read.
//   * `Sort::getElemSort()` was array-only, so every set builder threw.
//   * `dumpSMT2()` dropped soft assertions, turning a MaxSAT problem into a
//     plain SAT one.
//   * `Parser::mkSortDec` created the sort but never registered the symbol, so
//     the `declare-sort` line was never emitted.
//   * `Parser::mkFuncDec` registered the function but not its declaration
//     order, so the `declare-fun` line was never emitted.
//   * `Parser::mkFuncDef`, `Parser::mkFuncRec` and `Parser::mkSortDef`: the same
//     omission again, for define-fun, define-fun-rec and define-sort.
//
// The existing round-trip property (test/regression/test_dump_roundtrip.cpp)
// runs over the instance corpus, and that is exactly why it caught none of
// these: a construct no corpus file uses is never built, so the property never
// sees it. This file closes that gap from the other end -- terms built through
// the PUBLIC API rather than read from a file -- which is the only way a
// construct with no corpus coverage gets exercised at all.
//
// A new construct belongs here the moment its builder is public, whether or not
// any instance uses it. That is the point.

#include "somtparser/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

/** Build a script through the API, dump it, and require a fresh parser to read
 *  the dump. Returns the dump so callers can also assert on what it contains --
 *  a script that re-parses but lost a command is still wrong. */
std::string roundTrip(const std::function<void(const ParserPtr&)>& build) {
    ParserPtr p = newParser();
    build(p);
    const std::string dumped = p->dumpSMT2();
    ParserPtr reader = newParser();
    if (!reader->parseStr(dumped)) {
        std::cerr << "the dump did not re-parse:\n" << dumped << std::endl;
        VERIFY(false);
    }
    return dumped;
}

} // namespace

int main() {
    std::cout << "======= API-built terms survive dump/re-parse =======\n";

    // ---- An uninterpreted sort and functions over it. -----------------------
    // The whole of cluster G. Before mkSortDec registered the symbol, the dump
    // named `U` in a binder that nothing declared; before mkFuncDec recorded the
    // declaration order, `f` and `p` were applied but never declared.
    {
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto U = p->mkSortDec("U", 0);
            p->mkFuncDec("f", {U}, U);
            p->mkFuncDec("p", {U}, p->mkBoolSort());
            auto c = p->mkVar(U, "c");
            p->assert(p->mkApplyUF(p->mkBoolSort(), "p",
                                   {p->mkApplyUF(U, "f", {c})}));
        });
        VERIFY(has(s, "(declare-sort U 0)"));
        VERIFY(has(s, "declare-fun f (U) U"));
        VERIFY(has(s, "declare-fun p (U) Bool"));
        VERIFY(has(s, "declare-fun c () U"));
    }
    {
        // A sort used ONLY as a quantifier binder's sort -- no variable of it is
        // ever declared. This is the shape the TPTP frontend produces and the
        // one that surfaced the defect: the sort reaches the script through the
        // binder alone, so a registration that happened as a side effect of
        // declaring a variable would not have covered it.
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto U = p->mkSortDec("U", 0);
            p->mkFuncDec("q", {U}, p->mkBoolSort());
            auto x = p->mkQuantVar("x", U);
            // params[0] is the BODY; params[1..] are the binders. The reverse
            // of the surface syntax, and of what mkForall's declaration comment
            // said until this test was written.
            p->assert(p->mkForall({p->mkApplyUF(p->mkBoolSort(), "q", {x}), x}));
        });
        VERIFY(has(s, "(declare-sort U 0)"));
        VERIFY(has(s, "(forall ((x U)) (q x))"));
    }
    {
        // The two ways to reach one formula must agree. `mkForall`'s argument
        // order is the reverse of the syntax, and getting it wrong produces
        // `(forall ((q Bool)) x)` -- a well-formed script denoting a different
        // formula, with no error anywhere. Comparing the API path against the
        // PARSE path is what makes that visible: neither dump alone looks wrong.
        const char* src =
            "(declare-sort U 0)\n"
            "(declare-fun q (U) Bool)\n"
            "(assert (forall ((x U)) (q x)))\n"
            "(check-sat)\n";
        ParserPtr parsed = newParser();
        VERIFY(parsed->parseStr(src));

        ParserPtr built = newParser();
        auto U = built->mkSortDec("U", 0);
        built->mkFuncDec("q", {U}, built->mkBoolSort());
        auto x = built->mkQuantVar("x", U);
        built->assert(built->mkForall({built->mkApplyUF(built->mkBoolSort(), "q", {x}), x}));

        VERIFY(parsed->dumpSMT2() == built->dumpSMT2());
    }
    {
        // Declaring the same sort twice must not emit two declare-sort lines.
        // registerSort was already idempotent; mkSortDec now calls it once per
        // occurrence, so this is the claim that keeps that safe.
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto U = p->mkSortDec("U", 0);
            p->mkSortDec("U", 0);
            p->mkFuncDec("g", {U}, U);
            p->assert(p->mkEq(p->mkVar(U, "a"), p->mkVar(U, "b")));
        });
        std::size_t n = 0, at = 0;
        while ((at = s.find("(declare-sort U", at)) != std::string::npos) { ++n; ++at; }
        VERIFY(n == 1);
        // Same for the function: the (declare-fun ...) command path calls
        // addFunctionName after mkFuncDec, so the name arrives twice there.
        std::size_t m = 0;
        at = 0;
        while ((at = s.find("declare-fun g ", at)) != std::string::npos) { ++m; ++at; }
        VERIFY(m == 1);
    }

    // ---- Definitions, not just declarations. --------------------------------
    // Found by sweeping the command handlers against the mk* they call, after
    // mkSortDec and mkFuncDec turned out to be half-declarations: mkFuncDef,
    // mkFuncRec and mkSortDef were the same shape. A function defined through
    // the API resolved and was callable, and appeared nowhere in the script.
    {
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto x = p->mkFunParamVar(p->mkIntSort(), "x");
            p->mkFuncDef("twice", {x}, p->mkIntSort(), p->mkAdd({x, x}));
            auto n = p->mkVarInt("n");
            p->assert(p->mkEq(p->mkApplyUF(p->mkIntSort(), "twice", {n}),
                              p->mkConstInt(6)));
        });
        VERIFY(has(s, "define-fun twice"));
    }
    {
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto x = p->mkFunParamVar(p->mkIntSort(), "x");
            p->mkFuncRec("f", {x}, p->mkIntSort(),
                         p->mkIte(p->mkLe(x, p->mkConstInt(0)), p->mkConstInt(0),
                                  p->mkApplyUF(p->mkIntSort(), "f",
                                               {p->mkSub({x, p->mkConstInt(1)})})));
            p->assert(p->mkEq(p->mkApplyUF(p->mkIntSort(), "f", {p->mkVarInt("n")}),
                              p->mkConstInt(0)));
        });
        VERIFY(has(s, "define-fun-rec f") || has(s, "define-funs-rec"));
    }
    {
        // define-sort is NOT a dump claim: `parseSort()` expands an alias where
        // it is used, so `(define-sort Idx () Int)` leaves no line in the script
        // and `(declare-const i Idx)` comes back as `(declare-fun i () Int)`.
        // What mkSortDef owes the caller is the same thing mkSortDec does --
        // that the NAME resolves afterwards, as it does on the command path.
        ParserPtr p = newParser();
        auto alias = p->mkSortDef("Idx", {}, p->mkIntSort());
        VERIFY(alias != nullptr);
        VERIFY(p->getSymbolManager()->hasSort("Idx"));
        VERIFY(p->getSymbolManager()->resolveSort("Idx") == alias);
        // The alias object itself is not usable as a variable's sort -- the
        // arithmetic builders reject it, because it is SK_DEF rather than the
        // sort it stands for. Recorded in docs/open-questions-2026-08-13.md
        // rather than worked around here: whether mkSortDef should return the
        // resolved sort is a design call, not a bug fix.
    }

    // ---- Soft assertions: the dump is the only record of the weight. --------
    {
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto x = p->mkVarBool("x");
            auto y = p->mkVarBool("y");
            p->assert(p->mkOr({x, y}));
            p->assertSoft(x, p->mkConstInt(3), "g1");
            p->assertSoft(p->mkNot(y), p->mkConstInt(1), "g1");
        });
        // A MaxSAT problem must not come back a plain SAT problem.
        VERIFY(has(s, "assert-soft"));
        VERIFY(has(s, ":weight 3"));
        VERIFY(has(s, ":id g1"));
    }

    // ---- Constants whose printed form is not their read form. ---------------
    {
        // A bare decimal is a REAL in SMT-LIB, so a floating-point constant has
        // to carry its format: `((_ to_fp 8 24) RNE 1.5)`.
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto f = p->mkVarFp("f", 8, 24);
            p->assert(p->mkEq(f, p->mkConstFp("1.5", 8, 24)));
        });
        VERIFY(has(s, "to_fp"));
    }
    {
        // A string constant is quoted, and an embedded quote is doubled.
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto v = p->mkVarStr("s");
            p->assert(p->mkEq(v, p->mkConstStr("a\"b")));
        });
        VERIFY(has(s, "\"a\"\"b\""));
    }
    {
        // `(as set.empty (Set Int))` -- the empty set needs its sort, and the
        // annotated form has to be readable by the plain-head path.
        const std::string s = roundTrip([](const ParserPtr& p) {
            auto set_sort = p->getSortManager()->createSetSort(p->mkIntSort());
            auto v = p->mkVar(set_sort, "S");
            p->assert(p->mkEq(v, p->mkSetEmpty(set_sort)));
        });
        VERIFY(has(s, "set.empty"));
    }

    std::cout << "All API dump/re-parse tests passed." << std::endl;
    return 0;
}
