// An applied sort constructor, built directly in the HIR.
//
// `(declare-sort S 1)` declares a sort CONSTRUCTOR, so `(S Bool)` and `(S Int)`
// are two sorts (SMT-LIB 2.6 §3.6), and `Hir::Sort::args` is what carries the
// arguments across.
//
// This file exists because the round-trip sweep could not reach the rule. A
// script equating two instantiations is refused by the ENGINE, at parse, so it
// never arrives at the HIR type checker -- and a breakage probe confirmed it:
// with `sameSort` cut back to comparing names alone, every round-trip test
// still passed. The rule is therefore checked here, where a model is built by
// hand the way a frontend that does not go through SMT-LIB text builds one.
//
// What that means in practice: the frontends most at risk are exactly the ones
// with no SMT-LIB parser under them.

#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace H = SOMTParser::Uir::Hir;

namespace {

const H::Sort INT   = H::Sort::integer();
const H::Sort BOOLS = H::Sort::boolean();
/** `(S Bool)`, `(S Int)`, `(S (S Bool))` and `(Q Int Bool)`. */
const H::Sort S_BOOL = H::Sort::sortApp("S", {BOOLS});
const H::Sort S_INT  = H::Sort::sortApp("S", {INT});
const H::Sort S_S_B  = H::Sort::sortApp("S", {S_BOOL});
const H::Sort Q_IB   = H::Sort::sortApp("Q", {INT, BOOLS});
/** Arity 0, the ordinary uninterpreted sort. */
const H::Sort U      = H::Sort::uninterpreted("U");

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

H::VarDecl decl(const char* n, H::Sort s) {
    H::VarDecl d;
    d.name = n;
    d.sort = std::move(s);
    return d;
}

void add(H::ConstraintModel& m, H::ExprPtr formula) {
    H::Constraint c;
    c.formula = std::move(formula);
    m.constraints.push_back(c);
}

/** Type-check, and say whether it passed. */
bool checks(const H::ConstraintModel& m) {
    Diagnostics d;
    return typeCheck(m, d);
}

std::string emit(const H::ConstraintModel& m) {
    Diagnostics d;
    VERIFY(typeCheck(m, d));
    ParserPtr p = newParser();
    Lower::HirToParser lowered(p);
    TranslationReport report;
    VERIFY(lowered.lower(m, report, d));
    return p->dumpSMT2();
}

} // namespace

int main() {
    std::cout << "======= Hir::Sort, applied sort constructors =======\n";

    // ---- sameSort is the rule, and it compares the ARGUMENTS. ---------------
    {
        VERIFY(sameSort(S_BOOL, H::Sort::sortApp("S", {BOOLS})));
        // The one that matters. Comparing names alone makes these equal, and
        // then two variables of unrelated sorts are interchangeable.
        VERIFY(!sameSort(S_BOOL, S_INT));
        // A different constructor with the same arguments.
        VERIFY(!sameSort(S_BOOL, H::Sort::sortApp("T", {BOOLS})));
        // Recursion: `(S (S Bool))` is not `(S Bool)`, which only holds if the
        // comparison goes all the way down rather than stopping at the top.
        VERIFY(!sameSort(S_S_B, S_BOOL));
        VERIFY(sameSort(S_S_B, H::Sort::sortApp("S", {S_BOOL})));
        // Arity is part of it.
        VERIFY(!sameSort(Q_IB, H::Sort::sortApp("Q", {INT})));
        VERIFY(sameSort(Q_IB, H::Sort::sortApp("Q", {INT, BOOLS})));
        // Argument ORDER is part of it.
        VERIFY(!sameSort(Q_IB, H::Sort::sortApp("Q", {BOOLS, INT})));
        // Arity 0 is unchanged: no arguments, compared by name.
        VERIFY(sameSort(U, H::Sort::uninterpreted("U")));
        VERIFY(!sameSort(U, H::Sort::uninterpreted("V")));
        // ...and an arity-0 sort is not an application of the same name.
        VERIFY(!sameSort(H::Sort::uninterpreted("S"), S_BOOL));
    }

    // ---- The type checker uses it. -----------------------------------------
    {
        // Same instantiation: well-sorted.
        H::ConstraintModel m;
        m.decls.push_back(decl("a", S_BOOL));
        m.decls.push_back(decl("b", S_BOOL));
        add(m, H::mkOp(H::Op::EQ, {H::mkIdent("a", S_BOOL), H::mkIdent("b", S_BOOL)}));
        VERIFY(checks(m));
    }
    {
        // Two instantiations: NOT well-sorted. This is the assertion the
        // round-trip tests cannot make, because the engine refuses the script
        // before the HIR ever sees it.
        H::ConstraintModel m;
        m.decls.push_back(decl("a", S_BOOL));
        m.decls.push_back(decl("c", S_INT));
        add(m, H::mkOp(H::Op::EQ, {H::mkIdent("a", S_BOOL), H::mkIdent("c", S_INT)}));
        VERIFY(!checks(m));
    }

    // ---- It reaches a script, and the script says what the model said. ------
    {
        H::ConstraintModel m;
        m.decls.push_back(decl("a", S_BOOL));
        m.decls.push_back(decl("c", S_INT));
        m.decls.push_back(decl("z", S_S_B));
        m.decls.push_back(decl("q", Q_IB));
        m.decls.push_back(decl("u", U));
        add(m, H::mkOp(H::Op::EQ, {H::mkIdent("a", S_BOOL), H::mkIdent("a", S_BOOL)}));
        const std::string smt = emit(m);

        // The constructor is declared at its arity, ONCE, and the two
        // instantiations both appear.
        VERIFY(contains(smt, "(declare-sort S 1)"));
        VERIFY(contains(smt, "(declare-sort Q 2)"));
        VERIFY(contains(smt, "(declare-sort U 0)"));
        VERIFY(contains(smt, "(declare-fun a () (S Bool))"));
        VERIFY(contains(smt, "(declare-fun c () (S Int))"));
        VERIFY(contains(smt, "(declare-fun z () (S (S Bool)))"));
        VERIFY(contains(smt, "(declare-fun q () (Q Int Bool))"));
        VERIFY(contains(smt, "(declare-fun u () U)"));

        // And it reads back. Lowering that returned the CONSTRUCTOR for every
        // instantiation would print `(declare-fun a () S)` here -- a
        // constructor at the wrong arity, which no other tool accepts.
        ParserPtr p = newParser();
        if (!p->parseStr(smt)) {
            std::cout << "  emitted script does not re-parse:\n" << smt;
            VERIFY(false);
        }
    }

    // ---- An applied sort inside another sort. ------------------------------
    {
        H::ConstraintModel m;
        const H::Sort arr = H::Sort::array(INT, S_BOOL);
        m.decls.push_back(decl("m", arr));
        m.decls.push_back(decl("a", S_BOOL));
        add(m, H::mkOp(H::Op::EQ,
                       {H::mkOp(H::Op::SELECT, {H::mkIdent("m", arr), H::mkInt(0)}),
                        H::mkIdent("a", S_BOOL)}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "(Array Int (S Bool))"));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(smt));
    }
    {
        // ...and the element sort is still compared. `(Array Int (S Bool))` is
        // not `(Array Int (S Int))`.
        VERIFY(!sameSort(H::Sort::array(INT, S_BOOL), H::Sort::array(INT, S_INT)));
        VERIFY(sameSort(H::Sort::array(INT, S_BOOL), H::Sort::array(INT, S_BOOL)));
    }

    // ---- toString names the sort a diagnostic will show. -------------------
    {
        VERIFY(toString(S_BOOL) == "(S Bool)");
        VERIFY(toString(S_S_B) == "(S (S Bool))");
        VERIFY(toString(Q_IB) == "(Q Int Bool)");
        VERIFY(toString(U) == "U");
    }

    std::cout << "All parametric-sort HIR tests passed." << std::endl;
    return 0;
}
