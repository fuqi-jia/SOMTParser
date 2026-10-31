// The HIR's sort vocabulary, and what each new sort has to check.
//
// It was { BOOL, INT, REAL } and then { …, ARRAY }, which is not a vocabulary
// twenty-two languages can share: docs/languages/smtlib2.md §4.1 measured the
// gap as 45 bit-vector kinds, 44 floating-point and 44 string in the engine
// against three sorts in the HIR, and docs/hir-design-decisions-2026-08-12.md
// §2 records the decision to close it rather than route the baseline around it.
//
// This file pins the part that is easy to get wrong and impossible to see: a
// sort is not its *kind*. An 8-bit vector and a 32-bit vector are as different
// as Int and Bool, two FloatingPoint sorts differ by their exponent and
// significand, and two uninterpreted sorts are the same one only when their
// names match. A sameSort that compared kinds alone would type-check a width
// mismatch, and nothing downstream re-checks.

#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

// Sort is ambiguous once both using-directives are in scope: SOMTParser::Sort
// (the engine's) and SOMTParser::Uir::Hir::Sort are the same concept at two
// layers, so qualification rather than renaming is the right fix -- the same
// call test/lowering/test_lower_omt_dialect.cpp documents for Objective.
namespace H = SOMTParser::Uir::Hir;

namespace {

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

bool accepts(const ConstraintModel& m) {
    Diagnostics d;
    const bool ok = typeCheck(m, d);
    VERIFY(ok == !d.hasErrors());
    return ok;
}

bool rejects(const ConstraintModel& m, ErrorCode code) {
    Diagnostics d;
    if (typeCheck(m, d)) { return false; }
    return d.hasErrors() && d.firstErrorCode() == code;
}

/** The first error's message, so a diagnostic can be read and not just counted. */
std::string firstError(const ConstraintModel& m) {
    Diagnostics d;
    VERIFY(!typeCheck(m, d));
    for (const auto& e : d.all()) {
        if (e.severity == Severity::ERROR) { return e.message; }
    }
    VERIFY(false && "no error recorded");
    return "";
}

VarDecl decl(const char* n, H::Sort s) {
    VarDecl d;
    d.name = n;
    d.sort = std::move(s);
    return d;
}

Constraint hard(ExprPtr f) {
    Constraint c;
    c.formula = std::move(f);
    return c;
}

/** Lower a well-typed model and hand back the emitted script. */
std::string emit(const ConstraintModel& m) {
    Diagnostics d;
    VERIFY(typeCheck(m, d));
    ParserPtr p = newParser();
    Lower::HirToParser lowered(p);
    TranslationReport report;
    VERIFY(lowered.lower(m, report, d));
    VERIFY(!d.hasErrors());
    return p->dumpSMT2();
}

} // namespace

int main() {
    std::cout << "======= HIR sorts =======\n";

    // ---- sameSort is structural, not by kind. -------------------------------
    {
        VERIFY(sameSort(H::Sort::bitvec(8), H::Sort::bitvec(8)));
        VERIFY(!sameSort(H::Sort::bitvec(8), H::Sort::bitvec(32)));
        VERIFY(!sameSort(H::Sort::bitvec(8), H::Sort::integer()));

        VERIFY(sameSort(H::Sort::floating(8, 24), H::Sort::floating(8, 24)));
        VERIFY(!sameSort(H::Sort::floating(8, 24), H::Sort::floating(11, 53)));

        VERIFY(sameSort(H::Sort::uninterpreted("Ref"), H::Sort::uninterpreted("Ref")));
        VERIFY(!sameSort(H::Sort::uninterpreted("Ref"), H::Sort::uninterpreted("Field")));

        VERIFY(sameSort(H::Sort::string(), H::Sort::string()));

        // Arrays compare through both components, recursively.
        VERIFY(sameSort(H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8)),
                        H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8))));
        VERIFY(!sameSort(H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8)),
                         H::Sort::array(H::Sort::integer(), H::Sort::bitvec(32))));
        VERIFY(!sameSort(H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8)),
                         H::Sort::array(H::Sort::bitvec(8), H::Sort::bitvec(8))));
    }

    // ---- Each new sort declares and lowers. ---------------------------------
    {
        ConstraintModel m;
        m.decls.push_back(decl("bv", H::Sort::bitvec(8)));
        m.decls.push_back(decl("f", H::Sort::floating(8, 24)));
        m.decls.push_back(decl("s", H::Sort::string()));
        m.decls.push_back(decl("r", H::Sort::uninterpreted("Ref")));
        m.decls.push_back(decl("a", H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8))));
        VERIFY(accepts(m));

        const std::string smt = emit(m);
        VERIFY(contains(smt, "declare-fun bv"));
        VERIFY(contains(smt, "declare-fun f"));
        VERIFY(contains(smt, "declare-fun s"));
        VERIFY(contains(smt, "declare-fun r"));
        VERIFY(contains(smt, "declare-fun a"));
        // The widths reach the script rather than being lost in the kind.
        VERIFY(contains(smt, "BitVec 8"));
    }

    // ---- A sort prints as itself, widths included. ---------------------------
    // Not cosmetic. Every type diagnostic was built from the *kind*, so the
    // width-mismatch error below read "'x' is used as BitVec but was declared
    // BitVec" -- a correct check whose report cannot distinguish the two cases
    // it exists to distinguish. The spelling matches the engine's
    // Sort::toString so that one name serves the diagnostic and the script.
    {
        VERIFY(toString(H::Sort::boolean()) == "Bool");
        VERIFY(toString(H::Sort::integer()) == "Int");
        VERIFY(toString(H::Sort::real()) == "Real");
        VERIFY(toString(H::Sort::string()) == "String");
        VERIFY(toString(H::Sort::bitvec(8)) == "(_ BitVec 8)");
        VERIFY(toString(H::Sort::bitvec(32)) == "(_ BitVec 32)");
        VERIFY(toString(H::Sort::floating(8, 24)) == "(_ FloatingPoint 8 24)");
        VERIFY(toString(H::Sort::uninterpreted("Ref")) == "Ref");
        VERIFY(toString(H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8)))
               == "(Array Int (_ BitVec 8))");
        // Two sorts that sameSort separates must also print differently, or a
        // reader cannot act on the message.
        VERIFY(toString(H::Sort::bitvec(8)) != toString(H::Sort::bitvec(32)));
        VERIFY(toString(H::Sort::floating(8, 24)) != toString(H::Sort::floating(11, 53)));
        VERIFY(toString(H::Sort::uninterpreted("Ref"))
               != toString(H::Sort::uninterpreted("Field")));
    }

    // ---- The HIR's name for a sort is the one the script carries. -----------
    // The round trip that makes "borrow the engine's shape, do not share its
    // type" a checked claim rather than a design note: lowering goes through a
    // separate SOMTParser::Sort, and this pins the two spellings together, so
    // a future divergence fails here instead of surfacing as a script whose
    // declared sorts do not match the diagnostics that described them.
    {
        const H::Sort sorts[] = {
            H::Sort::boolean(), H::Sort::integer(), H::Sort::real(),
            H::Sort::string(), H::Sort::bitvec(8), H::Sort::bitvec(256),
            H::Sort::floating(8, 24), H::Sort::floating(11, 53),
            H::Sort::uninterpreted("Ref"),
            H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8)),
            H::Sort::array(H::Sort::bitvec(32), H::Sort::boolean()),
        };
        int nth = 0;
        for (const H::Sort& s : sorts) {
            ConstraintModel m;
            m.decls.push_back(decl(("v" + std::to_string(nth++)).c_str(), s));
            const std::string smt = emit(m);
            VERIFY(contains(smt, toString(s)));
        }
    }

    // ---- A width mismatch is a type error, not a silent coercion. -----------
    // The failure this whole sort structure exists to catch.
    {
        ConstraintModel m;
        m.decls.push_back(decl("x", H::Sort::bitvec(8)));
        m.decls.push_back(decl("y", H::Sort::bitvec(32)));
        m.constraints.push_back(hard(mkOp(Op::EQ,
            {mkIdent("x", H::Sort::bitvec(8)), mkIdent("y", H::Sort::bitvec(32))})));
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        // ...and the report names both widths. Without this the check passes
        // while telling the user nothing.
        const std::string msg = firstError(m);
        VERIFY(contains(msg, "(_ BitVec 8)"));
        VERIFY(contains(msg, "(_ BitVec 32)"));
    }
    {
        // ...and the matching widths are accepted, so the check is not simply
        // rejecting every bit-vector equality.
        ConstraintModel m;
        m.decls.push_back(decl("x", H::Sort::bitvec(8)));
        m.decls.push_back(decl("y", H::Sort::bitvec(8)));
        m.constraints.push_back(hard(mkOp(Op::EQ,
            {mkIdent("x", H::Sort::bitvec(8)), mkIdent("y", H::Sort::bitvec(8))})));
        VERIFY(accepts(m));
        VERIFY(contains(emit(m), "BitVec 8"));
    }

    // ---- Bit-vector literals carry their width. ------------------------------
    {
        ConstraintModel m;
        m.decls.push_back(decl("x", H::Sort::bitvec(8)));
        m.constraints.push_back(hard(mkOp(Op::EQ,
            {mkIdent("x", H::Sort::bitvec(8)), mkBitVec("#b00001010", 8)})));
        VERIFY(accepts(m));

        // A literal of the wrong width against the same variable is rejected --
        // the literal's width comes from its own sort, so this is the same
        // check reaching a different node.
        ConstraintModel bad;
        bad.decls.push_back(decl("x", H::Sort::bitvec(8)));
        bad.constraints.push_back(hard(mkOp(Op::EQ,
            {mkIdent("x", H::Sort::bitvec(8)), mkBitVec("#b1010", 4)})));
        VERIFY(rejects(bad, ErrorCode::E_TYPE));
    }

    // ---- Strings. ------------------------------------------------------------
    {
        ConstraintModel m;
        m.decls.push_back(decl("s", H::Sort::string()));
        m.constraints.push_back(hard(mkOp(Op::EQ,
            {mkIdent("s", H::Sort::string()), mkString("hello")})));
        VERIFY(accepts(m));
        VERIFY(contains(emit(m), "hello"));
    }

    // ---- Uninterpreted sorts and functions (cluster G). ---------------------
    {
        const H::Sort ref = H::Sort::uninterpreted("Ref");
        ConstraintModel m;
        m.decls.push_back(decl("p", ref));
        m.decls.push_back(decl("q", ref));

        FunDecl f;
        f.name = "parent";
        f.params = {ref};
        f.result = ref;
        m.funs.push_back(f);

        FunDecl pred;
        pred.name = "reachable";
        pred.params = {ref, ref};
        pred.result = H::Sort::boolean();
        m.funs.push_back(pred);

        // reachable(parent(p), q)
        m.constraints.push_back(hard(mkApply(
            "reachable", H::Sort::boolean(),
            {mkApply("parent", ref, {mkIdent("p", ref)}), mkIdent("q", ref)})));
        VERIFY(accepts(m));

        const std::string smt = emit(m);
        VERIFY(contains(smt, "reachable"));
        VERIFY(contains(smt, "parent"));
    }

    // ---- What an application must not get away with. ------------------------
    {
        const H::Sort ref = H::Sort::uninterpreted("Ref");
        FunDecl f;
        f.name = "parent";
        f.params = {ref};
        f.result = ref;

        {   // undeclared
            ConstraintModel m;
            m.decls.push_back(decl("p", ref));
            m.constraints.push_back(hard(mkOp(Op::EQ,
                {mkApply("nosuch", ref, {mkIdent("p", ref)}), mkIdent("p", ref)})));
            VERIFY(rejects(m, ErrorCode::E_TYPE));
        }
        {   // wrong arity
            ConstraintModel m;
            m.decls.push_back(decl("p", ref));
            m.funs.push_back(f);
            m.constraints.push_back(hard(mkOp(Op::EQ,
                {mkApply("parent", ref, {mkIdent("p", ref), mkIdent("p", ref)}),
                 mkIdent("p", ref)})));
            VERIFY(rejects(m, ErrorCode::E_TYPE));
        }
        {   // wrong argument sort
            ConstraintModel m;
            m.decls.push_back(decl("p", ref));
            m.decls.push_back(decl("i", H::Sort::integer()));
            m.funs.push_back(f);
            m.constraints.push_back(hard(mkOp(Op::EQ,
                {mkApply("parent", ref, {mkIdent("i", H::Sort::integer())}),
                 mkIdent("p", ref)})));
            VERIFY(rejects(m, ErrorCode::E_TYPE));
        }
        {   // a function and a variable of the same name would be two symbols
            // the emitted script cannot tell apart
            ConstraintModel m;
            m.decls.push_back(decl("parent", ref));
            m.funs.push_back(f);
            VERIFY(rejects(m, ErrorCode::E_TYPE));
        }
        {   // declared twice
            ConstraintModel m;
            m.funs.push_back(f);
            m.funs.push_back(f);
            VERIFY(rejects(m, ErrorCode::E_TYPE));
        }
    }

    // ---- A function is not a variable. --------------------------------------
    // features() must not report one, and the bound-ints pass iterates decls;
    // both would be wrong for a function, which is why funs is a separate list.
    {
        const H::Sort ref = H::Sort::uninterpreted("Ref");
        ConstraintModel m;
        FunDecl f;
        f.name = "g";
        f.params = {H::Sort::integer()};
        f.result = H::Sort::integer();
        m.funs.push_back(f);
        const auto features = m.features();
        VERIFY(features.count(feat::intVar()) == 0);
    }

    std::cout << "All HIR sort tests passed.\n";
    return 0;
}
