// Algebraic datatypes.
//
// The last row of docs/languages/smtlib2.md's missing table, or the half of it
// that has somewhere to land: the engine implements datatypes and tuples
// (NT_DT_CONSTRUCTOR, NT_DT_SELECTOR, NT_DT_TESTER, NT_DT_MATCH, NT_DT_UPDATER,
// and five more for tuples) and a parsed declare-datatypes already dumps back to
// itself. Sets, sequences and bags do not: they have a SORT_KIND each and zero
// NODE_KINDs and zero operators, so a HIR surface for them would lower to
// nothing. That is engine work, and this file is the part that is not.
//
// Two rules here are easy to state and easy to implement wrongly.
//
// Recursion is the point. A selector's sort may be the datatype being declared
// -- that is what makes a list a list -- or one declared later in the same
// model, because mutual recursion between two datatypes is ordinary modelling.
// So declarations are registered in one pass and filled in a second, and a
// forward reference is legal rather than an error.
//
// Constructor and selector names are unique across ALL datatypes in scope, not
// merely within one. SMT-LIB says so, and the reason is visible from the
// checker: an application names a constructor and nothing else, so two
// datatypes with a `cons` apiece would make `(cons 1 nil)` ambiguous.

#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace H = SOMTParser::Uir::Hir;

namespace {

const H::Sort INT = H::Sort::integer();
const H::Sort LST = H::Sort::datatype("Lst");

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

VarDecl decl(const char* n, H::Sort s) {
    VarDecl d;
    d.name = n;
    d.sort = std::move(s);
    return d;
}

DtSelector sel(const char* n, H::Sort s) { return DtSelector{n, std::move(s)}; }

/** `(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))` --
 *  recursive, which is the case worth testing rather than a flat enum. */
DatatypeDecl lst() {
    DatatypeDecl dt;
    dt.name = "Lst";
    dt.constructors.push_back(DtConstructor{"nil", {}});
    dt.constructors.push_back(DtConstructor{"cons", {sel("hd", INT), sel("tl", LST)}});
    return dt;
}

ConstraintModel base() {
    ConstraintModel m;
    m.datatypes.push_back(lst());
    m.decls.push_back(decl("l", LST));
    m.decls.push_back(decl("i", INT));
    return m;
}

void add(ConstraintModel& m, ExprPtr f) {
    Constraint c;
    c.formula = std::move(f);
    m.constraints.push_back(c);
}

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

bool rejects(const ConstraintModel& m, ErrorCode code) {
    Diagnostics d;
    if (typeCheck(m, d)) { return false; }
    return d.hasErrors() && d.firstErrorCode() == code;
}

ExprPtr nil()  { return mkDtConstructor("nil", LST, {}); }
ExprPtr lvar() { return mkIdent("l", LST); }

} // namespace

int main() {
    std::cout << "======= HIR datatypes =======\n";

    // ---- A recursive datatype declares, lowers, and round-trips. ------------
    {
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {lvar(), mkDtConstructor("cons", LST, {mkInt(1), nil()})}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "declare-datatypes"));
        VERIFY(contains(smt, "Lst"));
        VERIFY(contains(smt, "cons"));
        // The strong claim: what came out is SMT-LIB this library reads back.
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }

    // ---- Selector and tester. -----------------------------------------------
    {
        ConstraintModel m = base();
        add(m, mkDtTester("cons", lvar()));
        add(m, mkOp(Op::EQ, {mkDtSelector("hd", INT, lvar()), mkInt(1)}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "is"));
        VERIFY(contains(smt, "hd"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }
    {
        // A selector whose field sort is the datatype itself: `(tl l)` is a Lst,
        // and asserting it equal to another Lst exercises the recursion end to
        // end rather than only in the declaration.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkDtSelector("tl", LST, lvar()), nil()}));
        Diagnostics d;
        VERIFY(typeCheck(m, d));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(emit(m)));
    }

    // ---- Mutual recursion, and forward references. --------------------------
    // A selector may name a datatype declared LATER. Rejecting that would refuse
    // ordinary modelling, and it is why declarations are registered in one pass
    // and filled in a second.
    {
        ConstraintModel m;
        DatatypeDecl a;
        a.name = "A";
        a.constructors.push_back(DtConstructor{"mkA", {sel("toB", H::Sort::datatype("B"))}});
        a.constructors.push_back(DtConstructor{"endA", {}});
        DatatypeDecl b;
        b.name = "B";
        b.constructors.push_back(DtConstructor{"mkB", {sel("toA", H::Sort::datatype("A"))}});
        m.datatypes.push_back(a);          // A mentions B before B is declared
        m.datatypes.push_back(b);
        m.decls.push_back(decl("x", H::Sort::datatype("A")));
        add(m, mkDtTester("endA", mkIdent("x", H::Sort::datatype("A"))));
        Diagnostics d;
        VERIFY(typeCheck(m, d));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "A"));
        VERIFY(contains(smt, "B"));
    }

    // ---- Names are unique across ALL datatypes, not within one. -------------
    // Otherwise `(cons 1 nil)` names two different constructors and the checker
    // has to guess which.
    {
        ConstraintModel m = base();
        DatatypeDecl other;
        other.name = "Other";
        other.constructors.push_back(DtConstructor{"cons", {sel("x", INT)}});
        m.datatypes.push_back(other);
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        Diagnostics d;
        VERIFY(!typeCheck(m, d));
        VERIFY(contains(d.all().front().message, "unique"));
    }
    {
        // Selectors too.
        ConstraintModel m = base();
        DatatypeDecl other;
        other.name = "Other";
        other.constructors.push_back(DtConstructor{"mkOther", {sel("hd", INT)}});
        m.datatypes.push_back(other);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // ...and a datatype declared twice.
        ConstraintModel m = base();
        m.datatypes.push_back(lst());
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- A datatype with no constructors has no values. ---------------------
    // Every variable of it makes the model unsatisfiable, which is an answer
    // rather than a translation.
    {
        ConstraintModel m;
        DatatypeDecl empty;
        empty.name = "Void";
        m.datatypes.push_back(empty);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- What an application must not get away with. ------------------------
    {
        // Undeclared constructor.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {lvar(), mkDtConstructor("snoc", LST, {})}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // Wrong field count: cons takes two.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {lvar(), mkDtConstructor("cons", LST, {mkInt(1)})}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // Wrong field sort: hd is Int, and the list goes second.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {lvar(),
                             mkDtConstructor("cons", LST, {nil(), mkInt(1)})}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A selector applied to the wrong datatype -- here to an Int, which is
        // the case a frontend hits when it forgets which value it is holding.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkDtSelector("hd", INT, mkIdent("i", INT)), mkInt(1)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A selector recording the wrong result sort. mkDtSelector takes it from
        // the caller, so this is the check that the caller is not trusted.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkDtSelector("hd", LST, lvar()), nil()}));
        VERIFY(rejects(m, ErrorCode::E_INTERNAL));
    }
    {
        // A tester for a constructor of a different datatype.
        ConstraintModel m = base();
        DatatypeDecl other;
        other.name = "Other";
        other.constructors.push_back(DtConstructor{"mkOther", {}});
        m.datatypes.push_back(other);
        add(m, mkDtTester("mkOther", lvar()));      // l is a Lst, not an Other
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A tester for a name that is not a constructor at all.
        ConstraintModel m = base();
        add(m, mkDtTester("hd", lvar()));           // hd is a selector
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- Two datatype sorts are the same one exactly when their names are. --
    {
        VERIFY(sameSort(H::Sort::datatype("Lst"), H::Sort::datatype("Lst")));
        VERIFY(!sameSort(H::Sort::datatype("Lst"), H::Sort::datatype("Tree")));
        VERIFY(!sameSort(H::Sort::datatype("Lst"), H::Sort::uninterpreted("Lst")));
        VERIFY(toString(H::Sort::datatype("Lst")) == "Lst");
    }

    // ---- A datatype variable is a variable. ---------------------------------
    // features() drives pass validation; nothing here should report an int or
    // real variable that is not one.
    {
        ConstraintModel m = base();
        add(m, mkDtTester("nil", lvar()));
        VERIFY(m.features().count(feat::intVar()) == 1);   // "i" is an Int
        VERIFY(m.decls.size() == 2);
    }

    // ---- Parametric constructors: the recorded sort is the INSTANCE. --------
    // `(declare-datatypes ((Event 1)) ((par (X) ((Absent) (Present (val X))))))`.
    // A constructor's recorded sort is the instance -- `(Event Real)` -- not
    // the bare name, and its fields check against the instance's substitution
    // of the declaration's parameters, exactly as a selector's result does.
    {
        DatatypeDecl ev;
        ev.name = "Event";
        ev.params.push_back("X");
        ev.constructors.push_back(DtConstructor{"Absent", {}});
        ev.constructors.push_back(
            DtConstructor{"Present", {sel("val", H::Sort::uninterpreted("X"))}});
        const H::Sort EVENT_R = H::Sort::datatype("Event", {H::Sort::real()});

        ConstraintModel m;
        m.datatypes.push_back(ev);
        m.decls.push_back(decl("e", EVENT_R));
        add(m, mkOp(Op::EQ, {mkIdent("e", EVENT_R),
                             mkDtConstructor("Absent", EVENT_R, {})}));
        add(m, mkOp(Op::EQ, {mkIdent("e", EVENT_R),
                             mkDtConstructor("Present", EVENT_R,
                                             {mkReal("1.5")})}));
        add(m, mkOp(Op::EQ, {mkDtSelector("val", H::Sort::real(),
                                          mkIdent("e", EVENT_R)),
                             mkReal("2.5")}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "par"));
        VERIFY(contains(smt, "Event Real"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));

        // A field checked against the UNSUBSTITUTED parameter would read this
        // as "1 is Int, but val is X": the instance's X is Real.
        ConstraintModel bad_field;
        bad_field.datatypes.push_back(ev);
        bad_field.decls.push_back(decl("e", EVENT_R));
        add(bad_field, mkOp(Op::EQ, {mkIdent("e", EVENT_R),
                                     mkDtConstructor("Present", EVENT_R,
                                                     {mkInt(1)})}));
        VERIFY(rejects(bad_field, ErrorCode::E_TYPE));

        // The bare name is NOT an instance of a parametric datatype: a
        // constructor of `Event` records `(Event Real)` or it records a
        // frontend defect, which E_INTERNAL says rather than translating.
        ConstraintModel bare;
        bare.datatypes.push_back(ev);
        bare.decls.push_back(decl("e", EVENT_R));
        add(bare, mkOp(Op::EQ, {mkIdent("e", EVENT_R),
                                mkDtConstructor("Absent",
                                                H::Sort::datatype("Event"), {})}));
        VERIFY(rejects(bare, ErrorCode::E_INTERNAL));
    }

    {
        // Least and greatest fixed points must not silently be merged into
        // the same recursive declaration block by the dump dependency pass.
        ConstraintModel mixed;
        DatatypeDecl a;
        a.name = "A";
        a.coinductive = true;
        a.constructors.push_back({"makeA", {sel("getB", H::Sort::datatype("B"))}});
        DatatypeDecl b;
        b.name = "B";
        b.constructors.push_back({"makeB", {sel("getA", H::Sort::datatype("A"))}});
        mixed.datatypes = {a, b};
        VERIFY(rejects(mixed, ErrorCode::E_TYPE));
    }

    {
        // A type parameter named A is not a recursive edge to global A.
        ConstraintModel m;
        DatatypeDecl a;
        a.name = "A";
        a.coinductive = true;
        a.constructors.push_back({"ca", {sel("next", H::Sort::datatype(
            "B", {H::Sort::integer()}))}});
        DatatypeDecl b;
        b.name = "B";
        b.params = {"A"};
        b.constructors.push_back({"cb", {sel("value", H::Sort::uninterpreted("A"))}});
        m.datatypes = {a, b};
        Diagnostics diagnostics;
        VERIFY(typeCheck(m, diagnostics));
    }

    std::cout << "All HIR datatype tests passed." << std::endl;
    return 0;
}
