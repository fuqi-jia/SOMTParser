// Tuples, from the engine up to the SMT-LIB frontend.
//
// The same shape as the set gap this file's sibling pins, one theory over, and
// found the same way. The ENGINE had all of it: SORT_KIND::SK_TUPLE, five
// NODE_KINDs, `createTupleSort`, five builders with their own range checks,
// and a printer that knows `((_ tuple.select i) t)` spells its index inside
// the operator. The HIR had no sort for a tuple. So `liftSort` refused at the
// DECLARATION, every one of the five operators was unreachable, and three
// corpus files reported "sort '(Tuple Int Bool)' has no HIR counterpart" --
// which reads like a missing operator table and was the opposite: a full table
// with no sort under it (CLAUDE.md §6).
//
// What this file pins that the operator sweep cannot:
//
//   * the sweep asserts text equality after a round trip, which is silent
//     about WHICH field a select reads as long as the index survives. Here the
//     fields have different sorts and the result sorts are compared.
//   * the refusals. An index past the end of a tuple, an update that changes a
//     field's sort, and a `tuple.unit` recording a non-empty tuple sort are
//     all things a round trip never produces and a hand-built model can.
//   * `UnitTuple` -- the NULLARY tuple sort, which is a real sort with exactly
//     one value and not a malformed one. Every emptiness check in the lift,
//     the builders and the checker has to agree about that, and there are four
//     of them.

#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace H = SOMTParser::Uir::Hir;

namespace {

const H::Sort INT  = H::Sort::integer();
const H::Sort BOOLS = H::Sort::boolean();
const H::Sort TIB  = H::Sort::tuple({INT, BOOLS});   // (Tuple Int Bool)
const H::Sort TBI  = H::Sort::tuple({BOOLS, INT});   // (Tuple Bool Int)
const H::Sort TI   = H::Sort::tuple({INT});          // (Tuple Int)
const H::Sort UNIT = H::Sort::tuple({});             // UnitTuple

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

VarDecl decl(const char* n, H::Sort s) {
    VarDecl d;
    d.name = n;
    d.sort = std::move(s);
    return d;
}

ConstraintModel base() {
    ConstraintModel m;
    m.decls.push_back(decl("tp", TIB));
    m.decls.push_back(decl("rp", TBI));
    m.decls.push_back(decl("ut", UNIT));
    m.decls.push_back(decl("x", INT));
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

ExprPtr tup()  { return mkIdent("tp", TIB); }
ExprPtr unit() { return mkIdent("ut", UNIT); }

Translation smt(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.smt2";
    u.display_name = "t.smt2";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "smtlib2";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= tuples =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- The engine reads and re-emits the theory. --------------------------
    // Pinned first because everything below depends on it, and because a script
    // this library dumps must be one it reads.
    {
        const char* src =
            "(set-logic ALL)\n"
            "(declare-fun tp () (Tuple Int Bool))\n"
            "(declare-fun ut () UnitTuple)\n"
            "(assert (= tp (tuple 1 true)))\n"
            "(assert (= ((_ tuple.select 0) tp) 1))\n"
            "(assert (= ((_ tuple.update 0) tp 2) tp))\n"
            "(assert (distinct ut tuple.unit))\n";
        ParserPtr p = newParser();
        VERIFY(p->parseStr(src));
        const std::string dumped = p->dumpSMT2();
        VERIFY(contains(dumped, "(Tuple Int Bool)"));
        // The nullary tuple sort has its own spelling. `(Tuple)` would be a
        // sort no reader accepts, including this one.
        VERIFY(contains(dumped, "UnitTuple"));
        VERIFY(!contains(dumped, "(Tuple)"));
        VERIFY(contains(dumped, "((_ tuple.select 0) tp)"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(dumped));
    }

    // ---- HIR: two tuple sorts are equal when their FIELDS are, in order. ----
    {
        VERIFY(sameSort(TIB, H::Sort::tuple({INT, BOOLS})));
        // Order matters. A comparison that treated the fields as a set -- or
        // compared only the arity -- would make these one sort, and a value of
        // one would be usable where the other was declared.
        VERIFY(!sameSort(TIB, TBI));
        // Arity matters.
        VERIFY(!sameSort(TIB, TI));
        VERIFY(!sameSort(TI, UNIT));
        // UnitTuple is a sort, and it is equal to itself: it has exactly one
        // value, so two occurrences of it must compare equal or `tuple.unit`
        // could never be asserted equal to a variable of its own sort.
        VERIFY(sameSort(UNIT, H::Sort::tuple({})));
        // ...and it is not Bool, which is what every "malformed, fall back to
        // Bool" path in the builders produces. If those two compared equal the
        // fallbacks would be invisible.
        VERIFY(!sameSort(UNIT, BOOLS));
        VERIFY(toString(UNIT) == "UnitTuple");
        VERIFY(toString(TIB) == "(Tuple Int Bool)");
    }

    // ---- HIR: result sorts. -------------------------------------------------
    {
        VERIFY(sameSort(mkTuple({mkInt("1"), mkBool(true)})->sort, TIB));
        VERIFY(sameSort(mkTupleUnit()->sort, UNIT));
        // select reads the i-th FIELD, and the two fields here have different
        // sorts -- which is the whole reason the prelude is heterogeneous.
        VERIFY(sameSort(mkTupleSelect(tup(), 0)->sort, INT));
        VERIFY(sameSort(mkTupleSelect(tup(), 1)->sort, BOOLS));
        // update yields the TUPLE, not the field. Getting this wrong gives
        // `((_ tuple.update 0) tp 2)` the sort Int, and the mistake surfaces
        // somewhere else entirely.
        VERIFY(sameSort(mkTupleUpdate(tup(), 0, mkInt("2"))->sort, TIB));
        // project can reorder, narrow, or empty a tuple.
        VERIFY(sameSort(mkTupleProject(tup(), {1, 0})->sort, TBI));
        VERIFY(sameSort(mkTupleProject(tup(), {0})->sort, TI));
        VERIFY(sameSort(mkTupleProject(tup(), {})->sort, UNIT));
        // The indices are kept where SMT-LIB puts them -- in the operator --
        // and not as arguments. A lift that made them arguments would
        // round-trip as `(tuple.select tp 0)`, which no solver reads.
        const ExprPtr sel = mkTupleSelect(tup(), 1);
        VERIFY(sel->indices.size() == 1 && sel->indices[0] == 1);
        VERIFY(sel->args.size() == 1);
    }

    // ---- The checker accepts what is well sorted. ---------------------------
    {
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {tup(), mkTuple({mkInt("1"), mkBool(true)})}));
        add(m, mkOp(Op::EQ, {mkTupleSelect(tup(), 0), mkIdent("x", INT)}));
        add(m, mkTupleSelect(tup(), 1));
        add(m, mkOp(Op::EQ, {mkTupleUpdate(tup(), 0, mkInt("2")), tup()}));
        add(m, mkOp(Op::EQ, {mkTupleProject(tup(), {1, 0}), mkIdent("rp", TBI)}));
        add(m, mkOp(Op::DISTINCT, {unit(), mkTupleUnit()}));
        const std::string out = emit(m);
        VERIFY(contains(out, "(Tuple Int Bool)"));
        VERIFY(contains(out, "UnitTuple"));
        VERIFY(contains(out, "((_ tuple.select 0) tp)"));
        VERIFY(contains(out, "((_ tuple.project 1 0) tp)"));
        VERIFY(contains(out, "tuple.unit"));
        // What it emits, it reads.
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(out));
    }

    // ---- ...and refuses what is not. ----------------------------------------
    {
        // A select on something that is not a tuple. Refused here rather than
        // at `Parser::mkTupleSelect`, which reports through the engine's error
        // channel and yields an unknown node -- a type error surfacing as a
        // lowering failure with no source location.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkTupleSelect(mkIdent("x", INT), 0), mkIdent("x", INT)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // An index past the end. `(Tuple Int Bool)` has fields 0 and 1.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkTupleSelect(tup(), 2), mkIdent("x", INT)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // Out of range inside a PROJECT, where the list is variable-length and
        // an off-by-one is easiest to write.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkTupleProject(tup(), {0, 2}), mkIdent("rp", TBI)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // An update whose value does not have the field's sort. Without this
        // check an update could silently change a tuple's sort while still
        // recording the old one, and the emitted script would be ill-sorted.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkTupleUpdate(tup(), 0, mkBool(true)), tup()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // `tuple.unit` recording a non-empty tuple sort: a value of a sort
        // that has no such value. An E_INTERNAL, because no source can write
        // it -- only a frontend building the literal by hand.
        ConstraintModel m = base();
        auto bad = std::make_shared<Expr>();
        bad->kind = ExprKind::LIT_TUPLE_UNIT;
        bad->sort = TI;
        add(m, mkOp(Op::EQ, {bad, mkTupleProject(tup(), {0})}));
        VERIFY(rejects(m, ErrorCode::E_INTERNAL));
    }

    // ---- End to end, through the SMT-LIB frontend. --------------------------
    // The three corpus files' shapes. Each was refused at its declaration
    // before the sort existed, so none of them reached an operator.
    {
        const Translation t = smt(
            "(set-logic ALL)\n"
            "(declare-fun x () (Tuple Int Bool))\n"
            "(assert (not (= x (tuple 0 false))))\n"
            "(check-sat)\n");
        VERIFY(t.ok());
        VERIFY(contains(t.toSmt2(), "(Tuple Int Bool)"));
        VERIFY(contains(t.toSmt2(), "(tuple 0 false)"));
    }
    {
        const Translation t = smt(
            "(set-logic ALL)\n"
            "(declare-fun x () (Tuple Int Int))\n"
            "(assert (= ((_ tuple.select 0) x) 5))\n"
            "(check-sat)\n");
        VERIFY(t.ok());
        // Field 0 and not field 1. Both are Int here -- this is the one place
        // the sorts cannot tell them apart -- so the index is asserted in the
        // text, which is the only thing left that can.
        VERIFY(contains(t.toSmt2(), "((_ tuple.select 0) x)"));
        VERIFY(!contains(t.toSmt2(), "((_ tuple.select 1) x)"));
    }
    {
        const Translation t = smt(
            "(set-logic ALL)\n"
            "(declare-fun a () UnitTuple)\n"
            "(assert (distinct a tuple.unit))\n"
            "(check-sat)\n");
        VERIFY(t.ok());
        VERIFY(contains(t.toSmt2(), "UnitTuple"));
        VERIFY(contains(t.toSmt2(), "tuple.unit"));
    }

    // ---- The lift, directly: indices land in indices. -----------------------
    // The sweep asserts the text comes back equal, which is satisfied by any
    // representation that prints the same. This asserts the representation,
    // because the engine and the HIR disagree about where an index lives and
    // that disagreement is what the three indexed operators exist to bridge.
    {
        ParserPtr p = newParser();
        VERIFY(p->parseStr("(set-logic ALL)\n"
                           "(declare-fun tp () (Tuple Int Bool))\n"
                           "(assert (= ((_ tuple.update 1) tp true) tp))\n"));
        Lower::ParserToHir up(p);
        ConstraintModel m;
        Diagnostics d;
        VERIFY(up.lift(m, d));
        VERIFY(!d.hasErrors());
        VERIFY(typeCheck(m, d));
        VERIFY(m.constraints.size() == 1);
        const ExprPtr eq = m.constraints[0].formula;
        VERIFY(eq->kind == ExprKind::OP && eq->args.size() == 2);
        const ExprPtr upd = eq->args[0]->kind == ExprKind::OP
                                    && eq->args[0]->op == Op::TUPLE_UPDATE
                                ? eq->args[0] : eq->args[1];
        VERIFY(upd->op == Op::TUPLE_UPDATE);
        // Two arguments and one index -- the tuple and the replacement value,
        // with the index between them in the engine's child list. A lift that
        // took "everything after the first child" as indices would find two
        // indices here and no value.
        VERIFY(upd->args.size() == 2);
        VERIFY(upd->indices.size() == 1 && upd->indices[0] == 1);
        VERIFY(sameSort(upd->args[1]->sort, BOOLS));
    }

    std::cout << "All tuple tests passed.\n";
    return 0;
}
