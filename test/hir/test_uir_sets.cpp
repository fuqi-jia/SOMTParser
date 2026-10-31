// Finite sets, from the engine up to MiniZinc.
//
// The last row of docs/languages/smtlib2.md's gap table, and the only one that
// was an *engine* gap rather than a HIR one: SORT_KIND had SK_SET and the engine
// had zero NODE_KINDs, zero oper_key_map entries and zero builders for it, so
// `(Set Int)` was a sort a model could declare and nothing could constrain.
//
// This file covers all three layers, because a theory added at one layer and not
// the next is exactly the "sort with nothing behind it" that was being fixed.
//
// Two argument orders here read backwards from their names and are SMT-LIB's:
// `set.member` takes the ELEMENT first, and `set.insert` takes the set LAST.
// Both are checked, because a symmetric check would accept the other order and
// the two spellings do not mean the same thing.

#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
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

const H::Sort INT   = H::Sort::integer();
const H::Sort BOOLS = H::Sort::boolean();
const H::Sort SETI  = H::Sort::set(INT);
const H::Sort SETB  = H::Sort::set(BOOLS);

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
    m.decls.push_back(decl("s", SETI));
    m.decls.push_back(decl("t", SETI));
    m.decls.push_back(decl("b", SETB));
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

ExprPtr set()  { return mkIdent("s", SETI); }
ExprPtr set2() { return mkIdent("t", SETI); }
ExprPtr elem() { return mkIdent("x", INT); }
ExprPtr empty(){ return mkSetConst("set.empty", SETI); }

Translation mzn(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.mzn";
    u.display_name = "t.mzn";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "minizinc";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= finite sets =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- The engine reads and re-emits the theory. --------------------------
    // The layer that did not exist. A script this library dumps must be one it
    // reads, which is the property the three defects found on 2026-08-12 all
    // broke -- and set.empty is the same shape, since its sort lives in the term.
    {
        const char* src =
            "(set-logic ALL)\n"
            "(declare-fun s () (Set Int))\n"
            "(declare-fun x () Int)\n"
            "(assert (set.member x s))\n"
            "(assert (= s (set.union (set.singleton 1) (as set.empty (Set Int)))))\n"
            "(assert (> (set.card s) 0))\n"
            "(assert (set.subset (set.insert 1 2 (as set.empty (Set Int))) s))\n"
            "(assert (= s (set.minus s (set.complement s))))\n"
            "(assert (= s (set.inter s s)))\n";
        ParserPtr p = newParser();
        VERIFY(p->parseStr(src));
        const std::string dumped = p->dumpSMT2();
        VERIFY(contains(dumped, "(Set Int)"));
        VERIFY(contains(dumped, "(as set.empty (Set Int))"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(dumped));
    }

    // ---- HIR: result sorts. -------------------------------------------------
    {
        VERIFY(sameSort(mkOp(Op::SET_SINGLETON, {elem()})->sort, SETI));
        VERIFY(sameSort(mkOp(Op::SET_UNION, {set(), set2()})->sort, SETI));
        VERIFY(sameSort(mkOp(Op::SET_MINUS, {set(), set2()})->sort, SETI));
        VERIFY(mkOp(Op::SET_MEMBER, {elem(), set()})->sort.kind == SortKind::BOOL);
        VERIFY(mkOp(Op::SET_SUBSET, {set(), set2()})->sort.kind == SortKind::BOOL);
        VERIFY(sameSort(mkOp(Op::SET_CARD, {set()})->sort, INT));
        // set.insert takes the set LAST, so the result sort comes from the last
        // argument. Taking it from the first would give Int here -- a sort that
        // type-checks nowhere and would be blamed on the caller.
        VERIFY(sameSort(mkOp(Op::SET_INSERT, {mkInt(1), mkInt(2), empty()})->sort, SETI));
    }

    // ---- Two set sorts are equal exactly when their elements are. -----------
    {
        VERIFY(sameSort(H::Sort::set(INT), H::Sort::set(INT)));
        VERIFY(!sameSort(H::Sort::set(INT), H::Sort::set(BOOLS)));
        VERIFY(!sameSort(H::Sort::set(INT), INT));
        VERIFY(toString(SETI) == "(Set Int)");
        VERIFY(toString(H::Sort::set(SETI)) == "(Set (Set Int))");
    }

    // ---- A whole model lowers and round-trips. ------------------------------
    {
        ConstraintModel m = base();
        add(m, mkOp(Op::SET_MEMBER, {elem(), set()}));
        add(m, mkOp(Op::EQ, {set(), mkOp(Op::SET_UNION, {set(), set2()})}));
        add(m, mkOp(Op::GT, {mkOp(Op::SET_CARD, {set()}), mkInt(0)}));
        add(m, mkOp(Op::SET_SUBSET, {mkOp(Op::SET_INSERT, {mkInt(1), empty()}), set()}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "set.member"));
        VERIFY(contains(smt, "set.card"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }

    // ---- set.member takes the element first. --------------------------------
    // The order that reads backwards. A symmetric check would accept both, and
    // only one of them is what SMT-LIB means.
    {
        ConstraintModel ok = base();
        add(ok, mkOp(Op::SET_MEMBER, {elem(), set()}));
        Diagnostics d;
        VERIFY(typeCheck(ok, d));

        ConstraintModel bad = base();
        add(bad, mkOp(Op::SET_MEMBER, {set(), elem()}));
        VERIFY(rejects(bad, ErrorCode::E_TYPE));
    }
    {
        // An element of the wrong sort.
        ConstraintModel m = base();
        add(m, mkOp(Op::SET_MEMBER, {mkBool(true), set()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- Mixed element sorts are refused. -----------------------------------
    // (Set Int) and (Set Bool) agree on SortKind and differ on everything that
    // matters: the bit-vector width mistake in a third theory.
    {
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {set(), mkOp(Op::SET_UNION, {set(), mkIdent("b", SETB)})}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        Diagnostics d;
        VERIFY(!typeCheck(m, d));
        VERIFY(contains(d.all().front().message, "(Set Int)"));
        VERIFY(contains(d.all().front().message, "(Set Bool)"));
    }
    {
        // set.insert's elements must match the set it inserts into.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {set(), mkOp(Op::SET_INSERT, {mkBool(true), empty()})}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // ...and its last argument must be a set at all.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {set(), mkOp(Op::SET_INSERT, {mkInt(1), mkInt(2)})}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // set.card of a non-set.
        ConstraintModel m = base();
        add(m, mkOp(Op::GT, {mkOp(Op::SET_CARD, {elem()}), mkInt(0)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- The two set constants. ---------------------------------------------
    {
        VERIFY(sameSort(mkSetConst("set.empty", SETI)->sort, SETI));
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {set(), mkSetConst("set.universe", SETI)}));
        VERIFY(contains(emit(m), "set.universe"));

        ConstraintModel bad = base();
        add(bad, mkOp(Op::EQ, {set(), mkSetConst("set.everything", SETI)}));
        VERIFY(rejects(bad, ErrorCode::E_TYPE));
    }

    // ---- MiniZinc: the producer this theory exists for. ---------------------
    {
        const Translation t = mzn(
            "var set of int: s;\nvar int: x;\nconstraint x in s;\nsolve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(contains(smt, "(Set Int)"));
        VERIFY(contains(smt, "set.member"));
    }
    {
        // `var set of 1..3` -- the element range is NOT part of the sort, so it
        // has to be materialised as a constraint. Dropping it would admit
        // members the model excludes, and nothing downstream could tell: the
        // script would be well-formed and strictly more satisfiable.
        const Translation t = mzn(
            "var set of 1..3: s;\nconstraint card(s) > 1;\nsolve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(contains(smt, "(assert (= "));
        VERIFY(contains(smt, "set.inter"));
        VERIFY(!contains(smt, "(forall "));
        VERIFY(contains(smt, "set.insert 1 2 3"));
        VERIFY(contains(smt, "set.card"));
        VERIFY(t.report().stats().num_constraints == 2);   // the range, and card
    }
    {
        // Set literals and `subset`.
        const Translation t = mzn(
            "var set of int: s;\nconstraint s subset {1,2,3};\nsolve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(contains(t.toSmt2(), "set.subset"));
    }
    {
        // The typed peer gives the empty literal its element sort. Subset of
        // the empty set constrains s to be empty; it must not drop the relation.
        const Translation t = mzn(
            "var set of int: s;\nconstraint s subset {};\nsolve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(contains(t.toSmt2(), "set.subset"));
        VERIFY(contains(t.toSmt2(), "(as set.empty (Set Int))"));
    }
    {
        // `x in s` with x of the wrong sort is caught, not coerced.
        const Translation t = mzn(
            "var set of int: s;\nvar bool: p;\nconstraint p in s;\nsolve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        // `set` is no longer a coverage gap -- which is this file's claim, and
        // is not the same as MiniZinc being complete. The assertion here used to
        // be `missing.empty()`, and that was false the whole time: `x div 2` was
        // refused while coverage() reported 8/8.
        //
        // It then became "no entry in `missing` contains the word set", which
        // was meant to keep the claim narrow -- and on 2026-08-16 a genuinely
        // unrelated gap opened, par `set of int: S = 1..n;` items, which are a
        // compile-time integer range and not this theory at all. The scan fired
        // on the WORD. A check that reads the prose of a human-facing message
        // cannot tell two constructs apart just because one of them had to name
        // the other to say what it is not.
        //
        // So the claim is made where it is actually decidable: the four blocks
        // above translate `var set of int`, `var set of 1..3`, a set literal
        // and `card`, and assert the emitted `set.*` operators. That is what
        // "sets are supported" means, and it cannot be satisfied by wording.
        Lang::Language* m = Lang::LanguageRegistry::instance().byId("minizinc");
        VERIFY(m != nullptr);
        // What survives here is the structural invariant, which no wording can
        // fake: the counts and the list agree, whatever is in them.
        VERIFY(m->coverage().missing.size()
               == m->coverage().total - m->coverage().supported);
    }

    std::cout << "All finite-set tests passed." << std::endl;
    return 0;
}
