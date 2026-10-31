// The HIR must be well-sorted before anything reads it.
//
// Nothing checked this until 2026-08-11, and the consequences were not
// symmetric. `constraint x` on an Int x translated to `(assert x)`, exited 0
// and reported fidelity `exact` -- a wrong answer that looks like a right one.
// `constraint b + 1 > 0` on a Bool b reached Parser::mkAdd, which throws, and
// killed the process. Both come from the same hole: Hir::mkOp gives every
// connective and comparison the Bool sort without looking at its arguments.
//
// The cases below are built as HIR directly rather than through a frontend, on
// purpose. A frontend that happens to type-check its own language would hide
// the hole rather than close it, and the point of checking here is that the
// check holds for every frontend, including ones not written yet.

#include "somtparser/hir/typecheck.h"

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace {

ExprPtr intVar(const char* n)  { return mkIdent(n, Sort::integer()); }
ExprPtr boolVar(const char* n) { return mkIdent(n, Sort::boolean()); }

VarDecl decl(const char* n, Sort s) {
    VarDecl d;
    d.name = n;
    d.sort = s;
    return d;
}

Constraint hard(ExprPtr f) {
    Constraint c;
    c.formula = std::move(f);
    return c;
}

/** A model with x:Int and b:Bool declared, and whatever constraint is given. */
ConstraintModel modelWith(ExprPtr formula) {
    ConstraintModel m;
    m.decls.push_back(decl("x", Sort::integer()));
    m.decls.push_back(decl("y", Sort::integer()));
    m.decls.push_back(decl("b", Sort::boolean()));
    if (formula) { m.constraints.push_back(hard(std::move(formula))); }
    return m;
}

bool accepts(const ConstraintModel& m) {
    Diagnostics d;
    const bool ok = typeCheck(m, d);
    // A checker that returned true while recording an error, or false while
    // recording none, would leave a caller unable to act on either signal.
    assert(ok == !d.hasErrors());
    return ok;
}

/** Rejected, and rejected under @p code -- the code is the bucket the
 *  evaluation counts this failure in, so getting it right is the point. */
bool rejects(const ConstraintModel& m, ErrorCode code) {
    Diagnostics d;
    if (typeCheck(m, d)) { return false; }
    if (!d.hasErrors()) { return false; }
    return d.firstErrorCode() == code;
}

} // namespace

int main() {
    std::cout << "======= HIR type checking =======\n";

    // ---- What must be accepted. A checker that rejects everything would pass
    // every negative case below, so the positives come first. ----------------
    assert(accepts(modelWith(mkOp(Op::GT, {intVar("x"), mkInt(0)}))));
    assert(accepts(modelWith(mkOp(Op::AND, {boolVar("b"), mkBool(true)}))));
    assert(accepts(modelWith(mkOp(Op::NOT, {boolVar("b")}))));
    assert(accepts(modelWith(boolVar("b"))));
    // = relates Bools as well as numbers; the ordered comparisons do not.
    assert(accepts(modelWith(mkOp(Op::EQ, {boolVar("b"), mkBool(false)}))));
    assert(accepts(modelWith(mkOp(Op::EQ, {intVar("x"), intVar("y")}))));
    assert(accepts(modelWith(mkOp(Op::EQ,
        {intVar("x"), intVar("y"), mkInt(1)}))));
    assert(accepts(modelWith(mkOp(Op::EQ,
        {boolVar("b"), mkBool(true), mkBool(false)}))));
    assert(rejects(modelWith(mkOp(Op::EQ,
        {intVar("x"), intVar("y"), boolVar("b")})), ErrorCode::E_TYPE));
    assert(rejects(modelWith(mkOp(Op::EQ, {intVar("x")})), ErrorCode::E_TYPE));
    // Nested arithmetic under a comparison.
    assert(accepts(modelWith(mkOp(Op::LE,
        {mkOp(Op::ADD, {intVar("x"), mkOp(Op::MUL, {mkInt(2), intVar("y")})}),
         mkInt(10)}))));

    // Exact rational literals have nonzero denominators, regardless of sign
    // or leading zeros. Large valid denominators must not overflow a parser.
    for (const auto* text : {"0", "+1.25", "-3/2", "0/7", "0/0007", "+1/0002",
                             "1/100000000000000000000000000000000000000"}) {
        assert(accepts(modelWith(mkOp(Op::EQ, {mkReal(text), mkReal("0")}))));
    }
    for (const auto* text : {"1/0", "0/0", "-1/000", "+1/00"}) {
        assert(rejects(modelWith(mkOp(Op::EQ, {mkReal(text), mkReal("0")})),
                       ErrorCode::E_TYPE));
    }
    // A division expression remains well-sorted even at a zero denominator.
    assert(accepts(modelWith(mkOp(Op::EQ,
        {mkOp(Op::DIV_REAL, {mkReal("1"), mkReal("0")}), mkReal("0")}))));

    // ---- Constraints must be Bool. -----------------------------------------
    // `constraint x` used to become `(assert x)` on an Int and exit 0.
    assert(rejects(modelWith(intVar("x")), ErrorCode::E_TYPE));
    // `constraint 1` used to become `(assert 1)`.
    assert(rejects(modelWith(mkInt(1)), ErrorCode::E_TYPE));
    assert(rejects(modelWith(mkOp(Op::ADD, {intVar("x"), mkInt(1)})), ErrorCode::E_TYPE));

    // ---- Operators must agree with their arguments. -------------------------
    // The abort case: mkOp gave `b + 1` the sort Int and Parser::mkAdd threw.
    assert(rejects(modelWith(mkOp(Op::GT, {mkOp(Op::ADD, {boolVar("b"), mkInt(1)}),
                                           mkInt(0)})),
                   ErrorCode::E_TYPE));
    // A connective over a number.
    assert(rejects(modelWith(mkOp(Op::AND, {intVar("x"), mkBool(true)})),
                   ErrorCode::E_TYPE));
    // An ordered comparison over a Bool.
    assert(rejects(modelWith(mkOp(Op::LT, {boolVar("b"), mkInt(1)})),
                   ErrorCode::E_TYPE));
    // = across sorts that have no common domain.
    assert(rejects(modelWith(mkOp(Op::EQ, {boolVar("b"), intVar("x")})),
                   ErrorCode::E_TYPE));

    // ---- Arity. -------------------------------------------------------------
    {
        // Built by hand: mkOp does not enforce arity, and HirToParser's own
        // arity checks run after the passes have already seen the model.
        auto bad = std::make_shared<Expr>();
        bad->kind = ExprKind::OP;
        bad->op = Op::NOT;
        bad->sort = Sort::boolean();
        bad->args = {boolVar("b"), boolVar("b")};
        assert(rejects(modelWith(bad), ErrorCode::E_TYPE));
    }
    {
        auto bad = std::make_shared<Expr>();
        bad->kind = ExprKind::OP;
        bad->op = Op::LT;
        bad->sort = Sort::boolean();
        bad->args = {intVar("x")};
        assert(rejects(modelWith(bad), ErrorCode::E_TYPE));
    }

    // ---- Identifiers must resolve, and to the sort they claim. --------------
    assert(rejects(modelWith(mkOp(Op::GT, {intVar("nosuch"), mkInt(0)})),
                   ErrorCode::E_TYPE));
    {
        // The frontend read `x` off a stale scope and called it Bool. Left
        // alone, the recorded sort decides how the term lowers.
        ConstraintModel m = modelWith(nullptr);
        m.constraints.push_back(hard(mkIdent("x", Sort::boolean())));
        assert(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- Declarations. ------------------------------------------------------
    {
        // `var int: x; var bool: x;` emitted one declare-fun and dropped the
        // other declaration without a word.
        ConstraintModel m;
        m.decls.push_back(decl("x", Sort::integer()));
        m.decls.push_back(decl("x", Sort::boolean()));
        assert(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A bound on something with no order.
        ConstraintModel m;
        m.decls.push_back(decl("b", Sort::boolean()));
        m.decls.back().lower_bound = mkInt(0);
        assert(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A non-numeric bound on a numeric variable.
        ConstraintModel m;
        m.decls.push_back(decl("x", Sort::integer()));
        m.decls.back().upper_bound = mkBool(true);
        assert(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // The ordinary bounded declaration still passes.
        ConstraintModel m;
        m.decls.push_back(decl("x", Sort::integer()));
        m.decls.back().lower_bound = mkInt(1);
        m.decls.back().upper_bound = mkInt(9);
        assert(accepts(m));
    }

    {
        // Bounds belong to a simultaneous model. Later declarations and a
        // different declaration order must expose the same global symbols.
        ConstraintModel m;
        m.decls = {decl("dependent", Sort::integer()), decl("later", Sort::integer()),
                   decl("upper", Sort::integer())};
        m.decls[0].lower_bound = mkOp(Op::SUB, {intVar("later"), mkInt(1)});
        m.decls[0].upper_bound = mkOp(Op::ADD, {intVar("upper"), mkInt(2)});
        assert(accepts(m));
        std::swap(m.decls[0], m.decls[2]);
        assert(accepts(m));
        // A bound is an inequality, not a recursive initializer; mutual
        // references constrain the relation without requiring an evaluation order.
        m.decls[1].lower_bound = intVar("dependent");
        assert(accepts(m));
        m.decls[2].upper_bound = intVar("missing");
        assert(rejects(m, ErrorCode::E_TYPE));
    }
    {
        ConstraintModel m;
        m.decls = {decl("dependent", Sort::integer()), decl("later", Sort::boolean())};
        // A claimed Int sort may not disguise a later Boolean declaration.
        m.decls[0].lower_bound = intVar("later");
        assert(rejects(m, ErrorCode::E_TYPE));
        m.decls[0].lower_bound = boolVar("later");
        assert(rejects(m, ErrorCode::E_TYPE));
    }
    {
        ConstraintModel m;
        m.decls = {decl("dependent", Sort::integer()), decl("later", Sort::integer()),
                   decl("later", Sort::boolean())};
        m.decls[0].lower_bound = intVar("later");
        assert(rejects(m, ErrorCode::E_TYPE));
        m.decls.pop_back();
        FunDecl function;
        function.name = "later";
        function.result = Sort::integer();
        m.funs.push_back(function);
        assert(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- Objectives. --------------------------------------------------------
    {
        // `solve minimize b` on a Bool emitted (minimize b) and reported exact.
        ConstraintModel m = modelWith(nullptr);
        Objective o;
        o.kind = ObjKind::MINIMIZE;
        o.term = boolVar("b");
        o.name = "obj0";
        m.objectives.push_back(o);
        assert(rejects(m, ErrorCode::E_TYPE));
    }
    {
        ConstraintModel m = modelWith(nullptr);
        Objective o;
        o.kind = ObjKind::MAXIMIZE;
        o.term = mkOp(Op::ADD, {intVar("x"), intVar("y")});
        o.name = "obj0";
        m.objectives.push_back(o);
        assert(accepts(m));
    }
    {
        // An objective named after a variable rebinds that variable in the
        // emitted script. The frontend that minted the name is at fault, so
        // this is E_INTERNAL and must not inflate the language-coverage bucket.
        ConstraintModel m = modelWith(nullptr);
        Objective o;
        o.kind = ObjKind::MINIMIZE;
        o.term = intVar("x");
        o.name = "x";
        m.objectives.push_back(o);
        assert(rejects(m, ErrorCode::E_INTERNAL));
    }
    {
        ConstraintModel m = modelWith(nullptr);
        Objective o;
        o.kind = ObjKind::MINIMIZE;
        o.term = intVar("x");
        o.name = "same";
        m.objectives.push_back(o);
        m.objectives.push_back(o);
        assert(rejects(m, ErrorCode::E_INTERNAL));
    }

    // ---- Several objectives need a stated combination. ----------------------
    // Silence is not "independent": the emitter would produce several
    // (minimize t) commands, whose documented meaning under Z3 is
    // lexicographic, so leaving it unsaid picks a semantics rather than
    // deferring one.
    {
        ConstraintModel m = modelWith(nullptr);
        Objective a;
        a.kind = ObjKind::MINIMIZE;
        a.term = intVar("x");
        a.name = "obj0";
        Objective b = a;
        b.term = intVar("y");
        b.name = "obj1";
        m.objectives.push_back(a);
        m.objectives.push_back(b);

        // No combination stated -> refused.
        assert(rejects(m, ErrorCode::E_INTERNAL));

        // Any of the five is accepted.
        for (auto c : {ObjectiveCombination::LEXICOGRAPHIC,
                       ObjectiveCombination::PARETO,
                       ObjectiveCombination::BOX,
                       ObjectiveCombination::MINMAX,
                       ObjectiveCombination::MAXMIN}) {
            ConstraintModel ok = m;
            ok.objective_combination = c;
            assert(accepts(ok));
        }
    }
    {
        // ...and the converse: a combination with fewer than two objectives is
        // also wrong, so the field cannot be set decoratively.
        ConstraintModel m = modelWith(nullptr);
        Objective o;
        o.kind = ObjKind::MINIMIZE;
        o.term = intVar("x");
        o.name = "obj0";
        m.objectives.push_back(o);
        m.objective_combination = ObjectiveCombination::PARETO;
        assert(rejects(m, ErrorCode::E_INTERNAL));

        ConstraintModel empty;
        empty.objective_combination = ObjectiveCombination::LEXICOGRAPHIC;
        assert(rejects(empty, ErrorCode::E_INTERNAL));
    }

    // ---- Every violation is reported, not just the first. -------------------
    // A batch run reads these to decide what a frontend still gets wrong;
    // stopping at the first would understate that by an unknown factor.
    {
        ConstraintModel m = modelWith(nullptr);
        m.constraints.push_back(hard(intVar("x")));
        m.constraints.push_back(hard(mkInt(3)));
        m.constraints.push_back(hard(mkOp(Op::AND, {intVar("y"), mkBool(true)})));
        Diagnostics d;
        assert(!typeCheck(m, d));
        std::size_t errors = 0;
        for (const auto& e : d.all()) {
            if (e.severity == Severity::ERROR) { ++errors; }
        }
        assert(errors == 3);
    }

    // ---- Diagnostics carry a location. --------------------------------------
    // Expr::loc used to be set by nothing, so every message pointed at 0:0 and
    // a benchmark author had no way to find the term complained about.
    {
        SourceLoc at;
        at.file = "m.mzn";
        at.line = 7;
        at.column = 12;
        ConstraintModel m = modelWith(nullptr);
        m.constraints.push_back(hard(mkIdent("x", Sort::integer(), at)));
        Diagnostics d;
        assert(!typeCheck(m, d));
        assert(d.all().front().loc.file == "m.mzn");
        assert(d.all().front().loc.line == 7);
        assert(d.all().front().loc.column == 12);
    }
    {
        // When the expression carries none, the enclosing item's location is
        // used rather than nothing at all.
        ConstraintModel m = modelWith(nullptr);
        Constraint c = hard(intVar("x"));
        c.loc.file = "m.mzn";
        c.loc.line = 3;
        m.constraints.push_back(c);
        Diagnostics d;
        assert(!typeCheck(m, d));
        assert(d.all().front().loc.file == "m.mzn");
        assert(d.all().front().loc.line == 3);
    }

    // ---- The empty model is well-sorted. ------------------------------------
    // It is not this checker's job to decide whether a model says anything;
    // a language that permits an empty model is entitled to one.
    {
        ConstraintModel m;
        assert(accepts(m));
    }

    // ---- IEEE_BV_TO_FP: the bit pattern must be exactly the format's width. --
    // `((_ to_fp 8 24) bv)` reinterprets rather than converts, so a 16-bit
    // argument at format 8+24 is not a small float, it is a different meaning.
    {
        ConstraintModel m;
        m.decls.push_back(decl("v", Sort::bitvec(32)));
        m.decls.push_back(decl("g", Sort::floating(8, 24)));
        m.constraints.push_back(hard(mkOp(Op::FP_EQ,
            {mkIeeeBvToFp(mkIdent("v", Sort::bitvec(32)), 8, 24),
             mkIdent("g", Sort::floating(8, 24))})));
        assert(accepts(m));
    }
    {
        ConstraintModel m;
        m.decls.push_back(decl("v", Sort::bitvec(16)));
        m.decls.push_back(decl("g", Sort::floating(8, 24)));
        m.constraints.push_back(hard(mkOp(Op::FP_EQ,
            {mkIeeeBvToFp(mkIdent("v", Sort::bitvec(16)), 8, 24),
             mkIdent("g", Sort::floating(8, 24))})));
        assert(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A non-bit-vector source is a conversion question, not a
        // reinterpretation: Real goes to TO_FP with a rounding mode.
        ConstraintModel m;
        m.decls.push_back(decl("r", Sort::real()));
        m.decls.push_back(decl("g", Sort::floating(8, 24)));
        m.constraints.push_back(hard(mkOp(Op::FP_EQ,
            {mkIeeeBvToFp(mkIdent("r", Sort::real()), 8, 24),
             mkIdent("g", Sort::floating(8, 24))})));
        assert(rejects(m, ErrorCode::E_TYPE));
    }

    std::cout << "All HIR type checking tests passed." << std::endl;
    return 0;
}
