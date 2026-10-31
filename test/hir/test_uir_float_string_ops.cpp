// The floating-point and string operator sets.
//
// Same shape as the bit-vector slice: SortKind gained FLOAT and STRING, which
// let a variable be *declared*, and without operators the sorts could be
// declared and never used. docs/languages/smtlib2.md §4.1 measured the gap at 44
// floating-point and 44 string kinds in the engine against none in the HIR.
//
// Two things here are not bit-vectors again.
//
// The first is that RoundingMode is a SORT. SMT-LIB gives it five constants and
// permits a variable of that sort, so `fp.add rm x y` with a symbolic rm is a
// legal and useful question -- which rounding mode makes the property fail. An
// IR that put the mode on the operator could not ask it.
//
// The second is fp.eq, and it is the reason this file exists rather than a
// smaller one. **fp.eq is not `=`.** fp.eq is IEEE-754 equality: NaN equals
// nothing, including itself, and +0 equals -0. SMT-LIB's `=` on Float is
// structural: NaN = NaN holds and +0 = -0 does not. Both are Float x Float ->
// Bool. Both type-check. They disagree on exactly the values floating-point bugs
// live at, so translating one as the other produces a well-formed script that
// answers a different question -- and nothing downstream can tell.

#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <set>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace H = SOMTParser::Uir::Hir;

namespace {

const H::Sort F32 = H::Sort::floating(8, 24);     // single
const H::Sort F64 = H::Sort::floating(11, 53);    // double
const H::Sort STR = H::Sort::string();
const H::Sort INT = H::Sort::integer();
const H::Sort RM  = H::Sort::roundingMode();

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

VarDecl decl(const char* n, H::Sort s) {
    VarDecl d;
    d.name = n;
    d.sort = std::move(s);
    return d;
}

/** f, g at single precision; d at double; s, t strings; i an Int. */
ConstraintModel base() {
    ConstraintModel m;
    m.decls.push_back(decl("f", F32));
    m.decls.push_back(decl("g", F32));
    m.decls.push_back(decl("d", F64));
    m.decls.push_back(decl("s", STR));
    m.decls.push_back(decl("t", STR));
    m.decls.push_back(decl("i", INT));
    return m;
}

void assertTerm(ConstraintModel& m, const ExprPtr& term) {
    Constraint c;
    if (term->sort.kind == SortKind::BOOL) {
        c.formula = term;
    } else {
        const std::string name = "r" + std::to_string(m.constraints.size());
        m.decls.push_back(decl(name.c_str(), term->sort));
        c.formula = mkOp(Op::EQ, {term, mkIdent(name, term->sort)});
    }
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

std::string assertionOf(const ConstraintModel& m) {
    const std::string s = emit(m);
    const std::size_t a = s.find("(assert");
    VERIFY(a != std::string::npos);
    return s.substr(a, s.find('\n', a) - a);
}

ExprPtr rne() { return mkRoundingMode("RNE"); }
ExprPtr f()   { return mkIdent("f", F32); }
ExprPtr g()   { return mkIdent("g", F32); }
ExprPtr str() { return mkIdent("s", STR); }
ExprPtr str2(){ return mkIdent("t", STR); }
ExprPtr num() { return mkIdent("i", INT); }

struct Case {
    Op                    op;
    const char*           smtlib;
    std::vector<ExprPtr>  args;
};

std::vector<Case> allCases() {
    return {
        {Op::FP_ADD, "fp.add", {rne(), f(), g()}},
        {Op::FP_SUB, "fp.sub", {rne(), f(), g()}},
        {Op::FP_MUL, "fp.mul", {rne(), f(), g()}},
        {Op::FP_DIV, "fp.div", {rne(), f(), g()}},
        {Op::FP_FMA, "fp.fma", {rne(), f(), g(), f()}},
        {Op::FP_SQRT, "fp.sqrt", {rne(), f()}},
        {Op::FP_ROUND_TO_INTEGRAL, "fp.roundToIntegral", {rne(), f()}},
        {Op::FP_ABS, "fp.abs", {f()}},
        {Op::FP_NEG, "fp.neg", {f()}},
        {Op::FP_REM, "fp.rem", {f(), g()}},
        {Op::FP_MIN, "fp.min", {f(), g()}},
        {Op::FP_MAX, "fp.max", {f(), g()}},
        {Op::FP_LEQ, "fp.leq", {f(), g()}},
        {Op::FP_LT,  "fp.lt",  {f(), g()}},
        {Op::FP_GEQ, "fp.geq", {f(), g()}},
        {Op::FP_GT,  "fp.gt",  {f(), g()}},
        {Op::FP_EQ,  "fp.eq",  {f(), g()}},
        {Op::FP_IS_NORMAL,    "fp.isNormal",    {f()}},
        {Op::FP_IS_SUBNORMAL, "fp.isSubnormal", {f()}},
        {Op::FP_IS_ZERO,      "fp.isZero",      {f()}},
        {Op::FP_IS_INFINITE,  "fp.isInf",       {f()}},
        {Op::FP_IS_NAN,       "fp.isNaN",       {f()}},
        {Op::FP_IS_NEGATIVE,  "fp.isNeg",       {f()}},
        {Op::FP_IS_POSITIVE,  "fp.isPos",       {f()}},
        {Op::STR_CONCAT,      "str.++",         {str(), str2()}},
        {Op::STR_LEN,         "str.len",        {str()}},
        {Op::STR_AT,          "str.",           {str(), num()}},
        {Op::STR_SUBSTR,      "str.substr",     {str(), num(), num()}},
        {Op::STR_INDEXOF,     "str.indexof",    {str(), str2(), num()}},
        {Op::STR_REPLACE,     "str.replace",    {str(), str2(), str()}},
        {Op::STR_REPLACE_ALL, "str.replace_all",{str(), str2(), str()}},
        {Op::STR_CONTAINS,    "str.contains",   {str(), str2()}},
        {Op::STR_PREFIXOF,    "str.prefixof",   {str(), str2()}},
        {Op::STR_SUFFIXOF,    "str.suffixof",   {str(), str2()}},
        {Op::STR_LT,          "str.",           {str(), str2()}},
        {Op::STR_LE,          "str.",           {str(), str2()}},
        {Op::STR_TO_INT,      "str.to_int",     {str()}},
        {Op::STR_FROM_INT,    "str.from_int",   {num()}},
    };
}

} // namespace

int main() {
    std::cout << "======= HIR float and string operators =======\n";

    // ---- Every operator type-checks, lowers, and emits. ---------------------
    // Walked, not sampled: an operator added to the enum with no lowering fails
    // here rather than surfacing three languages later.
    {
        for (const Case& c : allCases()) {
            ConstraintModel m = base();
            assertTerm(m, mkOp(c.op, c.args));
            const std::string line = assertionOf(m);
            if (!contains(line, c.smtlib)) {
                std::cerr << "operator did not reach the script: " << line << std::endl;
                VERIFY(false);
            }
        }
    }

    // ---- No two of them are the same operator. ------------------------------
    {
        std::set<std::string> seen;
        for (const Case& c : allCases()) {
            ConstraintModel m = base();
            assertTerm(m, mkOp(c.op, c.args));
            VERIFY(seen.insert(assertionOf(m)).second);
        }
    }

    // ---- Everything emitted is SMT-LIB a parser accepts. --------------------
    {
        for (const Case& c : allCases()) {
            ConstraintModel m = base();
            assertTerm(m, mkOp(c.op, c.args));
            ParserPtr reader = newParser();
            VERIFY(reader->parseStr(emit(m)));
        }
    }

    // ---- fp.eq is not `=`. --------------------------------------------------
    // The finding this file is built around. Both are Float x Float -> Bool and
    // both type-check; they disagree on NaN and on signed zero. If a future
    // refactor routed FP_EQ through the structural builder -- the obvious
    // simplification, since "equality is equality" -- this is the only thing
    // that would notice.
    {
        ConstraintModel ieee = base();
        assertTerm(ieee, mkOp(Op::FP_EQ, {f(), g()}));
        ConstraintModel structural = base();
        assertTerm(structural, mkOp(Op::EQ, {f(), g()}));

        const std::string a = assertionOf(ieee);
        const std::string b = assertionOf(structural);
        VERIFY(a != b);
        VERIFY(contains(a, "fp.eq"));
        VERIFY(!contains(b, "fp.eq"));
        // ...and the structural one really is plain `=`, not some third thing.
        VERIFY(contains(b, "(= "));
    }

    // ---- Rounding modes. ----------------------------------------------------
    {
        // All five are accepted and reach the script.
        for (const char* mode : {"RNE", "RNA", "RTP", "RTN", "RTZ"}) {
            ConstraintModel m = base();
            assertTerm(m, mkOp(Op::FP_ADD, {mkRoundingMode(mode), f(), g()}));
            VERIFY(contains(emit(m), mode));
        }
    }
    {
        // A sixth is not a rounding mode. The engine's builder takes the name as
        // a string, so an unchecked one is emitted verbatim and fails in
        // whatever reads the script -- three layers from its cause.
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::FP_ADD, {mkRoundingMode("RNEAREST"), f(), g()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // The mode may be a VARIABLE. This is the reason ROUNDING_MODE is a sort
        // and not an operator attribute: `for which rounding mode does this
        // fail` is a question the format can ask and the IR must be able to hold.
        ConstraintModel m = base();
        m.decls.push_back(decl("rm", RM));
        assertTerm(m, mkOp(Op::FP_ADD, {mkIdent("rm", RM), f(), g()}));
        Diagnostics d;
        VERIFY(typeCheck(m, d));
        VERIFY(contains(emit(m), "rm"));
    }
    {
        // The rounding mode is the FIRST argument, and the result sort comes
        // from the second. Deriving it from args[0] would make every fp.add a
        // RoundingMode -- which is what an ARG0 rule would have done.
        const ExprPtr e = mkOp(Op::FP_ADD, {rne(), f(), g()});
        VERIFY(sameSort(e->sort, F32));
    }
    {
        // Omitting the rounding mode is an arity error, not a two-argument
        // fp.add: SMT-LIB has no unrounded fp.add to fall back on.
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ, {mkOp(Op::FP_ADD, {f(), g()}), f()});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // ...and passing a Float where the mode belongs is a sort error.
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ, {mkOp(Op::FP_ADD, {f(), f(), g()}), f()});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- Two float formats are two sorts. -----------------------------------
    // The bit-vector width mistake in another theory: single and double agree on
    // SortKind and differ on everything that matters.
    {
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ,
            {mkOp(Op::FP_ADD, {rne(), f(), mkIdent("d", F64)}), f()});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        Diagnostics diag;
        VERIFY(!typeCheck(m, diag));
        VERIFY(contains(diag.all().front().message, "(_ FloatingPoint 8 24)"));
        VERIFY(contains(diag.all().front().message, "(_ FloatingPoint 11 53)"));
    }
    {
        // Comparisons too, not only arithmetic.
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::FP_LT, {f(), mkIdent("d", F64)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- String result sorts are not all String. ----------------------------
    // str.len and str.indexof yield Int, the predicates yield Bool, and getting
    // one wrong would be caught only here: mkOp derives the sort and typeCheck
    // re-derives it, so both have to agree with SMT-LIB and not merely with
    // each other.
    {
        VERIFY(sameSort(mkOp(Op::STR_LEN, {str()})->sort, INT));
        VERIFY(sameSort(mkOp(Op::STR_INDEXOF, {str(), str2(), num()})->sort, INT));
        VERIFY(sameSort(mkOp(Op::STR_TO_INT, {str()})->sort, INT));
        VERIFY(sameSort(mkOp(Op::STR_FROM_INT, {num()})->sort, STR));
        VERIFY(sameSort(mkOp(Op::STR_AT, {str(), num()})->sort, STR));
        VERIFY(sameSort(mkOp(Op::STR_SUBSTR, {str(), num(), num()})->sort, STR));
        VERIFY(sameSort(mkOp(Op::STR_CONCAT, {str(), str2()})->sort, STR));
        VERIFY(mkOp(Op::STR_CONTAINS, {str(), str2()})->sort.kind == SortKind::BOOL);
        VERIFY(mkOp(Op::STR_LT, {str(), str2()})->sort.kind == SortKind::BOOL);
    }

    // ---- The positional signatures are enforced. ----------------------------
    {
        // str.at takes (String, Int); the arguments the other way round is the
        // mistake a reader makes once.
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ, {mkOp(Op::STR_AT, {num(), str()}), str()});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // str.substr takes (String, Int, Int), not three strings.
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ,
            {mkOp(Op::STR_SUBSTR, {str(), str2(), str()}), str()});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // str.indexof's third argument is the start offset: (s, t, i).
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ,
            {mkOp(Op::STR_INDEXOF, {str(), num(), num()}), num()});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // str.++ is variadic and every argument is a String.
        ConstraintModel ok = base();
        assertTerm(ok, mkOp(Op::STR_CONCAT, {str(), str2(), str(), str2()}));
        Diagnostics d;
        VERIFY(typeCheck(ok, d));

        ConstraintModel bad = base();
        Constraint c;
        c.formula = mkOp(Op::EQ,
            {mkOp(Op::STR_CONCAT, {str(), num()}), str()});
        bad.constraints.push_back(c);
        VERIFY(rejects(bad, ErrorCode::E_TYPE));
    }
    {
        // A string literal is a String, and reaches the script.
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::STR_CONTAINS, {str(), mkString("needle")}));
        VERIFY(contains(emit(m), "needle"));
    }

    // ---- Nonlinearity is not claimed where there is none. -------------------
    // features() feeds the per-instance table; string and float operators must
    // not accidentally match the Op::MUL rule, and fp.mul is genuinely nonlinear
    // and must not be missed the way bvmul was.
    {
        ConstraintModel lin = base();
        assertTerm(lin, mkOp(Op::STR_CONCAT, {str(), str2()}));
        VERIFY(lin.features().count(feat::nonlinear()) == 0);

        ConstraintModel fadd = base();
        assertTerm(fadd, mkOp(Op::FP_ADD, {rne(), f(), g()}));
        VERIFY(fadd.features().count(feat::nonlinear()) == 0);
    }

    std::cout << "All HIR float/string operator tests passed." << std::endl;
    return 0;
}
