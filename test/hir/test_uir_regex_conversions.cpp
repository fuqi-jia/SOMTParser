// Regular expressions, and the conversions between theories.
//
// The last two rows of docs/languages/smtlib2.md's "what is still missing"
// table. Each closes a gap of the same kind the operator sets closed, one level
// up: a theory that was present but unreachable.
//
//   * RegLan. A string theory without it carries the operators and not the
//     corpus -- most string benchmarks are mostly membership constraints, and
//     `str.in_re` needs a sort to be a member *of*.
//   * The conversions. Without them every theory was an island: a bit-vector
//     could not index an array, a floating-point result could not be compared
//     against a rational specification.
//
// The conversions are where a translation most easily changes the question
// without saying so, and the file is weighted accordingly. bv2nat and bv2int
// read the same bits as [0, 2^w) and as [-2^(w-1), 2^(w-1)); choosing wrong
// shifts every negative value by 2^w, and both are BitVec -> Int, so nothing
// downstream can tell. Same story for fp.to_sbv against fp.to_ubv, and for
// to_fp against to_fp_unsigned.

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

const H::Sort INT  = H::Sort::integer();
const H::Sort REAL = H::Sort::real();
const H::Sort STR  = H::Sort::string();
const H::Sort RE   = H::Sort::regLan();
const H::Sort B8   = H::Sort::bitvec(8);
const H::Sort F32  = H::Sort::floating(8, 24);

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
    m.decls.push_back(decl("s", STR));
    m.decls.push_back(decl("t", STR));
    m.decls.push_back(decl("i", INT));
    m.decls.push_back(decl("x", REAL));
    m.decls.push_back(decl("v", B8));
    m.decls.push_back(decl("f", F32));
    return m;
}

/** Assert a term, declaring a fresh variable of its sort when it is not Bool. */
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

ExprPtr str()  { return mkIdent("s", STR); }
ExprPtr str2() { return mkIdent("t", STR); }
ExprPtr num()  { return mkIdent("i", INT); }
ExprPtr real() { return mkIdent("x", REAL); }
ExprPtr bv()   { return mkIdent("v", B8); }
ExprPtr flt()  { return mkIdent("f", F32); }
ExprPtr rne()  { return mkRoundingMode("RNE"); }
/** A regular expression to build larger ones out of. */
ExprPtr re()   { return mkOp(Op::STR_TO_RE, {mkString("ab")}); }

struct Case {
    Op                   op;
    const char*          smtlib;
    std::vector<ExprPtr> args;
};

std::vector<Case> allCases() {
    return {
        {Op::STR_TO_RE,     "str.to_re",  {mkString("ab")}},
        {Op::STR_IN_RE,     "str.in_re",  {str(), re()}},
        {Op::RE_CONCAT,     "re.",        {re(), re()}},
        {Op::RE_UNION,      "re.union",   {re(), re()}},
        {Op::RE_INTER,      "re.inter",   {re(), re()}},
        {Op::RE_DIFF,       "re.",        {re(), re()}},
        {Op::RE_STAR,       "re.",        {re()}},
        {Op::RE_PLUS,       "re.",        {re()}},
        {Op::RE_OPT,        "re.opt",     {re()}},
        {Op::RE_COMPLEMENT, "re.",        {re()}},
        {Op::RE_RANGE,      "re.range",   {mkString("a"), mkString("z")}},
        // A variable argument, not a literal: str.to_code("a") is folded
        // to 97 by the builders, which is correct and would make a test
        // that looked for the operator name fail on right behaviour.
        {Op::STR_TO_CODE,   "str.to_code",   {str()}},
        {Op::STR_FROM_CODE, "str.from_code", {num()}},
        {Op::TO_INT,        "to_int",     {real()}},
        {Op::TO_REAL,       "to_real",    {num()}},
        {Op::BV_TO_NAT,     "nat",        {bv()}},
        {Op::BV_TO_INT,     "int",        {bv()}},
        {Op::FP_TO_REAL,    "real",       {flt()}},
        {Op::FP_TO_IEEE_BV, "ieee",       {flt()}},
    };
}

} // namespace

int main() {
    std::cout << "======= regular expressions and conversions =======\n";

    // ---- Every non-indexed operator type-checks, lowers and emits. ----------
    {
        for (const Case& c : allCases()) {
            ConstraintModel m = base();
            assertTerm(m, mkOp(c.op, c.args));
            const std::string line = assertionOf(m);
            if (!contains(line, c.smtlib)) {
                std::cerr << "operator did not reach the script: " << line << std::endl;
                VERIFY(false);
            }
            ParserPtr reader = newParser();
            VERIFY(reader->parseStr(emit(m)));
        }
    }

    // ---- No two of them collapse into one. ----------------------------------
    {
        std::set<std::string> seen;
        for (const Case& c : allCases()) {
            ConstraintModel m = base();
            assertTerm(m, mkOp(c.op, c.args));
            VERIFY(seen.insert(assertionOf(m)).second);
        }
    }

    // ---- The three nullary regular expressions. -----------------------------
    // Literals rather than zero-argument operators, because mkOp refuses an
    // empty argument list -- the same reason dimacs-cnf.md §4.1's empty clause
    // is a literal.
    {
        for (const char* name : {"re.none", "re.all", "re.allchar"}) {
            ConstraintModel m = base();
            assertTerm(m, mkOp(Op::STR_IN_RE, {str(), mkReglanConst(name)}));
            Diagnostics d;
            VERIFY(typeCheck(m, d));
            ParserPtr reader = newParser();
            VERIFY(reader->parseStr(emit(m)));
        }
        VERIFY(sameSort(mkReglanConst("re.none")->sort, RE));
    }
    {
        // A fourth name is not one of them, and must not reach the script.
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::STR_IN_RE, {str(), mkReglanConst("re.everything")}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- str.in_re relates a String to a RegLan, in that order. -------------
    {
        VERIFY(mkOp(Op::STR_IN_RE, {str(), re()})->sort.kind == SortKind::BOOL);
        VERIFY(sameSort(mkOp(Op::STR_TO_RE, {str()})->sort, RE));

        // Arguments the other way round.
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::STR_IN_RE, {re(), str()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A String where a RegLan belongs: the mistake that a stringly-typed
        // regular expression invites.
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::RE_UNION, {re(), str()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- re.loop is indexed. ------------------------------------------------
    {
        const ExprPtr loop = mkReLoop(re(), 2, 5);
        VERIFY(sameSort(loop->sort, RE));
        VERIFY(loop->indices.size() == 2);
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::STR_IN_RE, {str(), loop}));
        VERIFY(contains(emit(m), "re.loop"));
    }

    // ---- bv2nat and bv2int are different readings of the same bits. ---------
    // The conversion pair that most easily changes the question: both are
    // BitVec -> Int, both type-check, and they differ by 2^w on every value with
    // the top bit set. If one were routed through the other's builder, nothing
    // downstream would notice -- so the test is that they emit different text.
    {
        ConstraintModel u = base();
        assertTerm(u, mkOp(Op::BV_TO_NAT, {bv()}));
        ConstraintModel s = base();
        assertTerm(s, mkOp(Op::BV_TO_INT, {bv()}));
        VERIFY(assertionOf(u) != assertionOf(s));
        VERIFY(sameSort(mkOp(Op::BV_TO_NAT, {bv()})->sort, INT));
        VERIFY(sameSort(mkOp(Op::BV_TO_INT, {bv()})->sort, INT));
    }

    // ---- int2bv is indexed by the target width. -----------------------------
    {
        const ExprPtr e = mkIntToBv(num(), 16);
        VERIFY(sameSort(e->sort, H::Sort::bitvec(16)));
        ConstraintModel m = base();
        assertTerm(m, e);
        VERIFY(contains(emit(m), "16"));
    }
    {
        // A width the expression does not record is an internal error: every
        // consumer trusts the recorded sort over re-deriving it.
        auto bad = std::make_shared<Expr>();
        bad->kind = ExprKind::OP;
        bad->op = Op::INT_TO_BV;
        bad->args = {num()};
        bad->indices = {16};
        bad->sort = H::Sort::bitvec(8);
        ConstraintModel m = base();
        assertTerm(m, ExprPtr(bad));
        VERIFY(rejects(m, ErrorCode::E_INTERNAL));
    }

    // ---- fp.to_sbv and fp.to_ubv, likewise. ---------------------------------
    {
        const ExprPtr sbv = mkFpToBv(Op::FP_TO_SBV, rne(), flt(), 32);
        const ExprPtr ubv = mkFpToBv(Op::FP_TO_UBV, rne(), flt(), 32);
        VERIFY(sameSort(sbv->sort, H::Sort::bitvec(32)));
        VERIFY(sameSort(ubv->sort, H::Sort::bitvec(32)));

        ConstraintModel a = base();
        assertTerm(a, sbv);
        ConstraintModel b = base();
        assertTerm(b, ubv);
        VERIFY(assertionOf(a) != assertionOf(b));
    }
    {
        // fp.to_ieee_bv's width is the FORMAT's, not an index: eb + sb bits.
        const ExprPtr e = mkOp(Op::FP_TO_IEEE_BV, {flt()});
        VERIFY(sameSort(e->sort, H::Sort::bitvec(32)));   // 8 + 24
        const ExprPtr d = mkOp(Op::FP_TO_IEEE_BV,
                               {mkIdent("g", H::Sort::floating(11, 53))});
        VERIFY(sameSort(d->sort, H::Sort::bitvec(64)));   // 11 + 53
    }

    // ---- to_fp converts from three different sorts under one spelling. ------
    {
        for (const ExprPtr& src : {real(), flt(), bv()}) {
            const ExprPtr e = mkToFp(Op::TO_FP, rne(), src, 8, 24);
            VERIFY(sameSort(e->sort, F32));
            ConstraintModel m = base();
            assertTerm(m, e);
            Diagnostics d;
            VERIFY(typeCheck(m, d));
        }
    }
    {
        // ...but not from a String, which is not a numeric source at all.
        ConstraintModel m = base();
        assertTerm(m, mkToFp(Op::TO_FP, rne(), str(), 8, 24));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // to_fp_unsigned reads its argument as an unsigned bit-vector. There is
        // nothing unsigned about a Real, so that combination is refused rather
        // than silently treated as to_fp.
        ConstraintModel ok = base();
        assertTerm(ok, mkToFp(Op::TO_FP_UNSIGNED, rne(), bv(), 8, 24));
        Diagnostics d;
        VERIFY(typeCheck(ok, d));

        ConstraintModel bad = base();
        assertTerm(bad, mkToFp(Op::TO_FP_UNSIGNED, rne(), real(), 8, 24));
        VERIFY(rejects(bad, ErrorCode::E_TYPE));
    }
    {
        // ...and the signed and unsigned readings of the same bit-vector do not
        // collapse.
        ConstraintModel a = base();
        assertTerm(a, mkToFp(Op::TO_FP, rne(), bv(), 8, 24));
        ConstraintModel b = base();
        assertTerm(b, mkToFp(Op::TO_FP_UNSIGNED, rne(), bv(), 8, 24));
        VERIFY(assertionOf(a) != assertionOf(b));
    }

    // ---- to_int and to_real are not each other's inverse by accident. -------
    {
        VERIFY(sameSort(mkOp(Op::TO_INT, {real()})->sort, INT));
        VERIFY(sameSort(mkOp(Op::TO_REAL, {num()})->sort, REAL));

        // to_int takes a Real, not an Int: the identity case would otherwise
        // type-check and mean nothing.
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::TO_INT, {num()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- A conversion chain, which is the point of having them. -------------
    // A bit-vector read as an integer, converted to a real, converted to a
    // float: three theories in one term, which was unsayable before.
    {
        ConstraintModel m = base();
        assertTerm(m, mkOp(Op::FP_LT,
            {mkToFp(Op::TO_FP, rne(),
                    mkOp(Op::TO_REAL, {mkOp(Op::BV_TO_NAT, {bv()})}), 8, 24),
             flt()}));
        Diagnostics d;
        VERIFY(typeCheck(m, d));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(emit(m)));
    }

    std::cout << "All regex/conversion tests passed." << std::endl;
    return 0;
}
