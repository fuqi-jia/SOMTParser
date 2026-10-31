// The bit-vector operator set: 31 operators, and what each one has to check.
//
// docs/languages/smtlib2.md §4.1 measured the gap as 45 bit-vector kinds in the
// engine against none in the HIR. Widening SortKind gave bit-vectors a *sort*;
// this file is the operators, without which the sort could be declared and
// never used -- cluster F (BTOR2, CryptoLine, QF_BV) needs both.
//
// Two properties carry most of the weight.
//
// The first is that signed and unsigned do not collapse. bvult and bvslt are
// two different orderings of the same bits, so a single Op::LT reaching a
// bit-vector would have to guess; BTOR2 states which one the input meant
// (docs/languages/btor2.md §4.1) and an IR that cannot record it is wrong for
// exactly the instances that use the other one. Every pair below is asserted to
// emit *different* text, which is the only mechanical way to say "these did not
// become the same operator".
//
// The second is that the table is walked, not sampled. An operator added to the
// enum with no lowering, or lowered to the wrong builder, fails here rather than
// surfacing as a script some solver rejects three languages later.

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

// SOMTParser::Sort and SOMTParser::Uir::Hir::Sort are the same concept at two
// layers; qualification rather than renaming, as in test_uir_sorts.cpp.
namespace H = SOMTParser::Uir::Hir;

namespace {

const H::Sort B8  = H::Sort::bitvec(8);
const H::Sort B4  = H::Sort::bitvec(4);
const H::Sort B32 = H::Sort::bitvec(32);

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

VarDecl decl(const char* n, H::Sort s) {
    VarDecl d;
    d.name = n;
    d.sort = std::move(s);
    return d;
}

/** x and y, both 8-bit, plus z at 4 bits -- the vocabulary every case below
 *  draws on, so a case differs from its neighbours only in the operator. */
ConstraintModel base() {
    ConstraintModel m;
    m.decls.push_back(decl("x", B8));
    m.decls.push_back(decl("y", B8));
    m.decls.push_back(decl("z", B4));
    return m;
}

/** Wrap a term as an assertion: a Bool one goes in directly, a bit-vector one
 *  is equated with a fresh variable *of that term's own sort*.
 *
 * Equating with x instead would work for the width-preserving operators and
 * quietly break on concat, whose result is wider than either argument -- which
 * is what the first draft of this file did, and the engine caught it rather
 * than the checker, because the model was ill-sorted before it ever got there. */
void assertTerm(ConstraintModel& m, const ExprPtr& t) {
    Constraint c;
    if (t->sort.kind == SortKind::BOOL) {
        c.formula = t;
    } else {
        const std::string name = "r" + std::to_string(m.constraints.size());
        m.decls.push_back(decl(name.c_str(), t->sort));
        c.formula = mkOp(Op::EQ, {t, mkIdent(name, t->sort)});
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

/** The `assert` line of an emitted script, which is where the operator shows. */
std::string assertionOf(const ConstraintModel& m) {
    const std::string s = emit(m);
    const std::size_t a = s.find("(assert");
    VERIFY(a != std::string::npos);
    return s.substr(a, s.find('\n', a) - a);
}

struct OpCase {
    Op          op;
    const char* smtlib;
    int         arity;
};

/** Every non-indexed bit-vector operator. Indexed ones follow separately
 *  because they are built by their own builders. */
const std::vector<OpCase>& allOps() {
    static const std::vector<OpCase> cases = {
        {Op::BV_NOT, "bvnot", 1},   {Op::BV_NEG, "bvneg", 1},
        {Op::BV_AND, "bvand", 2},   {Op::BV_OR, "bvor", 2},
        {Op::BV_XOR, "bvxor", 2},   {Op::BV_NAND, "bvnand", 2},
        {Op::BV_NOR, "bvnor", 2},   {Op::BV_XNOR, "bvxnor", 2},
        {Op::BV_ADD, "bvadd", 2},   {Op::BV_SUB, "bvsub", 2},
        {Op::BV_MUL, "bvmul", 2},   {Op::BV_UDIV, "bvudiv", 2},
        {Op::BV_UREM, "bvurem", 2}, {Op::BV_SDIV, "bvsdiv", 2},
        {Op::BV_SREM, "bvsrem", 2}, {Op::BV_SMOD, "bvsmod", 2},
        {Op::BV_SHL, "bvshl", 2},   {Op::BV_LSHR, "bvlshr", 2},
        {Op::BV_ASHR, "bvashr", 2},
        {Op::BV_ULT, "bvult", 2},   {Op::BV_ULE, "bvule", 2},
        {Op::BV_UGT, "bvugt", 2},   {Op::BV_UGE, "bvuge", 2},
        {Op::BV_SLT, "bvslt", 2},   {Op::BV_SLE, "bvsle", 2},
        {Op::BV_SGT, "bvsgt", 2},   {Op::BV_SGE, "bvsge", 2},
        {Op::BV_CONCAT, "concat", 2},
    };
    return cases;
}

ExprPtr build(const OpCase& c) {
    if (c.arity == 1) { return mkOp(c.op, {mkIdent("x", B8)}); }
    return mkOp(c.op, {mkIdent("x", B8), mkIdent("y", B8)});
}

} // namespace

int main() {
    std::cout << "======= HIR bit-vector operators =======\n";

    // ---- Every operator type-checks, lowers, and emits under its own name. --
    // Walked, not sampled: an operator added to the enum without a lowering
    // fails here.
    {
        for (const OpCase& c : allOps()) {
            ConstraintModel m = base();
            assertTerm(m, build(c));
            const std::string line = assertionOf(m);
            if (!contains(line, c.smtlib)) {
                std::cerr << "operator " << c.smtlib << " did not reach the script: "
                          << line << std::endl;
                VERIFY(false);
            }
        }
    }

    // ---- Signed and unsigned are not the same operator. ---------------------
    // The reason the enum has both. If a future refactor routed the signed
    // family through the unsigned builders -- or collapsed them into one
    // Op::LT dispatched on sort -- every one of these pairs would coincide and
    // half of BTOR2's comparisons would translate to the wrong ordering.
    {
        const std::pair<Op, Op> pairs[] = {
            {Op::BV_ULT, Op::BV_SLT}, {Op::BV_ULE, Op::BV_SLE},
            {Op::BV_UGT, Op::BV_SGT}, {Op::BV_UGE, Op::BV_SGE},
            {Op::BV_UDIV, Op::BV_SDIV}, {Op::BV_UREM, Op::BV_SREM},
            {Op::BV_LSHR, Op::BV_ASHR},
        };
        for (const auto& p : pairs) {
            ConstraintModel u = base();
            assertTerm(u, mkOp(p.first, {mkIdent("x", B8), mkIdent("y", B8)}));
            ConstraintModel s = base();
            assertTerm(s, mkOp(p.second, {mkIdent("x", B8), mkIdent("y", B8)}));
            VERIFY(assertionOf(u) != assertionOf(s));
        }
        // ...and all 27 non-concat operators are pairwise distinct in the
        // emitted text, which is the same claim made once over the whole set:
        // no two of them are aliases.
        std::set<std::string> seen;
        for (const OpCase& c : allOps()) {
            ConstraintModel m = base();
            assertTerm(m, build(c));
            const std::string line = assertionOf(m);
            VERIFY(seen.insert(line).second);
        }
    }

    // ---- What is emitted is SMT-LIB, not something that looks like it. ------
    // A dumped script that no parser accepts is the failure a name check cannot
    // see, so every operator's script is read back by a fresh parser.
    {
        for (const OpCase& c : allOps()) {
            ConstraintModel m = base();
            assertTerm(m, build(c));
            ParserPtr reader = newParser();
            VERIFY(reader->parseStr(emit(m)));
        }
    }

    // ---- Widths must agree, and the diagnostic says which two. --------------
    {
        ConstraintModel m = base();
        m.decls.push_back(decl("w", B32));
        Constraint c;
        c.formula = mkOp(Op::EQ,
            {mkOp(Op::BV_ADD, {mkIdent("x", B8), mkIdent("w", B32)}),
             mkIdent("x", B8)});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        Diagnostics d;
        VERIFY(!typeCheck(m, d));
        VERIFY(contains(d.all().front().message, "(_ BitVec 8)"));
        VERIFY(contains(d.all().front().message, "(_ BitVec 32)"));
    }
    {
        // A shift is the case a reader is most likely to get wrong: SMT-LIB
        // wants the distance at the *operand's* width, not a narrower one.
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ,
            {mkOp(Op::BV_SHL, {mkIdent("x", B8), mkIdent("z", B4)}),
             mkIdent("x", B8)});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // An Int where a bit-vector belongs.
        ConstraintModel m = base();
        m.decls.push_back(decl("i", H::Sort::integer()));
        Constraint c;
        c.formula = mkOp(Op::EQ,
            {mkOp(Op::BV_AND, {mkIdent("x", B8), mkIdent("i", H::Sort::integer())}),
             mkIdent("x", B8)});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- concat's width is the sum, and is checked rather than assumed. -----
    {
        ConstraintModel m = base();
        const ExprPtr cat = mkOp(Op::BV_CONCAT,
                                 {mkIdent("z", B4), mkIdent("z", B4)});
        VERIFY(sameSort(cat->sort, B8));
        m.constraints.push_back([&] {
            Constraint c;
            c.formula = mkOp(Op::EQ, {cat, mkIdent("x", B8)});
            return c;
        }());
        VERIFY(contains(emit(m), "concat"));

        // Three arguments, so the sum is not just "the other one's width".
        const ExprPtr three = mkOp(Op::BV_CONCAT,
            {mkIdent("z", B4), mkIdent("z", B4), mkIdent("z", B4)});
        VERIFY(sameSort(three->sort, H::Sort::bitvec(12)));
    }
    {
        // A hand-built concat that records the wrong width is an internal
        // error, not a silent reinterpretation: every consumer trusts the
        // recorded sort rather than re-deriving it.
        auto bad = std::make_shared<Expr>();
        bad->kind = ExprKind::OP;
        bad->op   = Op::BV_CONCAT;
        bad->args = {mkIdent("z", B4), mkIdent("z", B4)};
        bad->sort = H::Sort::bitvec(9);
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ, {ExprPtr(bad), mkIdent("x", B8)});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_INTERNAL));
    }

    // ---- extract: the indices are part of the operator. ---------------------
    {
        const ExprPtr e = mkBvExtract(mkIdent("x", B8), 5, 2);
        VERIFY(sameSort(e->sort, B4));          // 5 - 2 + 1
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ, {e, mkIdent("z", B4)});
        m.constraints.push_back(c);
        // The SMT-LIB spelling of an indexed identifier, which a plain
        // prefix-form printer would get wrong.
        VERIFY(contains(emit(m), "(_ extract 5 2)"));
    }
    {
        // hi < lo: not a narrower result, a term with no meaning.
        const ExprPtr e = mkBvExtract(mkIdent("x", B8), 2, 5);
        ConstraintModel m = base();
        Constraint c;
        c.formula = mkOp(Op::EQ, {e, mkIdent("z", B4)});
        m.constraints.push_back(c);
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // Reading past the end. Off-by-one lives here: bit 8 of an 8-bit
        // vector does not exist, bit 7 does.
        ConstraintModel over = base();
        Constraint c;
        c.formula = mkOp(Op::EQ, {mkBvExtract(mkIdent("x", B8), 8, 5),
                                  mkIdent("z", B4)});
        over.constraints.push_back(c);
        VERIFY(rejects(over, ErrorCode::E_TYPE));

        ConstraintModel edge = base();
        Constraint ok;
        ok.formula = mkOp(Op::EQ, {mkBvExtract(mkIdent("x", B8), 7, 4),
                                   mkIdent("z", B4)});
        edge.constraints.push_back(ok);
        Diagnostics d;
        VERIFY(typeCheck(edge, d));
    }

    // ---- zero_extend and sign_extend widen, differently. --------------------
    {
        const ExprPtr z = mkBvExtend(Op::BV_ZERO_EXTEND, mkIdent("z", B4), 4);
        const ExprPtr s = mkBvExtend(Op::BV_SIGN_EXTEND, mkIdent("z", B4), 4);
        VERIFY(sameSort(z->sort, B8));
        VERIFY(sameSort(s->sort, B8));

        ConstraintModel mz = base();
        Constraint cz;
        cz.formula = mkOp(Op::EQ, {z, mkIdent("x", B8)});
        mz.constraints.push_back(cz);

        ConstraintModel ms = base();
        Constraint cs;
        cs.formula = mkOp(Op::EQ, {s, mkIdent("x", B8)});
        ms.constraints.push_back(cs);

        VERIFY(contains(emit(mz), "(_ zero_extend 4)"));
        VERIFY(contains(emit(ms), "(_ sign_extend 4)"));
        // Widening a bit-vector is a different function depending on how the
        // value is read; the two must not collapse any more than bvult and
        // bvslt may.
        VERIFY(assertionOf(mz) != assertionOf(ms));
    }
    {
        // Extending by zero is the identity on the sort, and must not be
        // mistaken for "no index given".
        const ExprPtr e = mkBvExtend(Op::BV_ZERO_EXTEND, mkIdent("x", B8), 0);
        VERIFY(sameSort(e->sort, B8));
        VERIFY(e->indices.size() == 1);
    }

    // ---- An indexed operator built through mkOp is a programming error. -----
    // mkOp has nowhere to put the indices, so letting it build one would
    // produce a node whose recorded width came from nothing.
    {
        bool threw = false;
        try {
            (void)mkOp(Op::BV_EXTRACT, {mkIdent("x", B8)});
        } catch (const std::exception&) {
            threw = true;
        }
        VERIFY(threw);
    }

    // ---- Nonlinearity is reported for bit-vectors too. ----------------------
    //
    // features() feeds the per-instance table the experiment reports, so an
    // omission here does not fail loudly: it records a corpus as linear that is
    // not. hasNonlinearMul looked only at Op::MUL, so a BTOR2 instance built
    // out of bvmul -- which is what makes QF_BV hard -- reported no nonlinear
    // feature at all.
    {
        const auto nonlinear = [](const ExprPtr& t) {
            ConstraintModel m = base();
            assertTerm(m, t);
            return m.features().count(feat::nonlinear()) == 1;
        };
        const ExprPtr x = mkIdent("x", B8), y = mkIdent("y", B8);
        const ExprPtr k = mkBitVec("#b00000010", 8);

        VERIFY(nonlinear(mkOp(Op::BV_MUL, {x, y})));
        // ...and multiplication by a constant is not, or every model would be
        // reported nonlinear and the feature would carry no information.
        VERIFY(!nonlinear(mkOp(Op::BV_MUL, {x, k})));

        // Division by a variable divisor, for the same reason (/ x y) is
        // nonlinear over the integers.
        VERIFY(nonlinear(mkOp(Op::BV_UDIV, {x, y})));
        VERIFY(nonlinear(mkOp(Op::BV_SDIV, {x, y})));
        VERIFY(nonlinear(mkOp(Op::BV_UREM, {x, y})));
        VERIFY(!nonlinear(mkOp(Op::BV_UDIV, {x, k})));

        // A variable shift distance: (bvshl x y) is multiplication by 2^y, and
        // a solver bit-blasts it as such. The easiest of these to miss.
        VERIFY(nonlinear(mkOp(Op::BV_SHL, {x, y})));
        VERIFY(nonlinear(mkOp(Op::BV_ASHR, {x, y})));
        VERIFY(!nonlinear(mkOp(Op::BV_SHL, {x, k})));

        // Plain bitwise and additive operators stay linear.
        VERIFY(!nonlinear(mkOp(Op::BV_ADD, {x, y})));
        VERIFY(!nonlinear(mkOp(Op::BV_AND, {x, y})));
        VERIFY(!nonlinear(mkOp(Op::BV_ULT, {x, y})));

        // Nested, so the recursion is exercised rather than only the top node.
        VERIFY(nonlinear(mkOp(Op::BV_ADD, {x, mkOp(Op::BV_MUL, {x, y})})));
    }

    std::cout << "All HIR bit-vector operator tests passed." << std::endl;
    return 0;
}
