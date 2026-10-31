// Integer division, three conventions, no default.
//
// This is the operator that motivated docs/open-questions-2026-08-13.md A6, and
// the reason it was a decision rather than an omission is visible in one table:
//
//     (-7) div 2   remainder    convention
//     ----------   ---------    ------------------------------------------
//     -4           1            Euclidean -- SMT-LIB's own div/mod, where
//                               the remainder is ALWAYS non-negative
//     -3          -1            truncating -- C, Java, Go, MiniZinc `div`
//     -4           1            flooring -- Python `//`
//
// All three agree on non-negative operands, which is most of every benchmark
// suite. A frontend that inherited the wrong one would therefore translate the
// corpus correctly, pass its tests, and be wrong only on instances with
// negative dividends -- with no diagnostic and no failed round trip. So the HIR
// has three named operators and no plain `DIV`, and this file's job is to hold
// them apart.
//
// Negative operands are the ONLY inputs that distinguish them, so every case
// below uses one. A table of positive examples would pass against a single
// division implemented three times under three names.
//
// The values are asserted, not the shapes. Euclidean lowers straight to
// SMT-LIB's div and the other two lower to correction terms around it, so a
// shape assertion would be asserting the correction rather than checking it --
// and constant folding evaluates the correction, which is what makes the check
// possible without a solver.

#include "somtparser/hir/typecheck.h"
#include "somtparser/hir/feature.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace H = SOMTParser::Uir::Hir;

namespace {

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

/** For failure messages only. Uir::Hir's own opName is file-local. */
const char* name(Op op) {
    switch (op) {
    case Op::DIV_EUCLID: return "div_euclid";
    case Op::MOD_EUCLID: return "mod_euclid";
    case Op::DIV_TRUNC:  return "div_trunc";
    case Op::MOD_TRUNC:  return "mod_trunc";
    case Op::DIV_FLOOR:  return "div_floor";
    case Op::MOD_FLOOR:  return "mod_floor";
    case Op::DIV_REAL:   return "/";
    default:             return "?";
    }
}

/** Lower `op(a, b)` on two integer literals and return the folded result as
 *  text. The builders fold constants, so a correction term over literals comes
 *  back as a literal -- which is how a convention's VALUE gets checked here
 *  rather than its emitted shape. */
std::string fold(Op op, long long a, long long b) {
    ParserPtr p = newParser();
    Lower::HirToParser lowered(p);
    Diagnostics d;
    TranslationReport report;

    ConstraintModel m;
    const ExprPtr t = mkOp(op, {mkInt(std::to_string(a)), mkInt(std::to_string(b))});
    VarDecl r;
    r.name = "r";
    r.sort = H::Sort::integer();
    m.decls.push_back(r);
    Constraint c;
    c.formula = mkOp(Op::EQ, {t, mkIdent("r", H::Sort::integer())});
    m.constraints.push_back(c);

    VERIFY(typeCheck(m, d));
    VERIFY(lowered.lower(m, report, d));
    VERIFY(!d.hasErrors());
    const std::string s = p->dumpSMT2();
    const std::size_t at = s.find("(assert");
    VERIFY(at != std::string::npos);
    return s.substr(at, s.find('\n', at) - at);
}

/** True when the folded assertion states exactly `r = want`, in either operand
 *  order -- the builders canonicalise commutative children, so pinning one
 *  order would be asserting the shape this file is trying not to assert. */
bool folds(Op op, long long a, long long b, const std::string& want) {
    const std::string line = fold(op, a, b);
    return contains(line, "(= " + want + " r)") || contains(line, "(= r " + want + ")");
}

struct Case {
    Op          op;
    long long   a;
    long long   b;
    const char* want;
};

} // namespace

int main() {
    std::cout << "======= integer division, three conventions =======\n";

    // ---- The table the whole decision rests on. ----------------------------
    //
    // Read down a column: the three conventions give three different answers
    // for the same inputs. Read across: each convention is self-consistent,
    // and `a = b*div(a,b) + mod(a,b)` holds in all of them, which is what
    // makes each a division rather than an arbitrary pair of functions.
    const std::vector<Case> table = {
        // Euclidean: SMT-LIB's own. The remainder is never negative.
        {Op::DIV_EUCLID, -7,  2, "(- 4)"}, {Op::MOD_EUCLID, -7,  2, "1"},
        {Op::DIV_EUCLID, -7, -2,     "4"}, {Op::MOD_EUCLID, -7, -2, "1"},
        {Op::DIV_EUCLID,  7, -2, "(- 3)"}, {Op::MOD_EUCLID,  7, -2, "1"},
        {Op::DIV_EUCLID,  7,  2,     "3"}, {Op::MOD_EUCLID,  7,  2, "1"},

        // Truncating: toward zero, so the remainder takes the sign of a.
        {Op::DIV_TRUNC,  -7,  2, "(- 3)"}, {Op::MOD_TRUNC,  -7,  2, "(- 1)"},
        {Op::DIV_TRUNC,  -7, -2,     "3"}, {Op::MOD_TRUNC,  -7, -2, "(- 1)"},
        {Op::DIV_TRUNC,   7, -2, "(- 3)"}, {Op::MOD_TRUNC,   7, -2, "1"},
        {Op::DIV_TRUNC,   7,  2,     "3"}, {Op::MOD_TRUNC,   7,  2, "1"},

        // Flooring: toward -infinity, so the remainder takes the sign of b.
        {Op::DIV_FLOOR,  -7,  2, "(- 4)"}, {Op::MOD_FLOOR,  -7,  2, "1"},
        {Op::DIV_FLOOR,  -7, -2,     "3"}, {Op::MOD_FLOOR,  -7, -2, "(- 1)"},
        {Op::DIV_FLOOR,   7, -2, "(- 4)"}, {Op::MOD_FLOOR,   7, -2, "(- 1)"},
        {Op::DIV_FLOOR,   7,  2,     "3"}, {Op::MOD_FLOOR,   7,  2, "1"},

        // EXACT divisions, where all three conventions agree because there is
        // no fractional part to round. These are the only inputs that exercise
        // the correction terms' "remainder is non-zero" guard: drop it and a
        // negative dividend gets corrected anyway, turning -8/2 from -4 into
        // -3. A breakage probe walked straight through the table above and the
        // identity check below, because the identity `a = b*q + r` still holds
        // when q and r are corrupted CONSISTENTLY -- 2*(-3) + (-2) = -8. An
        // identity proves two operators agree with each other, not that either
        // is right.
        {Op::DIV_TRUNC,  -8,  2, "(- 4)"}, {Op::MOD_TRUNC,  -8,  2, "0"},
        {Op::DIV_TRUNC,   8, -2, "(- 4)"}, {Op::MOD_TRUNC,   8, -2, "0"},
        {Op::DIV_FLOOR,  -8,  2, "(- 4)"}, {Op::MOD_FLOOR,  -8,  2, "0"},
        {Op::DIV_FLOOR,   8, -2, "(- 4)"}, {Op::MOD_FLOOR,   8, -2, "0"},
        {Op::DIV_EUCLID, -8,  2, "(- 4)"}, {Op::MOD_EUCLID, -8,  2, "0"},
    };
    for (const Case& c : table) {
        if (!folds(c.op, c.a, c.b, c.want)) {
            std::cout << "  FAILED: " << name(c.op) << "(" << c.a << ", " << c.b
                      << ") should be " << c.want << ", got: " << fold(c.op, c.a, c.b)
                      << "\n";
            VERIFY(false);
        }
    }

    // ---- The three are not the same operator under three names. ------------
    //
    // The mechanical claim: on the one input that separates them, the three
    // divisions disagree and so do the three remainders. Merging any two -- the
    // exact thing a later simplification pass might be tempted to do, since
    // they agree everywhere a positive test would look -- fails here.
    {
        VERIFY(fold(Op::DIV_EUCLID, -7, 2) != fold(Op::DIV_TRUNC, -7, 2));
        VERIFY(fold(Op::MOD_EUCLID, -7, 2) != fold(Op::MOD_TRUNC, -7, 2));
        // Euclidean and flooring coincide at b > 0 and part company at b < 0,
        // so the input that separates THEM is a different one. Using -7/2 for
        // this pair would have passed while proving nothing.
        VERIFY(fold(Op::DIV_EUCLID, 7, -2) != fold(Op::DIV_FLOOR, 7, -2));
        VERIFY(fold(Op::MOD_EUCLID, 7, -2) != fold(Op::MOD_FLOOR, 7, -2));
    }
    {
        // And they agree where they are supposed to: two non-negative operands.
        // Without this the tests above are satisfied by three arbitrary
        // functions that merely differ.
        VERIFY(fold(Op::DIV_EUCLID, 7, 2) == fold(Op::DIV_TRUNC, 7, 2));
        VERIFY(fold(Op::DIV_EUCLID, 7, 2) == fold(Op::DIV_FLOOR, 7, 2));
        VERIFY(fold(Op::MOD_EUCLID, 7, 2) == fold(Op::MOD_TRUNC, 7, 2));
    }

    // ---- The division identity holds in each convention. -------------------
    //
    // a = b*div(a,b) + mod(a,b). Checked by value for every (a,b) with a
    // negative operand, which is where a correction term that fixed the
    // quotient and forgot the remainder would show up.
    {
        const std::vector<std::pair<Op, Op>> pairs = {
            {Op::DIV_EUCLID, Op::MOD_EUCLID},
            {Op::DIV_TRUNC,  Op::MOD_TRUNC},
            {Op::DIV_FLOOR,  Op::MOD_FLOOR},
        };
        const std::vector<std::pair<long long, long long>> inputs = {
            {-7, 2}, {-7, -2}, {7, -2}, {7, 2}, {-8, 2}, {8, -2}, {-1, 5}, {1, -5},
        };
        for (const auto& [dop, mop] : pairs) {
            for (const auto& [a, b] : inputs) {
                // Recomputed here rather than read out of the folded text: the
                // point is that the two operators agree with each other, and
                // parsing their output back would be checking the printer.
                ParserPtr p = newParser();
                Lower::HirToParser lowered(p);
                Diagnostics d;
                TranslationReport report;
                ConstraintModel m;
                const ExprPtr q = mkOp(dop, {mkInt(std::to_string(a)), mkInt(std::to_string(b))});
                const ExprPtr r = mkOp(mop, {mkInt(std::to_string(a)), mkInt(std::to_string(b))});
                // b*q + r = a, as a Bool the folder can settle to `true`.
                const ExprPtr lhs =
                    mkOp(Op::ADD, {mkOp(Op::MUL, {mkInt(std::to_string(b)), q}), r});
                Constraint c;
                c.formula = mkOp(Op::EQ, {lhs, mkInt(std::to_string(a))});
                m.constraints.push_back(c);
                VERIFY(typeCheck(m, d));
                VERIFY(lowered.lower(m, report, d));
                VERIFY(!d.hasErrors());
                const std::string s = p->dumpSMT2();
                if (!contains(s, "(assert true)")) {
                    std::cout << "  IDENTITY FAILED for " << name(dop) << "(" << a
                              << ", " << b << "): " << s << "\n";
                    VERIFY(false);
                }
            }
        }
    }

    // ---- Real division is a different operator, not a fourth convention. ---
    {
        // `(/ 1 2)` is one half. An Int result here would be the single most
        // dangerous kind of wrong: it type-checks, it folds, and it silently
        // answers 0.
        ParserPtr p = newParser();
        Lower::HirToParser lowered(p);
        Diagnostics d;
        TranslationReport report;
        ConstraintModel m;
        VarDecl r;
        r.name = "r";
        r.sort = H::Sort::real();
        m.decls.push_back(r);
        const ExprPtr t = mkOp(Op::DIV_REAL, {mkInt("1"), mkInt("2")});
        VERIFY(t->sort.kind == SortKind::REAL);
        Constraint c;
        c.formula = mkOp(Op::EQ, {t, mkIdent("r", H::Sort::real())});
        m.constraints.push_back(c);
        VERIFY(typeCheck(m, d));
        VERIFY(lowered.lower(m, report, d));
        VERIFY(!d.hasErrors());
        const std::string s = p->dumpSMT2();
        VERIFY(contains(s, "r () Real"));
        VERIFY(!contains(s, "(= 0 r)") && !contains(s, "(= r 0)"));
    }

    // ---- Sorts: the integer family is Int in, Int out, and nothing else. ---
    {
        // A Real operand is rejected rather than widened. `(div 7 2.0)` has no
        // meaning to give and answering 3.5 for it would be worse than
        // refusing -- the operator would silently become real division.
        ConstraintModel m;
        Constraint c;
        c.formula = mkOp(Op::EQ, {mkOp(Op::DIV_EUCLID, {mkInt("7"), mkReal("2.0")}),
                                  mkInt("3")});
        m.constraints.push_back(c);
        Diagnostics d;
        VERIFY(!typeCheck(m, d));
        VERIFY(d.hasErrors() && d.firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        // Strictly binary. `(div a b c)` is not left-associative division in
        // any of these languages, and accepting three arguments would build a
        // term with no lowering.
        ConstraintModel m;
        Constraint c;
        c.formula = mkOp(Op::EQ, {mkOp(Op::DIV_TRUNC, {mkInt("7"), mkInt("2"), mkInt("1")}),
                                  mkInt("3")});
        m.constraints.push_back(c);
        Diagnostics d;
        VERIFY(!typeCheck(m, d));
    }
    {
        // The result of the integer family is Int, so it composes with Int
        // arithmetic. A WIDENED rule would have made it Real and this would
        // fail at the comparison.
        const ExprPtr t = mkOp(Op::DIV_FLOOR, {mkInt("-7"), mkInt("2")});
        VERIFY(t->sort.kind == SortKind::INT);
        VERIFY(mkOp(Op::MOD_TRUNC, {mkInt("-7"), mkInt("2")})->sort.kind == SortKind::INT);
    }

    // ---- Division by a variable is nonlinear. ------------------------------
    {
        // `x div y` is exactly as far outside LIA as `x * y` is. The switch
        // that classifies this has a `default:`, so the arithmetic divisions
        // had to be named in it or they would have been reported linear in
        // silence -- and a results table stratified on linearity would have put
        // them in the wrong row.
        const auto model = [](const ExprPtr& divisor) {
            ConstraintModel m;
            VarDecl x, y;
            x.name = "x"; x.sort = H::Sort::integer();
            y.name = "y"; y.sort = H::Sort::integer();
            m.decls.push_back(x);
            m.decls.push_back(y);
            Constraint c;
            c.formula = mkOp(Op::EQ,
                             {mkOp(Op::DIV_EUCLID, {mkIdent("x", H::Sort::integer()), divisor}),
                              mkInt("3")});
            m.constraints.push_back(c);
            return m;
        };
        const auto isNonlinear = [](const ConstraintModel& m) {
            const auto fs = m.features();
            return fs.count(feat::nonlinear()) != 0;
        };

        VERIFY(isNonlinear(model(mkIdent("y", H::Sort::integer()))));
        // ...and dividing by a CONSTANT is linear, so the check above is not
        // simply calling everything nonlinear.
        VERIFY(!isNonlinear(model(mkInt("2"))));
    }

    std::cout << "All division tests passed." << std::endl;
    return 0;
}
