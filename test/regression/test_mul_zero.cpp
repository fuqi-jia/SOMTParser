// `(* x 0)` came back as `x`.
//
// mkMul asked GlobalOptions which theory was active in order to decide what
// kind of zero to return, and had no fallback:
//
//     if (isZero(params[i])) {
//         if (options->isIntTheory())  return mkConstInt(0);
//         else if (options->isRealTheory()) return mkConstReal(0.0);
//     }                                   // <- and otherwise, nothing
//     else if (isOne(params[i])) continue;
//     else new_params.push_back(params[i]);
//
// When neither branch fired, control left the `if` without returning and
// without pushing: the zero factor was added to neither the result nor
// new_params, so it simply disappeared and the product became the product of
// the remaining factors.
//
// The condition for that was not exotic. `isIntTheory()` wants an "I" and no
// "R" in the logic string, `isRealTheory()` wants an "R", and the default logic
// is **ALL** -- which contains neither. So every model built through the API
// before a set-logic, which is every model this project's frontends build,
// multiplied by zero and got its other factor back.
//
// Deciding by logic was wrong in the other direction too: under a mixed logic
// such as AUFLIRA, isRealTheory() holds, and an Int-sorted product returned a
// Real zero. Zero's sort follows the operands, not the logic.
//
// Found while checking that `a = b*div(a,b) + mod(a,b)` holds for the three
// integer-division conventions: the identity failed at (1, -5), where the
// Euclidean quotient is 0, and the missing factor was the zero.

#include "somtparser/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

} // namespace

int main() {
    std::cout << "======= multiplication by zero =======\n";

    // ---- Constant folding: zero annihilates. -------------------------------
    {
        ParserPtr p = newParser();
        const auto zero = p->mkConstInt(0);
        // The original bug, in its smallest form. `-5` was the answer.
        VERIFY(p->mkMul(p->mkConstInt(-5), zero)->toString() == "0");
        VERIFY(p->mkMul(zero, p->mkConstInt(-5))->toString() == "0");
        VERIFY(p->mkMul(p->mkConstInt(3), zero)->toString() == "0");
        // n-ary, where the zero is neither first nor last: this returned the
        // operator symbol alone, an even more obviously broken result that
        // nothing was checking.
        VERIFY(p->mkMul({p->mkConstInt(3), zero, p->mkConstInt(7)})->toString() == "0");
        // And a product with no zero still multiplies.
        VERIFY(p->mkMul(p->mkConstInt(-5), p->mkConstInt(2))->toString() == "-10");
    }

    // ---- A variable factor is annihilated just the same. -------------------
    {
        // This is the case that matters: with a constant the answer is at least
        // a number, but `(* x 0)` returning `x` puts a free variable where a
        // zero belongs, and every downstream consumer -- the printer, the
        // evaluator, a solver -- agrees with it.
        ParserPtr p = newParser();
        const auto x = p->mkVarInt("x");
        VERIFY(p->mkMul(x, p->mkConstInt(0))->toString() == "0");
        VERIFY(p->mkMul(p->mkConstInt(0), x)->toString() == "0");
    }

    // ---- Addition is untouched: there, zero IS the identity. ---------------
    {
        // mkAdd drops zeroes on purpose and must keep doing so. Without this,
        // "fixing" the two builders alike would be a plausible next step.
        ParserPtr p = newParser();
        const auto x = p->mkVarInt("x");
        VERIFY(p->mkAdd(p->mkConstInt(-5), p->mkConstInt(0))->toString() == "-5");
        VERIFY(p->mkAdd(x, p->mkConstInt(0))->toString() == "x");
    }

    // ---- A constant-zero sum retains its operand sort. ---------------------
    for(const std::string logic : {"ALL", "AUFLIRA", "QF_LIA"}) {
        ParserPtr p = newParser();
        p->setOption("logic", logic);
        const auto zero = p->mkConstInt(0);
        const auto sum = p->mkAdd({zero, zero, zero});
        VERIFY(sum->isCInt());
        VERIFY(sum->toString() == "0");
        VERIFY(p->assert(p->mkEq(sum, zero)));
    }
    {
        ParserPtr p = newParser();
        const auto zero = p->mkConstReal(0.0);
        VERIFY(p->mkAdd(zero, zero)->isCReal());
        VERIFY(p->mkAdd(p->mkConstInt(0), zero)->isCReal());
    }

    // ---- One is still the multiplicative identity. -------------------------
    {
        ParserPtr p = newParser();
        const auto x = p->mkVarInt("x");
        VERIFY(p->mkMul(x, p->mkConstInt(1))->toString() == "x");
        // When every factor is one, simplification has no surviving operand
        // from which to copy a sort. The original operands still determine it;
        // the default `ALL` logic does not.
        const auto int_one = p->mkMul(p->mkConstInt(1), p->mkConstInt(1));
        VERIFY(int_one->toString() == "1");
        VERIFY(int_one->isCInt());
        const auto real_one = p->mkMul(p->mkConstReal(1.0), p->mkConstReal(1.0));
        VERIFY(real_one->isCReal());
    }

    // ---- The zero's sort follows the operands, not the logic. --------------
    {
        // Under a mixed logic the old code took the isRealTheory() branch and
        // handed back a Real zero for an Int product. Asserting through
        // dumpSMT2 rather than on the node keeps this about the emitted script,
        // which is what a solver reads.
        ParserPtr p = newParser();
        p->setOption("logic", "AUFLIRA");
        const auto x = p->mkVarInt("x");
        // Parser::assert is a member function, so parser.h #undefs the macro.
        VERIFY(p->assert(p->mkEq(p->mkMul(x, p->mkConstInt(0)), p->mkConstInt(0))));
        const std::string s = p->dumpSMT2();
        VERIFY(!has(s, "0.0"));
    }

    // ---- Under an explicit Real logic it is a Real zero. --------------------
    {
        ParserPtr p = newParser();
        const auto r = p->mkVarReal("r");
        const auto prod = p->mkMul(r, p->mkConstReal(0.0));
        VERIFY(prod->getSort()->isReal());
    }

    // ---- End to end: the division identity that found this. ----------------
    {
        // b*div(a,b) + mod(a,b) = a, at (1, -5) where the quotient is zero.
        // Written through the same builders a frontend uses, so it fails if the
        // annihilation regresses anywhere along that path rather than only in
        // mkMul.
        ParserPtr p = newParser();
        const auto a = p->mkConstInt(1);
        const auto b = p->mkConstInt(-5);
        const auto q = p->mkDivInt(a, b);
        const auto r = p->mkMod(a, b);
        VERIFY(q->toString() == "0");
        VERIFY(r->toString() == "1");
        VERIFY(p->mkAdd(p->mkMul(b, q), r)->toString() == "1");
    }

    std::cout << "All multiplication-by-zero tests passed." << std::endl;
    return 0;
}
