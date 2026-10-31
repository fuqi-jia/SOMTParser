#include <cmath>
#include <cfenv>
#include <iostream>
#include <string>

#include "somtparser/frontend/parser.h"
#include "somtparser/core/util.h"
#include "somtparser/ir/value.h"
#include "test_helpers.h"

int main() {
    using namespace SOMTParser;

    ParserPtr parser = newParser();

    {
        auto nanN = parser->mkExpr("(_ NaN 8 24)");
        VERIFY(nanN && !nanN->isErr());
        VERIFY(fpNodeIsNaN(nanN));
        VERIFY(!fpNodeIsInf(nanN));
        VERIFY(!fpNodeIsZero(nanN));
    }

    {
        auto pinf = parser->mkExpr("(_ +oo 8 24)");
        VERIFY(pinf && fpNodeIsInf(pinf) && !fpNodeIsNeg(pinf));
        auto ninf = parser->mkExpr("(_ -oo 8 24)");
        VERIFY(ninf && fpNodeIsInf(ninf) && fpNodeIsNeg(ninf));
    }

    {
        auto pz = parser->mkExpr("(_ +zero 8 24)");
        VERIFY(pz && fpNodeIsZero(pz) && !fpNodeIsNeg(pz));
        auto nz = parser->mkExpr("(_ -zero 8 24)");
        VERIFY(nz && fpNodeIsZero(nz) && fpNodeIsNeg(nz));
    }

    {
        auto one = parser->mkExpr("((_ to_fp 8 24) RNE 1.0)");
        VERIFY(one && fpNodeIsNormal(one) && !fpNodeIsSubnormal(one));
        VERIFY(!fpNodeIsNeg(one));
        auto neg = parser->mkExpr("((_ to_fp 8 24) RNE -2.5)");
        VERIFY(neg && fpNodeIsNeg(neg));
    }

    {
        auto sub = parser->mkExpr("(fp #b0 #b00000000 #b00000000000000000000001)");
        VERIFY(sub && fpNodeIsSubnormal(sub));
        VERIFY(sub->getValue() != nullptr);
        VERIFY(sub->getValue()->getType() == ValueType::FP);
    }

    {
        auto rm = parser->mkExpr("RNE");
        VERIFY(rm);
        VERIFY(getFPRoundingMode(rm) == FE_TONEAREST);
    }

    {
        VERIFY(parser->parseStr("(declare-const symbolic_fp_bits (_ BitVec 32))"));
        const std::string term = "(fp ((_ extract 31 31) symbolic_fp_bits) "
            "((_ extract 30 23) symbolic_fp_bits) ((_ extract 22 0) symbolic_fp_bits))";
        auto symbolic = parser->mkExpr(term);
        VERIFY(symbolic && !symbolic->isErr());
        VERIFY(!FloatingPointUtils::fpNodeToValue(symbolic).has_value());
        VERIFY(!symbolic->getValue());
        for (const auto& expression : {"(= " + term + " (_ +zero 8 24))",
                                      "(fp.eq " + term + " (_ +zero 8 24))",
                                      "(distinct " + term + " (_ +zero 8 24))",
                                      "(fp.isZero " + term + ")", "(fp.isNormal " + term + ")",
                                      "(fp.isSubnormal " + term + ")", "(fp.isInfinite " + term + ")",
                                      "(fp.isNaN " + term + ")", "(fp.isNegative " + term + ")",
                                      "(fp.isPositive " + term + ")"}) {
            auto predicate = parser->mkExpr(expression);
            VERIFY(predicate && !predicate->isErr());
            VERIFY(!predicate->isTrue() && !predicate->isFalse());
            auto evaluated = parser->evaluate(predicate, newModel());
            VERIFY(evaluated && !evaluated->isTrue() && !evaluated->isFalse());
        }
        // A partly symbolic constructor is not a literal either.
        auto partial = parser->mkExpr("(fp #b0 #b00000000 ((_ extract 22 0) symbolic_fp_bits))");
        VERIFY(partial && !FloatingPointUtils::fpNodeToValue(partial).has_value());
        // Hash-consed shared uses retain the same symbolic constructor.
        auto again = parser->mkExpr(term);
        VERIFY(again == symbolic);
        VERIFY(!FloatingPointUtils::fpNodeToValue(again).has_value());
    }

    {
        float x = 1.375f;
        std::string smt = float32ToSMTFP(x);
        auto n = parser->mkExpr(smt);
        VERIFY(n && !n->isErr());
        auto back = fpNodeToFloat32(n);
        VERIFY(back.has_value());
        VERIFY(std::fabs(static_cast<double>(*back - x)) < 1e-6);
    }

    {
        double y = -3.125;
        std::string smt = float64ToSMTFP(y);
        auto n = parser->mkExpr(smt);
        VERIFY(n && !n->isErr());
        auto back = fpNodeToFloat64(n);
        VERIFY(back.has_value());
        VERIFY(std::fabs(*back - y) < 1e-12);
    }

    {
        ModelPtr model = newModel();
        auto phi = parser->mkExpr("(fp.isNaN (_ NaN 8 24))");
        VERIFY(phi && !phi->isErr());
        auto ev = parser->evaluate(phi, model);
        VERIFY(ev && ev->isTrue());
        VERIFY(parser->toString(ev) == "true");
    }

    std::cout << "test_fp_util_wrappers: all assertions passed\n";
    return 0;
}
