#include "somtparser/core/util.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/ir/number.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;
using FP = FloatingPointUtils;

int main() {
    const auto check = [](const Number& source, mpfr_rnd_t mode,
                          unsigned sign, unsigned significand) {
        const auto value = FP::realToFpValue(source, 8, 24, mode);
        VERIFY(value.has_value());
        VERIFY(value->sign == sign);
        VERIFY(value->exponent == 151); // 2^24, with spacing exactly 2.
        VERIFY(value->significand == significand);
    };
    for (const auto& source : {Number(Integer(16777217)),
                              Number(Real(std::string("16777217.0")))}) {
        check(source, MPFR_RNDU, 0, 1);
        check(source, MPFR_RNDD, 0, 0);
        check(source, MPFR_RNDZ, 0, 0);
        check(source, MPFR_RNDN, 0, 0); // Exact tie, even lower significand.
    }
    for (const auto& source : {Number(Integer(-16777217)),
                              Number(Real(std::string("-16777217.0")))}) {
        check(source, MPFR_RNDD, 1, 1);
        check(source, MPFR_RNDU, 1, 0);
        check(source, MPFR_RNDZ, 1, 0);
        check(source, MPFR_RNDN, 1, 0);
    }
    const auto rna = FP::smtRMToMpfrRound("RNA");
    VERIFY(rna != MPFR_RNDA);
    VERIFY(!FP::realToFpValue(Number(Real(std::string("1.3"))), 8, 24, rna));
    FP::FPValue one;
    one.eb = 8; one.sb = 24; one.sign = 0; one.exponent = 127; one.significand = 0;
    VERIFY(!FP::fpUnaryOp(one, 8, 24, rna, mpfr_sqrt));
    VERIFY(!FP::fpBinaryOp(one, one, 8, 24, rna, mpfr_add));
    VERIFY(!FP::fpTernaryOp(one, one, one, 8, 24, rna, mpfr_fma));
    VERIFY(!FP::fpRoundToIntegral(one, 8, 24, rna));
    VERIFY(!FP::fpValueToUbv(one, 8, rna));
    VERIFY(!FP::fpValueToSbv(one, 8, rna));
    VERIFY(!FP::bvToFpValueSigned(1, 8, 8, 24, rna));
    VERIFY(!FP::bvToFpValueUnsigned(1, 8, 8, 24, rna));

    auto small = one;
    small.exponent = 102; // 2^-25: add is exact at sb+4, but not at sb.
    VERIFY(!FP::fpBinaryOp(one, small, 8, 24, MPFR_RNDN, mpfr_add));
    const auto two = FP::fpBinaryOp(one, one, 8, 24, MPFR_RNDN, mpfr_add);
    VERIFY(two && two->exponent == 128 && two->significand == 0);
    VERIFY(!FP::fpUnaryOp(*two, 8, 24, MPFR_RNDN, mpfr_sqrt));
    auto infinity = one;
    infinity.exponent = 255;
    const auto infinite_sum = FP::fpBinaryOp(infinity, one, 8, 24, MPFR_RNDN, mpfr_add);
    VERIFY(infinite_sum && infinite_sum->isInf());
    const auto invalid_difference = FP::fpBinaryOp(infinity, infinity, 8, 24, MPFR_RNDN, mpfr_sub);
    VERIFY(invalid_difference && invalid_difference->isNaN());
    auto nan = infinity;
    nan.significand = 1;
    const auto propagated_nan = FP::fpBinaryOp(nan, one, 8, 24, MPFR_RNDN, mpfr_add);
    VERIFY(propagated_nan && propagated_nan->isNaN());

    auto parser = newParser();
    auto model = newModel();
    for (const auto& text : {
        "((_ to_fp 8 24) RNA 1.3)",
        "(fp.add RNE (fp #b0 #b01111111 #b00000000000000000000000) (fp #b0 #b01100110 #b00000000000000000000000))",
        "(fp.roundToIntegral RNA (fp #b0 #b01111111 #b00011001100110011001101))",
        "((_ to_fp 8 24) RTP ((_ to_fp 11 53) RNE 16777217.0))"}) {
        const auto expression = parser->mkExpr(std::string(text));
        VERIFY(expression && !expression->isErr() && !expression->isCFP());
        const auto printed = parser->toString(expression);
        const auto evaluated = parser->evaluate(expression, model);
        VERIFY(evaluated && !evaluated->isErr());
        VERIFY(evaluated->getKind() == expression->getKind());
        VERIFY(parser->toString(evaluated) == printed);
        const auto reread = parser->mkExpr(printed);
        VERIFY(reread && !reread->isErr());
        VERIFY(parser->toString(reread) == printed);
    }
}
