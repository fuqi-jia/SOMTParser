#include "somtparser/core/util.h"
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <array>
#include <limits>
#include <optional>
#include <string>

using namespace SOMTParser;
using FP = FloatingPointUtils;

static mpz_class powerOfTwo(unsigned long exponent) {
    mpz_class result(1);
    mpz_mul_2exp(result.get_mpz_t(), result.get_mpz_t(), exponent);
    return result;
}

static FP::FPValue exactInteger(const mpz_class& integer) {
    // The fixtures use at most 64 significant bits, including the large
    // powers of two at the 128-bit target boundaries.
    mpfr_t source, restored;
    mpfr_init2(source, 256);
    mpfr_init2(restored, 256);
    VERIFY(mpfr_set_z(source, integer.get_mpz_t(), MPFR_RNDN) == 0);
    const auto value = FP::FPValue::fromMpfr(source, 15, 64);
    VERIFY(value.toMpfr(restored));
    VERIFY(mpfr_equal_p(source, restored));
    mpfr_clear(restored);
    mpfr_clear(source);
    return value;
}

static void expectValue(const std::optional<std::string>& actual,
                        const mpz_class& expected) {
    VERIFY(actual.has_value());
    VERIFY(*actual == expected.get_str());
}

static void checkWidths() {
    const std::array<size_t, 6> widths{{1, 32, 63, 64, 65, 128}};
    const std::array<mpfr_rnd_t, 4> modes{{MPFR_RNDN, MPFR_RNDZ, MPFR_RNDU, MPFR_RNDD}};
    for(const size_t width : widths) {
        const mpz_class modulus = powerOfTwo(static_cast<unsigned long>(width));
        const mpz_class half = modulus / 2;
        // Largest representable source integer below each upper boundary.
        // Exact 2^128-1 is not representable in our <=64-bit-significand FPValue.
        const mpz_class unsigned_step = width <= 64 ? mpz_class(1)
            : powerOfTwo(static_cast<unsigned long>(width - 64));
        const mpz_class signed_step = width <= 65 ? mpz_class(1)
            : powerOfTwo(static_cast<unsigned long>(width - 65));
        const mpz_class below_min_step = width <= 64 ? mpz_class(1)
            : powerOfTwo(static_cast<unsigned long>(width - 64));
        for(const auto mode : modes) {
            expectValue(FP::fpValueToUbv(exactInteger(0), width, mode), 0);
            expectValue(FP::fpValueToUbv(exactInteger(1), width, mode), 1);
            expectValue(FP::fpValueToUbv(exactInteger(modulus - unsigned_step), width, mode),
                        modulus - unsigned_step);
            VERIFY(!FP::fpValueToUbv(exactInteger(modulus), width, mode));
            VERIFY(!FP::fpValueToUbv(exactInteger(-1), width, mode));

            expectValue(FP::fpValueToSbv(exactInteger(half - signed_step), width, mode),
                        half - signed_step);
            expectValue(FP::fpValueToSbv(exactInteger(-half), width, mode), half);
            expectValue(FP::fpValueToSbv(exactInteger(-1), width, mode), modulus - 1);
            VERIFY(!FP::fpValueToSbv(exactInteger(half), width, mode));
            VERIFY(!FP::fpValueToSbv(exactInteger(-half - below_min_step), width, mode));
        }
    }
    // Explicit decimal oracle, source is ordinary Float64 and exact at 2^100.
    const auto large = FP::FPValue::fromFloat64(0x1p100);
    const mpz_class expected("1267650600228229401496703205376");
    expectValue(FP::fpValueToUbv(large, 128, MPFR_RNDN), expected);
    expectValue(FP::fpValueToSbv(large, 128, MPFR_RNDN), expected);
    expectValue(FP::fpValueToSbv(large.neg(), 128, MPFR_RNDN),
                mpz_class("340282365653287863235145205935065006080"));
    VERIFY(!FP::fpValueToUbv(large, 65, MPFR_RNDN));
    VERIFY(!FP::fpValueToSbv(large, 65, MPFR_RNDN));
}

static void checkRoundingAndUndefined() {
    struct Rounded {
        double source;
        long rne, rtz, rtp, rtn;
    };
    const std::array<mpfr_rnd_t, 4> modes{{MPFR_RNDN, MPFR_RNDZ, MPFR_RNDU, MPFR_RNDD}};
    for(const auto& row : std::array<Rounded, 8>{{
            {1.5, 2, 1, 2, 1}, {2.5, 2, 2, 3, 2},
            {-1.5, -2, -1, -1, -2}, {-2.5, -2, -2, -2, -3},
            {0.25, 0, 0, 1, 0}, {-0.25, 0, 0, 0, -1},
            {0.5, 0, 0, 1, 0}, {-0.5, 0, 0, 0, -1}}}) {
        const std::array<long, 4> rounded{{row.rne, row.rtz, row.rtp, row.rtn}};
        for(size_t i = 0; i < modes.size(); ++i) {
            const auto value = FP::FPValue::fromFloat64(row.source);
            const mpz_class signed_bits = rounded[i] < 0 ? mpz_class(rounded[i] + 256)
                                                        : mpz_class(rounded[i]);
            expectValue(FP::fpValueToSbv(value, 8, modes[i]), signed_bits);
            const auto unsigned_bits = FP::fpValueToUbv(value, 8, modes[i]);
            if(rounded[i] < 0) VERIFY(!unsigned_bits);
            else expectValue(unsigned_bits, mpz_class(rounded[i]));
        }
    }
    const auto upper = FP::FPValue::fromFloat64(2147483647.75);
    expectValue(FP::fpValueToSbv(upper, 32, MPFR_RNDZ), mpz_class("2147483647"));
    VERIFY(!FP::fpValueToSbv(upper, 32, MPFR_RNDN));
    VERIFY(!FP::fpValueToSbv(upper, 32, MPFR_RNDU));
    const auto lower = FP::FPValue::fromFloat64(-2147483648.25);
    expectValue(FP::fpValueToSbv(lower, 32, MPFR_RNDZ), mpz_class("2147483648"));
    VERIFY(!FP::fpValueToSbv(lower, 32, MPFR_RNDD));
    const auto unsigned_upper = FP::FPValue::fromFloat64(4294967295.75);
    expectValue(FP::fpValueToUbv(unsigned_upper, 32, MPFR_RNDZ), mpz_class("4294967295"));
    VERIFY(!FP::fpValueToUbv(unsigned_upper, 32, MPFR_RNDN));
    VERIFY(!FP::fpValueToUbv(unsigned_upper, 32, MPFR_RNDU));
    VERIFY(!FP::fpValueToSbv(FP::FPValue::fromFloat64(0.5), 1, MPFR_RNDU));
    expectValue(FP::fpValueToSbv(FP::FPValue::fromFloat64(-1.5), 1, MPFR_RNDU), 1);
    VERIFY(!FP::fpValueToSbv(FP::FPValue::fromFloat64(-1.5), 1, MPFR_RNDN));

    for(const auto mode : modes) {
        for(double zero : {0.0, -0.0}) {
            const auto value = FP::FPValue::fromFloat64(zero);
            expectValue(FP::fpValueToUbv(value, 128, mode), 0);
            expectValue(FP::fpValueToSbv(value, 128, mode), 0);
            VERIFY(!FP::fpValueToUbv(value, 0, mode));
            VERIFY(!FP::fpValueToSbv(value, 0, mode));
        }
        for(double undefined : {std::numeric_limits<double>::infinity(),
                                 -std::numeric_limits<double>::infinity(),
                                 std::numeric_limits<double>::quiet_NaN()}) {
            const auto value = FP::FPValue::fromFloat64(undefined);
            VERIFY(!FP::fpValueToUbv(value, 128, mode));
            VERIFY(!FP::fpValueToSbv(value, 128, mode));
        }
    }
    // Both public's former RNA alias and private's RNA sentinel must be refused.
    for(const auto mode : {MPFR_RNDA, MPFR_RNDNA}) {
        for(double source : {0.0, 1.25, -1.25}) {
            const auto value = FP::FPValue::fromFloat64(source);
            VERIFY(!FP::fpValueToUbv(value, 128, mode));
            VERIFY(!FP::fpValueToSbv(value, 128, mode));
        }
    }
}

static void checkParserFolding() {
    auto parser = newParser();
    auto model = newModel();
    const auto check = [&](const char* op, const FP::FPValue& source, size_t width,
                           const char* mode, const std::optional<std::string>& expected) {
        const std::string text = "((_ " + std::string(op) + " " + std::to_string(width)
            + ") " + mode + " " + source.toSMTFP() + ")";
        const auto expr = parser->mkExpr(text);
        VERIFY(expr && !expr->isErr());
        const auto evaluated = parser->evaluate(expr, model);
        VERIFY(evaluated && !evaluated->isErr());
        for(const auto& node : {expr, evaluated}) {
            if(expected) {
                VERIFY(node->isCBV());
                VERIFY(node->getSort()->getBitWidth() == width);
                VERIFY(BitVectorUtils::bvToNat(node->toString()) == Integer(*expected));
            } else {
                VERIFY(!node->isCBV()); // Undefined/unsupported is not a chosen bit pattern.
            }
        }
    };
    const auto large = FP::FPValue::fromFloat64(0x1p100);
    for(const char* mode : {"RNE", "RTZ", "RTP", "RTN"}) {
        check("fp.to_ubv", large, 128, mode, "1267650600228229401496703205376");
        check("fp.to_sbv", large.neg(), 128, mode, "340282365653287863235145205935065006080");
        check("fp.to_sbv", large, 64, mode, std::nullopt);
    }
    for(const char* mode : {"RNE", "RTZ", "RTP"})
        check("fp.to_ubv", FP::FPValue::fromFloat64(-0.25), 65, mode, "0");
    check("fp.to_ubv", FP::FPValue::fromFloat64(-0.25), 65, "RTN", std::nullopt);
    check("fp.to_ubv", large, 128, "RNA", std::nullopt);
    check("fp.to_sbv", large, 128, "RNA", std::nullopt);
    for(const char* op : {"fp.to_ubv", "fp.to_sbv"}) {
        check(op, FP::FPValue::fromFloat64(std::numeric_limits<double>::infinity()),
              128, "RNE", std::nullopt);
        check(op, FP::FPValue::fromFloat64(std::numeric_limits<double>::quiet_NaN()),
              128, "RNE", std::nullopt);
    }
}

int main() {
    checkWidths();
    checkRoundingAndUndefined();
    checkParserFolding();
}
