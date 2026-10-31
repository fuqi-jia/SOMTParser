#include "somtparser/core/checked_integer.h"
#include "somtparser/ir/number.h"
#include "test_helpers.h"

#include <cstdint>
#include <limits>
#include <string>

using namespace SOMTParser;

int main() {
    // Exhaust every pair in a small signed domain using wider exact arithmetic.
    for (int a = -128; a <= 127; ++a) {
        for (int b = -128; b <= 127; ++b) {
            const int expected[] = {a + b, a - b, a * b};
            const auto x = static_cast<std::int8_t>(a), y = static_cast<std::int8_t>(b);
            std::int8_t results[3] = {};
            const bool overflow[] = {
                detail::addOverflow(x, y, &results[0]),
                detail::subOverflow(x, y, &results[1]),
                detail::mulOverflow(x, y, &results[2])};
            for (int i = 0; i < 3; ++i) {
                VERIFY(overflow[i] == (expected[i] < -128 || expected[i] > 127));
                if (!overflow[i]) VERIFY(results[i] == expected[i]);
            }
        }
    }

    const auto lo = std::numeric_limits<long long>::min();
    const auto hi = std::numeric_limits<long long>::max();
    const long long values[] = {lo, lo + 1, -4294967296LL, -2, -1, 0,
                               1, 2, 4294967296LL, hi - 1, hi};
    const mpz_class lower(std::to_string(lo)), upper(std::to_string(hi));
    for (long long a : values) {
        VERIFY(Integer(a).toString() == std::to_string(a));
        for (long long b : values) {
            const mpz_class x(std::to_string(a)), y(std::to_string(b));
            const mpz_class expected[] = {x + y, x - y, x * y};
            long long results[3] = {a, a, a};
            const bool overflow[] = {
                detail::addOverflow(results[0], b, &results[0]),
                detail::subOverflow(results[1], b, &results[1]),
                detail::mulOverflow(results[2], b, &results[2])};
            for (int i = 0; i < 3; ++i) {
                VERIFY(overflow[i] == (expected[i] < lower || expected[i] > upper));
                if (!overflow[i]) VERIFY(std::to_string(results[i]) == expected[i].get_str());
            }
        }
    }
    VERIFY(Integer(lo).toString() == "-9223372036854775808");
    VERIFY(Integer(hi).toString() == "9223372036854775807");
    return 0;
}
