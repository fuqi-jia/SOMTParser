#ifndef SOMTPARSER_CORE_CHECKED_INTEGER_H
#define SOMTPARSER_CORE_CHECKED_INTEGER_H

#include <limits>
#include <type_traits>

namespace SOMTParser::detail {

// Return true on overflow, without evaluating an overflowing signed operation.
// Arguments are copied before writing the result, so the output may alias either.
template <typename T>
bool addOverflow(T a, T b, T* result) {
    static_assert(std::is_integral_v<T> && std::is_signed_v<T>);
    const T lo = std::numeric_limits<T>::min(), hi = std::numeric_limits<T>::max();
    if ((b > 0 && a > hi - b) || (b < 0 && a < lo - b)) return true;
    *result = static_cast<T>(a + b);
    return false;
}

template <typename T>
bool subOverflow(T a, T b, T* result) {
    static_assert(std::is_integral_v<T> && std::is_signed_v<T>);
    const T lo = std::numeric_limits<T>::min(), hi = std::numeric_limits<T>::max();
    if ((b > 0 && a < lo + b) || (b < 0 && a > hi + b)) return true;
    *result = static_cast<T>(a - b);
    return false;
}

template <typename T>
bool mulOverflow(T a, T b, T* result) {
    static_assert(std::is_integral_v<T> && std::is_signed_v<T>);
    const T lo = std::numeric_limits<T>::min(), hi = std::numeric_limits<T>::max();
    if (a > 0) {
        if ((b > 0 && a > hi / b) || (b < 0 && b < lo / a)) return true;
    } else if (a < 0) {
        if ((b > 0 && a < lo / b) || (b < 0 && a < hi / b)) return true;
    }
    *result = static_cast<T>(a * b);
    return false;
}

} // namespace SOMTParser::detail

#endif
