#pragma once

#include <string>

namespace SOMTParser::Lang::WcnfInternal {

// Exact, normalized positive decimal costs. Both HIR representations must
// classify a weight against top without a machine-integer or floating cast.
inline bool decimalNatural(const std::string& text, std::string& normalized) {
    if (text.empty()) { return false; }
    for (char c : text) {
        if (c < '0' || c > '9') { return false; }
    }
    const std::size_t first = text.find_first_not_of('0');
    if (first == std::string::npos) { return false; }
    normalized = text.substr(first);
    return true;
}

inline bool decimalAtLeast(const std::string& lhs, const std::string& rhs) {
    return lhs.size() != rhs.size() ? lhs.size() > rhs.size() : lhs >= rhs;
}

} // namespace SOMTParser::Lang::WcnfInternal
