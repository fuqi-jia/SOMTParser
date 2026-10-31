// Shared validation and objective ordering for native weighted HIR constraints.
#pragma once

#include "somtparser/hir/hir.h"
#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Uir::Hir {

inline bool isExactPositiveSoftWeight(std::string_view text) {
    bool positive = false;
    for (const char ch : text) {
        if (ch < '0' || ch > '9') return false;
        positive = positive || ch != '0';
    }
    return positive;
}

/** group is an SMT-LIB symbol spelling, or empty for the unnamed group.
 *  Quoted and unquoted spellings have the same identity. No interpolation of
 *  unchecked text into :id is permitted. */
inline bool isSoftGroupSymbol(std::string_view group) {
    if (group.empty()) return true;
    if (group.front() == '|') {
        if (group.size() <= 2 || group.back() != '|') return false;
        for (std::size_t i = 1; i + 1 < group.size(); ++i) {
            const unsigned char ch = static_cast<unsigned char>(group[i]);
            if (ch == '|' || ch == '\\' || ch < 32 || ch == 127) return false;
        }
        return true;
    }
    constexpr std::string_view punctuation = "~!@$%^&*_-+=<>.?/";
    const auto initial = [&](char ch) {
        return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
            || punctuation.find(ch) != std::string_view::npos;
    };
    if (!initial(group.front())) return false;
    for (const char ch : group) {
        if (!initial(ch) && (ch < '0' || ch > '9')) return false;
    }
    // SMT-LIB reserved tokens may be used only in quoted form.
    for (const auto reserved : {"!", "_", "as", "BINARY", "DECIMAL", "HEXADECIMAL",
                               "NUMERAL", "STRING", "exists", "forall", "let", "match", "par"}) {
        if (group == reserved) return false;
    }
    return true;
}

/** Effective minimization groups in the order actually emitted: ordinary
 *  soft assertions first, then the unnamed packed-clause group if present.
 *  Explicit arithmetic objectives follow these groups in model order. */
inline std::vector<std::string> softObjectiveGroups(const ConstraintModel& model) {
    std::vector<std::string> result;
    std::unordered_set<std::string> seen;
    const auto append = [&](const std::string& spelling) {
        const std::string name = spelling.size() >= 2 && spelling.front() == '|'
                && spelling.back() == '|'
            ? spelling.substr(1, spelling.size() - 2) : spelling;
        if (seen.insert(name).second) result.push_back(name);
    };
    for (const auto& constraint : model.constraints) {
        if (constraint.soft) append(constraint.group);
    }
    // Valid packed batches cover weight_bytes exactly with monotone spans.
    // Nonempty bytes therefore mean at least one soft clause. Metadata queries
    // need only O(number of batches), including enormous hard-only instances;
    // full span/weight validation belongs to typeCheck and the packed writer.
    for (const auto& batch : model.packed_bool_clauses) {
        if (!batch.weight_bytes.empty()) {
            append("");
            break;
        }
    }
    return result;
}

inline std::size_t objectiveCountWithSoft(const ConstraintModel& model) {
    return softObjectiveGroups(model).size() + model.objectives.size();
}

} // namespace SOMTParser::Uir::Hir
