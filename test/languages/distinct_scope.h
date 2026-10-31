#pragma once

#include "somtparser/frontend/parser.h"
#include <algorithm>
#include <string>
#include <unordered_set>
#include <vector>

namespace SomtTest {

// Inspect the actual distinct operands, independent of commutative print order
// and of array cells that appear only in separate domain-bound assertions.
inline bool hasDistinctArguments(const SOMTParser::ParserPtr& parser,
                                 std::vector<std::string> expected) {
    std::sort(expected.begin(), expected.end());
    auto stack = parser->getAssertions();
    std::unordered_set<const SOMTParser::DAGNode*> visited;
    while (!stack.empty()) {
        auto node = stack.back();
        stack.pop_back();
        if (!visited.insert(node.get()).second) { continue; }
        if (node->isDistinct()) {
            std::vector<std::string> actual;
            for (const auto& child : node->getChildren()) {
                actual.push_back(parser->toString(child));
            }
            std::sort(actual.begin(), actual.end());
            if (actual == expected) { return true; }
        }
        for (const auto& child : node->getChildren()) { stack.push_back(child); }
    }
    return false;
}

} // namespace SomtTest
