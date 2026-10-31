#include <functional>
#include <memory>
#include <string>

#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

namespace {

size_t legacyHashCode(DAGNode& node) {
    const auto children = node.getChildren();
    size_t combined_hash = 0;
    for (const auto& child : children) {
        const size_t child_hash = child->hashCode();
        combined_hash ^= child_hash + 0x9e3779b9 + (combined_hash << 6)
            + (combined_hash >> 2);
    }

    const size_t h1 = std::hash<std::string>{}(node.getSort()->toString());
    const size_t h2 = static_cast<size_t>(node.getKind());
    const size_t h3 = node.getName().empty()
        ? 0 : std::hash<std::string>{}(node.getName());
    const size_t h4 = children.size();
    const size_t h5 = children.empty()
        ? 0 : std::hash<std::string>{}(std::to_string(combined_hash));

    size_t seed = 0;
    seed ^= h1 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    seed ^= h2 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    seed ^= h3 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    seed ^= h4 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    seed ^= h5 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    seed ^= 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
}

} // namespace

int main() {
    auto parser = newParser();
    VERIFY(parser->parseStr("(set-logic QF_LIA)\n(declare-const x Int)\n"));

    const auto leaf = parser->mkExpr("x");
    const auto one = parser->mkExpr("1");
    const auto sum = parser->mkExpr("(+ x 1)");
    const auto other_sum = parser->mkExpr("(+ x 2)");
    VERIFY(leaf != nullptr && one != nullptr && sum != nullptr && other_sum != nullptr);

    // The compact stored value must produce exactly the same public hash as
    // the former decimal-string representation, including the empty sentinel
    // used by leaves. A present raw value is distinct from the empty sentinel.
    VERIFY(leaf->hashCode() == legacyHashCode(*leaf));
    VERIFY(sum->hashCode() == legacyHashCode(*sum));

    const auto equivalent_sum = std::make_shared<DAGNode>(
        sum->getSort(), sum->getKind(), sum->getName(), sum->getChildren());
    VERIFY(equivalent_sum->hashCode() == legacyHashCode(*equivalent_sum));
    VERIFY(sum->isEquivalentTo(*equivalent_sum));
    VERIFY(!sum->isEquivalentTo(*other_sum));
    VERIFY(dumpSMTLIB2(sum) == dumpSMTLIB2(equivalent_sum));
    const auto ordered_sum = std::make_shared<DAGNode>(
        sum->getSort(), sum->getKind(), sum->getName(),
        std::vector<std::shared_ptr<DAGNode>>{leaf, one});
    VERIFY(dumpSMTLIB2(ordered_sum) == "(+ x 1)");
    const DAGNode copied(*ordered_sum);
    VERIFY(copied.hashCode() == ordered_sum->hashCode());
    VERIFY(copied.isEquivalentTo(*ordered_sum));
    std::cout << "sizeof_DAGNode=" << sizeof(DAGNode) << '\n';
}
