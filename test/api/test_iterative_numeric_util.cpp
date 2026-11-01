#include "somtparser/frontend/parser.h"
#include "somtparser/core/util.h"
#include "test_helpers.h"

#include <string>
#include <vector>

using namespace SOMTParser;
using Node = std::shared_ptr<DAGNode>;

static Node raw(const ParserPtr& parser, const std::shared_ptr<Sort>& sort,
                NODE_KIND kind, std::vector<Node> children) {
    return parser->getNodeManager()->createNode(sort, kind, kindToString(kind), std::move(children));
}

static std::string fpDump(const ParserPtr& parser, const Node& value) {
    auto fp = raw(parser, SortManager::FLOAT32_SORT, NODE_KIND::NT_FP_TO_FP,
        {parser->mkConstInt(8), parser->mkConstInt(24), parser->mkExpr("RNE"), value});
    return dumpSMTLIB2(fp);
}

static void checkExactDeepNumbers() {
    auto parser = newParser();
    auto one = parser->mkConstReal(std::string("1.0"));
    auto term = one;
    for (int i = 0; i < 30000; ++i) {
        term = raw(parser, SortManager::REAL_SORT, NODE_KIND::NT_NEG, {term});
    }
    VERIFY(fpDump(parser, term) == fpDump(parser, one));
    // Repeated edges must use memoized values, not enumerate 2^40 paths.
    term = one;
    for (int i = 0; i < 40; ++i) {
        term = raw(parser, SortManager::REAL_SORT, NODE_KIND::NT_ADD, {term, term});
    }
    VERIFY(fpDump(parser, term) == fpDump(parser, parser->mkConstReal(std::string("1099511627776.0"))));
    for (int a : {-7, 7}) {
        for (int b : {-2, 2}) {
            auto div = raw(parser, SortManager::INT_SORT, NODE_KIND::NT_DIV_INT,
                {parser->mkConstInt(a), parser->mkConstInt(b)});
            auto real = raw(parser, SortManager::REAL_SORT, NODE_KIND::NT_TO_REAL, {div});
            const int expected = a == -7 ? (b == -2 ? 4 : -4) : (b == -2 ? -3 : 3);
            VERIFY(fpDump(parser, real) == fpDump(parser, parser->mkConstReal(std::to_string(expected))));
        }
    }
    auto symbolic_rm = parser->mkVar(SortManager::ROUNDING_MODE_SORT, "rounding_choice");
    auto symbolic_fp = raw(parser, SortManager::FLOAT32_SORT, NODE_KIND::NT_FP_TO_FP,
        {parser->mkConstInt(8), parser->mkConstInt(24), symbolic_rm, parser->mkConstReal(std::string("1.1"))});
    VERIFY(dumpSMTLIB2(symbolic_fp).find("rounding_choice") != std::string::npos);
    VERIFY(dumpSMTLIB2(symbolic_fp).find("to_fp") != std::string::npos);
    auto ratio = raw(parser, SortManager::REAL_SORT, NODE_KIND::NT_DIV_REAL,
        {parser->mkConstReal(std::string("7.0")), parser->mkConstReal(std::string("2.0"))});
    VERIFY(fpDump(parser, ratio) == fpDump(parser, parser->mkConstReal(std::string("3.5"))));
    auto zero = raw(parser, SortManager::REAL_SORT, NODE_KIND::NT_DIV_REAL,
        {one, parser->mkConstReal(std::string("0.0"))});
    VERIFY(fpDump(parser, zero).find("to_fp") != std::string::npos);
    VERIFY(fpDump(parser, parser->mkVarReal("unknown")).find("unknown") != std::string::npos);
}

static void checkUFPreorderAndSharing() {
    auto parser = newParser();
    auto a = parser->mkApplyUF(SortManager::INT_SORT, "f", {parser->mkConstInt(1)});
    auto b = parser->mkApplyUF(SortManager::INT_SORT, "f", {parser->mkConstInt(2)});
    auto c = parser->mkApplyUF(SortManager::INT_SORT, "f", {a});
    auto root = c;
    for (int i = 0; i < 30000; ++i) {
        root = raw(parser, SortManager::INT_SORT, NODE_KIND::NT_ADD, {root, a});
    }
    auto applications = collectUFApplications({nullptr, root, b, root});
    VERIFY(applications.size() == 1);
    const auto& f = applications.at("f");
    VERIFY(f.size() == 3);
    VERIFY(f[0].application_node == c);
    VERIFY(f[1].application_node == a);
    VERIFY(f[2].application_node == b);
    VERIFY(f[0].args == c->getChildren());
    VERIFY(f[0].result_sort == SortManager::INT_SORT);
    VERIFY(collectUFApplications({}).empty());
}

int main() {
    checkExactDeepNumbers();
    checkUFPreorderAndSharing();
}
