#include "somtparser/frontend/parser.h"
#include "somtparser/frontend/symbol_manager.h"
#include "test_helpers.h"

#include <memory>
#include <string>
#include <vector>

using namespace SOMTParser;

int main() {
    auto parser = newParser();
    // A repeated selector sort must not be mistaken for a cycle in the
    // current constructor path. The old visited set leaked across siblings.
    VERIFY(parser->parseStr("(declare-datatypes ((Leaf 0) (Pair 0)) "
        "(((leaf)) ((pair (left Leaf) (right Leaf)))))"));
    auto pair = parser->mkDefaultDTValue(parser->getSymbolManager()->resolveSort("Pair"));
    VERIFY(pair && pair->getChildrenSize() == 2);
    VERIFY(pair->getChild(0)->getName() == "leaf");
    VERIFY(pair->getChild(1)->getName() == "leaf");

    VERIFY(parser->parseStr("(declare-datatypes ((Choice 0)) "
        "(((loop (next Choice)) (value (payload Int)))))"));
    auto choice_sort = parser->getSymbolManager()->resolveSort("Choice");
    VERIFY(parser->isRecursiveDatatype(choice_sort));
    auto choice = parser->mkDefaultDTValue(choice_sort);
    VERIFY(choice && choice->getName() == "value");

    {
        auto nested_parser = newParser();
        std::string script = "(declare-const nested ";
        for (std::size_t i = 0; i < 3000; ++i) script += "(Set ";
        script += "Int";
        script.append(3000, ')');
        script += ")";
        VERIFY(nested_parser->parseStr(script));
        auto sort = nested_parser->getVariable("nested")->getSort();
        for (std::size_t i = 0; i < 3000; ++i) {
            VERIFY(sort && sort->isSet() && sort->children.size() == 1);
            sort = sort->children[0];
        }
        VERIFY(sort->isInt());
        // A failed nested sort must not leave operands in the next parse.
        VERIFY(!nested_parser->parseStr("(declare-const bad (Array Int))"));
        VERIFY(nested_parser->parseStr("(declare-const good (Array Int Bool))"));
    }

    constexpr std::size_t depth = 20000;
    std::vector<std::shared_ptr<Sort>> sorts;
    sorts.reserve(depth);
    for (std::size_t i = 0; i < depth; ++i)
        sorts.push_back(std::make_shared<Sort>(SORT_KIND::SK_DATATYPE, "D" + std::to_string(i)));
    for (std::size_t i = 0; i < depth; ++i) {
        Sort::DtConstructor constructor;
        constructor.name = "makeD" + std::to_string(i);
        if (i + 1 < depth)
            constructor.selectors.push_back({"nextD" + std::to_string(i), sorts[i + 1]});
        sorts[i]->dt_constructors = std::make_shared<std::vector<Sort::DtConstructor>>(
            std::initializer_list<Sort::DtConstructor>{constructor});
        parser->getSymbolManager()->registerSort(sorts[i]->name, sorts[i]);
    }
    VERIFY(!parser->isRecursiveDatatype(sorts.front()));
    auto value = parser->mkDefaultDTValue(sorts.front());
    VERIFY(value != nullptr);
    auto cursor = value;
    for (std::size_t i = 0; i < depth; ++i) {
        VERIFY(cursor && cursor->getName() == "makeD" + std::to_string(i));
        if (i + 1 < depth) cursor = cursor->getChild(0);
    }
    VERIFY(cursor->getChildrenSize() == 0);
    const auto dump = parser->dumpSMT2();
    const auto first = dump.find("(declare-datatypes ((D0 0))");
    const auto last = dump.find("(declare-datatypes ((D19999 0))");
    VERIFY(first != std::string::npos && last != std::string::npos && last < first);
    auto reparsed = newParser();
    VERIFY(reparsed->parseStr(dump));
    VERIFY(reparsed->getSymbolManager()->resolveSort("D0") != nullptr);

    // Keep ownership teardown separate from this traversal regression. Sort
    // reclamation has its own deep-chain regression; do not hide a cycle leak.
    for (auto& sort : sorts) sort->dt_constructors.reset();
    return 0;
}
