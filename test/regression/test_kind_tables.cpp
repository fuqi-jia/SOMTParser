#include "somtparser/parser.h"

#include <array>
#include <iostream>

#include "test_helpers.h"

std::array<const void*, 3> kindTableAddressesFromOtherTranslationUnit();

int main() {
    using namespace SOMTParser;
    const std::array<const void*, 3> local = {
        &static_kinds, &kind_key_map, &oper_key_map};
    VERIFY(local == kindTableAddressesFromOtherTranslationUnit());

    VERIFY(static_kinds.count(NODE_KIND::NT_CONST_TRUE) == 1);
    VERIFY(static_kinds.count(NODE_KIND::NT_CONST_FALSE) == 1);
    VERIFY(static_kinds.count(NODE_KIND::NT_VAR) == 0);
    VERIFY(kind_key_map.at("true") == NODE_KIND::NT_CONST_TRUE);
    VERIFY(kind_key_map.at("false") == NODE_KIND::NT_CONST_FALSE);
    for (const auto& [symbol, kind] : oper_key_map) {
        VERIFY(getOperKind(symbol) == kind);
    }

    std::cout << "Kind lookup tables are shared and preserve operator lookup.\n";
    return 0;
}
