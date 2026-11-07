#include "somtparser/parser.h"

#include <array>

std::array<const void*, 3> kindTableAddressesFromOtherTranslationUnit() {
    return {&SOMTParser::static_kinds, &SOMTParser::kind_key_map,
            &SOMTParser::oper_key_map};
}
