#include "somtparser/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& text, const std::string& part) {
    return text.find(part) != std::string::npos;
}

} // namespace

int main() {
    std::cout << "======= Z3 hardware bit-vector aliases =======\n";

    const std::string source =
        "(set-logic ALL)\n"
        "(declare-fun x () (_ BitVec 8))\n"
        "(declare-fun y () (_ BitVec 8))\n"
        "(assert (= (bvudiv_i x y) #x00))\n"
        "(assert (= (bvurem_i x y) #x00))\n"
        "(assert (= (bvsdiv_i x y) #x00))\n"
        "(assert (= (bvsrem_i x y) #x00))\n"
        "(assert (= (bvsmod_i x y) #x00))\n";

    ParserPtr parser = newParser();
    VERIFY(parser->parseStr(source));
    const std::string canonical = parser->dumpSMT2();
    VERIFY(!has(canonical, "bvudiv_i"));
    VERIFY(!has(canonical, "bvurem_i"));
    VERIFY(!has(canonical, "bvsdiv_i"));
    VERIFY(!has(canonical, "bvsrem_i"));
    VERIFY(!has(canonical, "bvsmod_i"));
    VERIFY(has(canonical, "bvudiv"));
    VERIFY(has(canonical, "bvsrem"));

    ParserPtr reader = newParser();
    VERIFY(reader->parseStr(canonical));

    std::cout << "All Z3 hardware-alias tests passed.\n";
    return 0;
}
