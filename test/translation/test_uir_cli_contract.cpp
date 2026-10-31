// The CLI's dialect names are part of the published contract: the evaluation
// pipeline passes them through and groups results by them.
#include "somtparser/lowering/omt_emitter.h"
#include "somtparser/translation/profile.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;

int main() {
    // Every dialect has a stable name, and the names round-trip.
    struct { Lower::OmtDialect d; const char* name; } kCases[] = {
        {Lower::OmtDialect::SmtLib2025,  "smtlib-omt-2025"},
        {Lower::OmtDialect::Z3,          "z3"},
        {Lower::OmtDialect::OptiMathSAT, "optimathsat"},
        {Lower::OmtDialect::None,        "none"},
    };
    for (const auto& c : kCases) {
        assert(std::string(Lower::omtDialectName(c.d)) == c.name);
    }

    // Every advertised profile actually resolves, so --list-profiles cannot
    // print a name that --profile then rejects.
    for (const auto& id : Uir::EncodingProfile::builtinIds()) {
        assert(Uir::EncodingProfile::builtin(id) != nullptr);
    }

    std::cout << "All CLI contract tests passed." << std::endl;
    return 0;
}
