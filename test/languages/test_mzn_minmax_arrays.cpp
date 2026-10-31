// MiniZinc numeric max/min overloads preserve numeric value semantics.

#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation translateMiniZinc(const std::string& source) {
    Lang::SourceUnit unit;
    unit.inline_source = source;
    unit.display_name = "<minizinc-minmax-test>";
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

} // namespace

int main() {
    std::cout << "======= MiniZinc: numeric min/max overloads =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        const Translation t = translateMiniZinc(
            "constraint max(-7, -2) = -2;\n"
            "constraint min(-7, -2) = -7;\n"
            "constraint max([-9, -2, -5]) = -2;\n"
            "constraint min([-9, -2, -5]) = -9;\n"
            "constraint max(1.25, -2.5) = 1.25;\n"
            "int: literal_max = max([-4, 9, 2]);\n"
            "constraint literal_max = 9;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
    }

    {
        const Translation t = translateMiniZinc(
            "array[0..1,4..5] of var -8..8: m;\n"
            "constraint min(m) = -6;\n"
            "constraint max(m) = 7;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
    }

    {
        const Translation t = translateMiniZinc(
            "constraint max([]) = 0;\nsolve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    return 0;
}
