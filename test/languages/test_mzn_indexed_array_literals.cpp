#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {
Translation run(const std::string& source) {
    Lang::SourceUnit unit;
    unit.display_name = "indexed-array-literal.mzn";
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

std::string errors(const Translation& translation) {
    std::string text;
    for (const auto& d : translation.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { text += d.message + "\n"; }
    }
    return text;
}
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // Explicit keys are sorted by their index tuple, independent of source order.
    auto explicit_keys = run(
        "array[2..4] of var int:a=[4:30,2:10,3:20];"
        "constraint a[2]=10 /\\ a[3]=20 /\\ a[4]=30;solve satisfy;");
    VERIFY(explicit_keys.ok());
    VERIFY(explicit_keys.toSmt2().find("false") == std::string::npos);

    auto start_only = run(
        "array[2..4] of var int:a=[2:10,20,30];"
        "constraint a[2]=10 /\\ a[3]=20 /\\ a[4]=30;solve satisfy;");
    VERIFY(start_only.ok());
    VERIFY(start_only.toSmt2().find("false") == std::string::npos);

    auto enum_keys = run(
        "enum E={a,b,c};array[E] of var int:x=[c:30,a:10,b:20];"
        "constraint x[a]=10 /\\ x[b]=20 /\\ x[c]=30;solve satisfy;");
    VERIFY(enum_keys.ok());

    auto matrix = run(
        "array[2..3,4..5] of var int:x="
        "[(3,5):4,(2,4):1,(3,4):3,(2,5):2];"
        "constraint x[3,4]=3;solve satisfy;");
    VERIFY(matrix.ok());

    auto hole = run(
        "array[2..3] of var int:x=[2:_,3:4];"
        "constraint x[2]=1;solve satisfy;");
    VERIFY(hole.ok());

    auto mixed_enum = run(
        "enum E={a,b};enum F={c,d};"
        "array[int] of var int:x=[a:1,d:2];solve satisfy;");
    VERIFY(mixed_enum.ok());

    for (const std::string literal : {
             "[2:10,20,4:30]", "[2:10,3:20,30]"}) {
        auto mixed = run("array[2..4] of var int:x=" + literal + ";solve satisfy;");
        VERIFY(!mixed.ok());
        VERIFY(errors(mixed).find("mixing indexed and non-indexed") != std::string::npos);
    }

    for (const std::string literal : {
             "[2:10,2:20]", "[2:10,4:20]",
             "[(1,1):0,(1,3):1,(2,1):0,(2,3):2]"}) {
        auto invalid = run("array[int] of var int:x=" + literal + ";solve satisfy;");
        VERIFY(!invalid.ok());
        VERIFY(errors(invalid).find("duplicate index tuples") != std::string::npos
               || errors(invalid).find("contiguous rectangular") != std::string::npos);
    }

    // An enum start-only index that runs beyond the enum range is undefined;
    // MiniZinc makes that false in a Boolean context, including array init.
    auto enum_overflow = run(
        "enum E={a,b};array[int] of var int:x=[a:10,20,30];solve satisfy;");
    VERIFY(enum_overflow.ok());
    VERIFY(enum_overflow.toSmt2().find("false") != std::string::npos);

    std::cout << "MiniZinc indexed array literal tests passed.\n";
}
