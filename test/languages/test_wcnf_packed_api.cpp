#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include "test_helpers.h"

#include <stdexcept>
#include <string>

using namespace SOMTParser;

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::SourceUnit legacy;
    legacy.inline_source = "p wcnf 1 1 10\n1 1 0\n";
    TranslateOptions legacy_options;
    legacy_options.language_id = "wcnf";
    const Translation legacy_result = translate(legacy, legacy_options);
    VERIFY(legacy_result.ok());
    VERIFY(legacy_result.hasParser());
    VERIFY(!legacy_result.usesPackedSmtStream());
    VERIFY(static_cast<bool>(legacy_result.parser()));

    Lang::SourceUnit unit;
    unit.display_name = "<wcnf-packed-api>";
    unit.inline_source =
        "p wcnf 3 5 9007199254740994\n"
        "9007199254740994 1 0\n"
        "4 -2 3 0\n"
        "h -1 0\n"
        "2 0\n"
        "9007199254740993 3 0\n";
    TranslateOptions options;
    options.language_id = "wcnf";
    options.omt_dialect = Lower::OmtDialect::Z3;
    options.parse.options["packed"] = "1";
    const Translation result = translate(unit, options);
    VERIFY(result.ok());
    VERIFY(result.usesPackedSmtStream());
    VERIFY(!result.hasParser());

    bool parser_guarded = false;
    try { (void)result.parser(); }
    catch (const std::logic_error&) { parser_guarded = true; }
    VERIFY(parser_guarded);
    VERIFY(result.objectiveCount() == 1);
    VERIFY(result.toSmt2() ==
        "(declare-const x1 Bool)\n"
        "(declare-const x2 Bool)\n"
        "(declare-const x3 Bool)\n"
        "(assert (or x1))\n"
        "(assert-soft (or (not x2) x3) :weight 4)\n"
        "(assert (or (not x1)))\n"
        "(assert-soft false :weight 2)\n"
        "(assert-soft (or x3) :weight 9007199254740993)\n"
        "(check-sat)\n(exit)\n");

    Lang::SourceUnit empty;
    empty.inline_source = "p wcnf 0 1 9\n9 0\n";
    const Translation empty_result = translate(empty, options);
    VERIFY(empty_result.ok());
    VERIFY(empty_result.toSmt2() == "(assert false)\n(check-sat)\n(exit)\n");

    Lang::SourceUnit large_top;
    large_top.inline_source =
        "p wcnf 2 2 9007199254740993\n"
        "9007199254740993 1 0\n"
        "9 2 0\n";
    const Translation top_result = translate(large_top, options);
    VERIFY(top_result.ok());
    VERIFY(top_result.toSmt2() ==
        "(declare-const x1 Bool)\n"
        "(declare-const x2 Bool)\n"
        "(assert (or x1))\n"
        "(assert-soft (or x2) :weight 9)\n"
        "(check-sat)\n(exit)\n");

    // Costs/top are exact text in either representation. The values exceed
    // signed 64-bit and differ by one, so neither stoll nor double suffices.
    for (const std::string& packed : {std::string("0"), std::string("1")}) {
        TranslateOptions exact_options;
        exact_options.language_id = "wcnf";
        exact_options.parse.options["packed"] = packed;
        Lang::SourceUnit exact;
        exact.inline_source =
            "p wcnf 2 3 00018446744073709551618\n"
            "18446744073709551618 1 2 0\n"
            "18446744073709551619 -2 0\n"
            "00018446744073709551617 -1 0\n";
        const Translation translated = translate(exact, exact_options);
        VERIFY(translated.ok());
        const std::string script = translated.toSmt2();
        const std::size_t first_soft = script.find("(assert-soft");
        VERIFY(first_soft != std::string::npos);
        VERIFY(script.find("(assert-soft", first_soft + 1) == std::string::npos);
        VERIFY(script.find(":weight 18446744073709551617") != std::string::npos);
        VERIFY(script.find(":weight 18446744073709551618") == std::string::npos);
        VERIFY(script.find(":weight 18446744073709551619") == std::string::npos);
    }

    Lang::SourceUnit bad_range;
    bad_range.inline_source = "p wcnf 1 1\n1 2 0\n";
    options.parse.strict = true;
    const Translation rejected = translate(bad_range, options);
    VERIFY(!rejected.ok());
    VERIFY(!rejected.diagnostics().all().empty());
}
