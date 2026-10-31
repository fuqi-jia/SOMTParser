#include "somtparser/languages/lp.h"
#include "somtparser/translation/translate.h"
#include "../test_helpers.h"

#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

using namespace SOMTParser;

struct Case {
    std::string name;
    std::string source;
    bool inline_bounds = false;
    bool accepted = true;
};

int main(int argc, char** argv) {
    Lang::LanguageRegistry::instance().add(Lang::mkLpLanguage());
    const std::string head = "Minimize\n cost: x\nSubject To\n";
    std::string repeated;
    for (int i = 0; i < 4000; ++i) { repeated += " + 1 x\n"; }
    const std::vector<Case> cases = {
        {"long-default", head + " r:\n" + repeated + " <= 4000\nEnd\n"},
        {"long-inline-bounds", head + " r:\n" + repeated
            + " <= 4000 Bounds -1 <= x <= 2\nEnd\n", true},
        {"inline-positive-bound", head + " r: x <= 2 Bounds +1 <= x <= 2\nEnd\n", true},
        {"header-negative-bound", head + " r: x <= 2\nBounds -1 <= x <= 2\nEnd\n"},
        {"long-objective", "Minimize\n cost:\n" + repeated
            + "Subject To\n r: x <= 2\nEnd\n"},
        {"named-reset", head + " r: x >= 1\n s:\n + x\n <= 2\nBounds\n x free\nEnd\n"},
        {"unnamed-reset", head + " x >= 1\n + x\n <= 2\nBounds\n x free\nEnd\n"},
        {"inline-subject", "Minimize cost: x Subject To r:\n + x\n <= 2\nEnd\n"},
        {"inline-reset", head + " r: x >= 1\n s:\n + x\n <= 2 Bounds x free\nEnd\n", true},
        {"keyword-labels", head + " end:\n + x\n >= 1\n bounds:\n + x\n <= 2\nEnd\n", true},
        {"exact-duplicates", head + " r:\n + 0.1 x\n + 0.2 x\n + 0.3 x\n <= 0.6\nEnd\n"},
        {"integer-max", "Maximize\n cost: -2 x\nSubject To\n r:\n + x\n <= 2\nGenerals\n x\nEnd\n"},
        {"range-reset", head + " r: -1 <= x <= 3\n s:\n + x\n <= 2\nBounds\n x free\nEnd\n"},
        {"comments-crlf", head + " r:\r\n + x \\ ignore <= here\r\n\r\n \\ and here >=\r\n <= 2\r\nEnd\r\n"},
        {"inline-negative-lower", head + " r: x <= 3 Bounds -2 <= x <= 2\nEnd\n", true},
        {"inline-positive-lower", head + " r: x <= 3 Bounds +1 <= x <= 2\nEnd\n", true},
        {"header-negative-lower", head + " r: x <= 3\nBounds -2 <= x <= 2\nEnd\n"},
        {"header-positive-lower", head + " r: x <= 3\nBounds +1 <= x <= 2\nEnd\n"},
        {"inline-negative-exponent", head + " r: x <= 3 Bounds -.5e+1 <= x <= 2\nEnd\n", true},
        {"header-negative-exponent", head + " r: x <= 3\nBounds -.5e+1 <= x <= 2\nEnd\n"},
        {"inline-negative-infinity", head + " r: x <= 3 Bounds -inf <= x <= 2\nEnd\n", true},
        {"header-negative-infinity", head + " r: x <= 3\nBounds -infinity <= x <= 2\nEnd\n"},
        {"inline-double-sign", head + " r: x <= 3 Bounds --1 <= x <= 2\nEnd\n", true, false},
        {"inline-mixed-sign", head + " r: x <= 3 Bounds +-1 <= x <= 2\nEnd\n", true, false},
        {"header-double-sign", head + " r: x <= 3\nBounds --1 <= x <= 2\nEnd\n", false, false},
        {"disabled-inline-negative", head + " r: x <= 3 Bounds -2 <= x <= 2\nEnd\n", false, false},
        {"missing-rhs-before-label", head + " r: x <=\n s: x <= 2\nEnd\n", false, false},
        {"rhs-next-line", head + " r: x <=\n 2\nEnd\n", false, false},
        {"bound-sign-before-variable", head + " r: x <= 2 Bounds - x <= 2\nEnd\n", true, false},
        {"unfinished-before-bounds", head + " r: x\nBounds\n x free\nEnd\n", true, false}
    };
    const bool export_results = argc == 2;
    if (export_results) { std::filesystem::create_directories(argv[1]); }
    for (const auto& item : cases) {
        Lang::SourceUnit unit;
        unit.inline_source = item.source;
        unit.main_path = item.name + ".lp";
        unit.display_name = unit.main_path;
        TranslateOptions options;
        options.language_id = "lp";
        options.omt_dialect = Lower::OmtDialect::Z3;
        if (item.inline_bounds) { options.parse.options["inline_bounds"] = "true"; }
        const auto translated = translate(unit, options);
        if (translated.ok() != item.accepted) {
            std::cerr << item.name << ": " << translated.report().toJson() << '\n';
        }
        VERIFY(translated.ok() == item.accepted);
        if (item.accepted) { VERIFY(translated.objectiveCount() == 1); }
        if (export_results) {
            const auto prefix = std::filesystem::path(argv[1]) / item.name;
            std::ofstream source(prefix.string() + ".lp");
            source << item.source;
            source.close();
            VERIFY(source.good());
            std::ofstream report(prefix.string() + ".report.json");
            report << translated.report().toJson() << '\n';
            report.close();
            VERIFY(report.good());
            if (item.accepted) {
                translated.writeSmt2(prefix.string() + ".smt2", Lower::OmtDialect::Z3);
            }
        }
        std::cout << item.name << ": " << (item.accepted ? "accepted" : "rejected") << '\n';
    }
    return 0;
}
