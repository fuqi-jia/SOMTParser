// Official-corpus driver for the full public PDDL pipeline. No solver job is
// hidden here: the campaign independently loads the complete emitted module.
#include "somtparser/languages/pddl.h"
#include "somtparser/translation/translate.h"

#include <algorithm>
#include <climits>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>

int main(int argc, char** argv) {
    if (argc != 7) {
        std::cerr << "usage: pddl_translate DOMAIN PROBLEM HORIZON SMT_PATH REPORT_PATH strict|lenient\n";
        return 64;
    }
    const std::string horizon = argv[3], target = argv[4], report = argv[5], mode = argv[6];
    if (horizon.empty() || !std::all_of(horizon.begin(), horizon.end(),
            [](char c) { return c >= '0' && c <= '9'; })
        || (mode != "strict" && mode != "lenient") || report.empty() || report == "-"
        || target.empty() || target == report) {
        std::cerr << "invalid explicit horizon, requirements mode, or output paths\n";
        return 64;
    }
    try {
        if (std::stoull(horizon) > UINT_MAX) { return 64; }
    } catch (const std::exception&) { return 64; }
    try {
        // Resolve relative spelling and existing directory symlinks before
        // creating either output, including when both files do not yet exist.
        if (target != "-" && std::filesystem::weakly_canonical(target)
                == std::filesystem::weakly_canonical(report)) {
            std::cerr << "SMT and report outputs must be different paths\n";
            return 64;
        }
        if (std::filesystem::exists(report)
            || (target != "-" && std::filesystem::exists(target))) {
            std::cerr << "output exists; refusing to overwrite previous evidence\n";
            return 74;
        }
        using namespace SOMTParser;
        auto& registry = Lang::LanguageRegistry::instance();
        if (!registry.byId("pddl")) { registry.add(Lang::mkPddlLanguage()); }
        Lang::SourceUnit unit;
        unit.main_path = argv[1];
        unit.display_name = argv[1];
        unit.data_paths.push_back(argv[2]);
        TranslateOptions options;
        options.language_id = "pddl";
        options.profile_id = "bmc";
        options.omt_dialect = Lower::OmtDialect::Z3;
        options.timeout_ms = 0;
        options.parse.options["plan_horizon"] = horizon;
        options.parse.options["lenient_requirements"] = mode == "lenient" ? "true" : "false";
        const auto translated = translate(unit, options);
        for (const auto& message : translated.diagnostics().all()) {
            const char* severity = message.severity == Uir::Severity::ERROR ? "ERROR"
                : message.severity == Uir::Severity::WARNING ? "WARNING" : "NOTE";
            std::cerr << severity << ' ' << Uir::errorCodeName(message.code) << ' '
                << message.loc.file << ':' << message.loc.line << ':' << message.loc.column
                << ' ' << message.message << '\n';
        }
        std::ofstream reportStream(report, std::ios::binary);
        reportStream.exceptions(std::ios::failbit | std::ios::badbit);
        reportStream << translated.report().toJson() << '\n';
        reportStream.close();
        if (!translated.ok()) { return 2; }
        if (target == "-") {
            std::cout.exceptions(std::ios::failbit | std::ios::badbit);
            translated.writeSmt2(std::cout, Lower::OmtDialect::Z3);
            std::cout.flush();
        } else {
            std::ofstream output(target, std::ios::binary);
            output.exceptions(std::ios::failbit | std::ios::badbit);
            translated.writeSmt2(output, Lower::OmtDialect::Z3);
            output.close();
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "pddl_translate output/exception: " << error.what() << '\n';
        return 74;
    }
}
