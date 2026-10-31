#ifndef SOMTPARSER_TEST_PLANNING_PUBLIC_PIPELINE_HEADER
#define SOMTPARSER_TEST_PLANNING_PUBLIC_PIPELINE_HEADER

#include "somtparser/languages/pddl.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <atomic>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>

namespace SomtPlanningTest {

// The public frontend accepts the problem through SourceUnit::data_paths.
// Keep this fixture alive until translate() has finished reading that file.
class ProblemFile {
public:
    explicit ProblemFile(const std::string& source) {
        static std::atomic<unsigned long long> next{0};
        const auto stamp = std::chrono::steady_clock::now().time_since_epoch().count();
        for (;;) {
            directory_ = std::filesystem::temp_directory_path()
                / ("somt-pddl-public-" + std::to_string(stamp) + "-" + std::to_string(next++));
            if (std::filesystem::create_directory(directory_)) { break; }
        }
        std::ofstream stream(path(), std::ios::binary);
        stream << source;
        stream.close();
        VERIFY(stream.good());
    }
    ~ProblemFile() {
        std::error_code error;
        std::filesystem::remove(path(), error);
        std::filesystem::remove(directory_, error);
    }
    std::filesystem::path path() const { return directory_ / "problem.pddl"; }
    ProblemFile(const ProblemFile&) = delete;
    ProblemFile& operator=(const ProblemFile&) = delete;
private:
    std::filesystem::path directory_;
};

inline SOMTParser::Translation publicTranslation(
    const std::string& domain, const std::string& problem,
    const std::string& name, unsigned horizon, bool accepted) {
    using namespace SOMTParser;
    namespace S = Uir::Sem;
    auto& registry = Lang::LanguageRegistry::instance();
    if (!registry.byId("pddl")) { registry.add(Lang::mkPddlLanguage()); }
    ProblemFile file(problem);
    Lang::SourceUnit unit;
    unit.inline_source = domain;
    unit.display_name = name;
    unit.data_paths.push_back(file.path().string());
    TranslateOptions options;
    options.language_id = "pddl";
    options.profile_id = "bmc";
    options.omt_dialect = Lower::OmtDialect::Z3;
    options.parse.options["plan_horizon"] = std::to_string(horizon);
    auto translation = translate(unit, options);
    if (translation.ok() != accepted) {
        std::cerr << "public PDDL pipeline: " << name << '\n';
        for (const auto& message : translation.diagnostics().all()) {
            std::cerr << message.message << '\n';
        }
    }
    VERIFY(translation.ok() == accepted);
    if (!accepted) {
        VERIFY(translation.diagnostics().hasErrors());
        return translation;
    }
    Uir::Diagnostics diagnostics;
    VERIFY(translation.semantics().validate(diagnostics));
    const auto& stages = translation.semantics().stages();
    VERIFY(stages.size() >= 2);
    VERIFY(stages.front().source.id == "pddl");
    VERIFY(S::validateSourceContract(S::sourceSemanticSpec("pddl"), stages.front(), diagnostics));
    VERIFY(stages.front().source.assumptions.functions == S::FunctionSemantics::MIXED);
    VERIFY(stages.front().source.assumptions.undefined == S::UndefinedSemantics::STRICT);
    VERIFY(!translation.report().fidelity().complete);
    bool hasHorizon = false;
    for (const auto& bound : translation.report().fidelity().bounds) {
        if (bound.kind == Uir::Fidelity::Bound::PLAN_HORIZON) {
            VERIFY(bound.value == horizon);
            hasHorizon = true;
        }
    }
    VERIFY(hasHorizon);
    VERIFY(!diagnostics.hasErrors());
    return translation;
}

} // namespace SomtPlanningTest
#endif
