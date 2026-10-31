#include "planning_public_pipeline.h"
#include "test_helpers.h"
int main() {
    const std::string prefix = "(define (domain d) (:requirements :adl :preferences :constraints) (:predicates (p)) ";
    const std::string problem = "(define (problem p) (:domain d) (:init) (:goal (and)))";
    for (const auto& constraint : {"(preference soft (always (p)))", "(and (preference soft (sometime (p))))", "(forall (?x - object) (preference soft (at end (p))))"}) {
        auto result = SomtPlanningTest::publicTranslation(prefix + "(:constraints " + constraint + "))", problem, "domain-pref-refusal", 0, false);
        bool reason = false;
        for (const auto& message : result.diagnostics().all()) { reason |= message.message.find("domain :constraints must be hard") != std::string::npos; }
        VERIFY(reason);
    }
    SomtPlanningTest::publicTranslation(prefix + "(:constraints (always (p))))", problem, "hard-domain-unsat-is-valid-source", 0, true);
    return 0;
}
