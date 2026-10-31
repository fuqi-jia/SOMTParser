// HDDL bounded translation: hierarchy, partial orders, and the two bounds.

#include "somtparser/frontend/parser.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

Translation run(
    unsigned horizon, unsigned depth,
    const std::string& domain =
        "languages/hddl/instances/ok/transport-domain.hddl",
    const std::string& problem =
        "languages/hddl/instances/ok/transport-problem.hddl") {
    Lang::SourceUnit unit;
    unit.main_path = domain;
    unit.display_name = domain;
    unit.data_paths.push_back(problem);
    TranslateOptions options;
    options.language_id = "hddl";
    options.profile_id = "bmc";
    options.parse.options["plan_horizon"] = std::to_string(horizon);
    options.parse.options["decomposition_depth"] = std::to_string(depth);
    return translate(unit, options);
}

} // namespace

int main() {
    std::cout << "======= HDDL frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* language = Lang::LanguageRegistry::instance().byId("hddl");
    assert(language != nullptr);
    assert(language->acceptsDataFiles());
    assert(language->sniff("(define (domain d) (:task t) (:method m))") > 0.5);
    assert(language->sniff("(define (domain d) (:action a))") == 0.0);

    // A primitive action is admitted only if a bounded decomposition produces
    // it. The unrelated teleport action is validated, then omitted from the
    // transition system because alpha_HTN cannot select it.
    {
        const Translation translation = run(1, 1);
        assert(translation.ok());
        const std::string smt = translation.toSmt2();
        assert(has(smt, "do_drive_truck1_l1_l2@0"));
        assert(!has(smt, "do_teleport_truck1_l2@0"));
        // The static road relation has only l1 -> l2. Its necessary
        // condition propagates through the direct primitive subtask.
        VERIFY(!has(smt, "do_drive_truck1_l2_l2@0"));
        VERIFY(has(smt, "(assert do_drive_truck1_l1_l2@0)"));
        assert(!has(smt, "(assert (or do_teleport"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));

        const auto& stages = translation.semantics().stages();
        assert(stages.size() == 2);
        assert(stages.front().id == "hddl-to-typed-relational-core-v1");
        assert(stages.front().source.id == "hddl");
        assert(stages.front().decision.source == Sem::DecisionKind::PLAN_EXISTENCE);
        assert(!stages.front().source_signature.symbols.empty());
        assert(!stages.front().symbol_map.empty());
        assert(!stages.front().target_axioms.empty());
        Diagnostics contract_diagnostics;
        assert(translation.semantics().validate(contract_diagnostics));
    }

    // beta decodes one-hot action coordinates and removes generated noops.
    {
        const Translation translation = run(2, 1);
        assert(translation.ok());
        Sem::Assignment target{
            {"do_drive_truck1_l1_l2@0", "true"},
            {"do_drive_truck1_l1_l1@0", "false"},
            {"do_drive_truck1_l2_l1@0", "false"},
            {"do_drive_truck1_l2_l2@0", "false"},
            {"do_teleport_truck1_l1@0", "false"},
            {"do_teleport_truck1_l2@0", "false"},
            {"__pddl_noop@0", "false"},
            {"do_drive_truck1_l1_l2@1", "false"},
            {"do_drive_truck1_l1_l1@1", "false"},
            {"do_drive_truck1_l2_l1@1", "false"},
            {"do_drive_truck1_l2_l2@1", "false"},
            {"do_teleport_truck1_l1@1", "false"},
            {"do_teleport_truck1_l2@1", "false"},
            {"__pddl_noop@1", "true"},
        };
        Sem::Assignment source;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, source, diagnostics));
        assert(source.size() == 1);
        assert(source.at("plan[0]") == "(drive truck1 l1 l2)");
    }

    // Both independent under-approximation coordinates are public metadata.
    {
        const Translation translation = run(3, 2);
        assert(translation.ok());
        bool horizon = false;
        bool depth = false;
        for (const Fidelity::Bound& bound : translation.report().fidelity().bounds) {
            horizon = horizon
                   || (bound.kind == Fidelity::Bound::PLAN_HORIZON
                       && bound.value == 3);
            depth = depth
                 || (bound.kind == Fidelity::Bound::DECOMPOSITION_DEPTH
                     && bound.value == 2);
        }
        assert(horizon && depth);
        assert(translation.report().fidelity().sound);
        assert(!translation.report().fidelity().complete);
        assert(has(translation.report().toJson(), "PLAN_HORIZON"));
        assert(has(translation.report().toJson(), "DECOMPOSITION_DEPTH"));
    }

    // The official reference corpus requires interleaving two ordered method
    // expansions. Concatenating whole method bodies would omit valid plans.
    {
        const Translation translation = run(
            4, 1, "languages/hddl/instances/upstream/interleaving-d.hddl",
            "languages/hddl/instances/upstream/interleaving-p.hddl");
        assert(translation.ok());
        const std::string smt = translation.toSmt2();
        assert(has(smt, "do_a@0"));
        assert(has(smt, "do_b@1"));
        assert(has(smt, "do_c@2"));
        assert(has(smt, "do_d@3"));
    }

    // Empty methods denote the empty primitive frontier and therefore admit a
    // zero-length plan, rather than being mistaken for a missing method.
    {
        const Translation translation = run(
            0, 1, "languages/hddl/instances/upstream/empty-d.hddl",
            "languages/hddl/instances/upstream/empty-p.hddl");
        assert(translation.ok());
        assert(has(translation.toSmt2(), "(assert true)"));
    }

    // With no method expansion available, a goal-reaching primitive action
    // must not leak through the shared PDDL transition system.
    {
        const Translation translation = run(
            1, 0, "languages/hddl/instances/ok/transport-domain.hddl",
            "languages/hddl/instances/ok/transport-blocked-problem.hddl");
        assert(translation.ok());
        assert(has(translation.toSmt2(), "(assert false)"));
    }

    // No hidden defaults: both bounds are part of the question being asked.
    {
        Lang::SourceUnit unit;
        unit.main_path = "languages/hddl/instances/ok/transport-domain.hddl";
        unit.data_paths.push_back(
            "languages/hddl/instances/ok/transport-problem.hddl");
        TranslateOptions options;
        options.language_id = "hddl";
        options.profile_id = "bmc";
        options.parse.options["plan_horizon"] = "1";
        const Translation translation = translate(unit, options);
        assert(!translation.ok());
        assert(has(translation.diagnostics().all()[0].message,
                   "decomposition_depth"));
    }

    // Method state conditions use the reference prefix-task compilation.
    // A missing requirement still needs explicit lenience; the accepted case
    // retains a method event without consuming a source primitive action.
    {
        const std::string undeclared =
            "(define (domain test-domain) (:requirements :hierarchy) (:predicates (p)) "
            "(:task task1) (:method m :task (task1) :precondition (p) :subtasks (and)))";
        const std::string declared =
            "(define (domain test-domain) (:requirements :hierarchy :htn-method-pre-eff) "
            "(:predicates (p)) (:task task1) (:method m :task (task1) "
            ":precondition (p) :subtasks (and)))";
        const auto check = [&](const std::string& source, bool lenient, bool ready = true) {
            Lang::SourceUnit unit;
            unit.main_path = "conditional.hddl";
            unit.inline_source = source;
            unit.data_paths.push_back(ready
                ? "languages/hddl/instances/ok/method-ready-problem.hddl"
                : "languages/hddl/instances/upstream/empty-p.hddl");
            TranslateOptions options;
            options.language_id = "hddl";
            options.profile_id = "bmc";
            options.parse.options["plan_horizon"] = "0";
            options.parse.options["decomposition_depth"] = "1";
            if (lenient) { options.parse.options["lenient_requirements"] = "1"; }
            return translate(unit, options);
        };
        const auto strict = check(undeclared, false);
        assert(!strict.ok());
        assert(strict.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(strict.diagnostics().all()[0].message, ":htn-method-pre-eff"));
        const auto lenient = check(undeclared, true);
        assert(lenient.ok());
        assert(has(lenient.report().toJson(), "lenient-requirements"));
        const auto explicit_requirement = check(declared, false);
        assert(explicit_requirement.ok());
        // The upstream empty instance has no p and no action can establish
        // it. Its method is impossible; projection checks below need a real
        // executable method event, supplied by the ready instance instead.
        const auto impossible = check(declared, false, false);
        VERIFY(impossible.ok());
        VERIFY(has(impossible.toSmt2(), "(assert false)"));
        VERIFY(!has(impossible.toSmt2(), "do_somt-hddl-method-0@0"));
        std::string ipc = declared;
        ipc.replace(ipc.find(":htn-method-pre-eff"), std::string(":htn-method-pre-eff").size(),
                    ":method-preconditions");
        const auto ipc_requirement = check(ipc, false);
        VERIFY(ipc_requirement.ok());
        VERIFY(ipc_requirement.toSmt2() == explicit_requirement.toSmt2());
        VERIFY(!has(ipc_requirement.report().toJson(), "lenient-requirements"));
        std::string effect_only = ipc;
        effect_only.replace(effect_only.find(":precondition "), std::string(":precondition").size(),
                            ":effect");
        VERIFY(!check(effect_only, false).ok());
        // Requirements may occur after the methods they govern.
        const std::string requirements = "(:requirements :hierarchy :method-preconditions)";
        ipc.erase(ipc.find(requirements), requirements.size());
        ipc.insert(ipc.size() - 1, requirements);
        VERIFY(check(ipc, false).ok());
        assert(has(explicit_requirement.toSmt2(), "do_somt-hddl-method-0@0"));
        Diagnostics diags;
        assert(explicit_requirement.semantics().validate(diags));
        Sem::Assignment target{{"do_somt-hddl-method-0@0", "true"},
                               {"__pddl_noop@0", "false"}};
        Sem::Assignment source;
        const bool projected = explicit_requirement.semantics().project(target, source, diags);
        if (!projected) {
            for (const auto& diagnostic : diags.all()) { std::cerr << diagnostic.message << '\n'; }
        }
        assert(projected);
        assert(source.size() == 1);
        assert(source.at("method[0]") == "(method m)");
    }

    // The PDDL door still refuses HDDL instead of ignoring its hierarchy.
    {
        Lang::SourceUnit unit;
        unit.main_path = "languages/hddl/instances/ok/transport-domain.hddl";
        unit.data_paths.push_back(
            "languages/hddl/instances/ok/transport-problem.hddl");
        TranslateOptions options;
        options.language_id = "pddl";
        options.profile_id = "bmc";
        options.parse.options["plan_horizon"] = "1";
        const Translation translation = translate(unit, options);
        assert(!translation.ok());
        assert(has(translation.diagnostics().all()[0].message, ":hierarchy"));
    }

    const Lang::OpCoverage& coverage = language->coverage();
    VERIFY(coverage.supported == 2 && coverage.total == 3);
    assert(coverage.missing.size() == coverage.total - coverage.supported);

    std::cout << "All HDDL tests passed." << std::endl;
    return 0;
}
