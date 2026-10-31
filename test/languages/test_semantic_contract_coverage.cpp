#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

struct Case {
    std::string language;
    std::string source_id;
    std::string path;
    std::string inline_source;
    std::string data_path;
    std::string profile = "default";
    std::string option_name;
    std::string option_value;
    std::string option_name2;
    std::string option_value2;
};

Translation run(const Case& test) {
    Lang::SourceUnit unit;
    unit.main_path = test.path;
    unit.display_name = test.path.empty() ? "<semantic-coverage>" : test.path;
    unit.inline_source = test.inline_source;
    if (!test.data_path.empty()) { unit.data_paths.push_back(test.data_path); }
    TranslateOptions options;
    options.language_id = test.language;
    options.profile_id = test.profile;
    if (!test.option_name.empty()) {
        options.parse.options[test.option_name] = test.option_value;
    }
    if (!test.option_name2.empty()) {
        options.parse.options[test.option_name2] = test.option_value2;
    }
    return translate(unit, options);
}

} // namespace

int main() {
    std::cout << "======= migrated frontend semantic-contract coverage =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    const std::vector<Case> cases = {
        {"minizinc", "minizinc", "languages/minizinc/instances/ok/trivial.mzn", ""},
        {"flatzinc", "flatzinc", "languages/flatzinc/instances/ok/domains.fzn", ""},
        {"essence", "essence-prime", "languages/essence/instances/ok/sparse.eprime", ""},
        {"xcsp3", "xcsp3", "languages/xcsp3/instances/ok/intension.xml", ""},
        {"dimacs", "dimacs", "languages/dimacs/instances/ok/simple.cnf", ""},
        {"wcnf", "wcnf", "languages/wcnf/instances/ok/new_format.wcnf", ""},
        {"opb", "opb", "languages/opb/instances/ok/spec_example.opb", ""},
        {"lp", "lp", "languages/lp/instances/ok/doc_example.lp", ""},
        {"mps", "mps", "languages/mps/instances/ok/doc_example.mps", ""},
        {"qcir", "qcir", "languages/qcir/instances/ok/gates.qcir", ""},
        {"qdimacs", "qdimacs", "languages/qdimacs/instances/ok/standard.qdimacs", ""},
        {"smtlib2", "smtlib2", "",
         "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n"},
        {"aiger", "aiger", "languages/aiger/instances/ok/toggle.aag", "", "",
         "bmc", "bmc_depth", "2"},
        {"btor2", "btor2", "languages/btor2/instances/ok/counter.btor2", "", "",
         "bmc", "bmc_depth", "2"},
        {"vmt", "vmt", "languages/vmt/instances/ok/counter.vmt", "", "",
         "bmc", "bmc_depth", "2"},
        {"moxi", "moxi", "languages/moxi/instances/ok/reachable.moxi", "", "",
         "bmc", "bmc_depth", "2"},
        {"boogie", "boogie", "languages/boogie/instances/ok/inc.bpl", ""},
        {"cryptoline", "cryptoline", "languages/cryptoline/instances/ok/mul_add.cl", ""},
        {"chc", "chc", "languages/chc/instances/ok/loop.smt2", ""},
        {"tptp", "tptp", "languages/tptp/instances/ok/socrates.p", ""},
        {"pddl", "pddl", "languages/pddl/instances/ok/gripper.pddl", "",
         "languages/pddl/instances/ok/gripper.problem.pddl", "bmc",
         "plan_horizon", "1"},
        {"hddl", "hddl",
         "languages/hddl/instances/ok/transport-domain.hddl", "",
         "languages/hddl/instances/ok/transport-problem.hddl", "bmc",
         "plan_horizon", "1", "decomposition_depth", "1"},
        {"sygus", "sygus", "languages/sygus/instances/ok/max2.sl", "", "",
         "bmc", "grammar_depth", "2"},
        {"syntcomp", "syntcomp",
         "languages/syntcomp/instances/ok/mealy-copy.tlsf", ""},
    };

    for (const Case& test : cases) {
        std::cout << "checking " << test.language << "\n";
        const Translation translation = run(test);
        if (!translation.ok()) {
            for (const auto& diagnostic : translation.diagnostics().all()) {
                std::cerr << diagnostic.message << "\n";
            }
        }
        VERIFY(translation.ok());
        const auto& stages = translation.semantics().stages();
        VERIFY(stages.size() == 2);
        VERIFY(stages[0].source.id == test.source_id);
        VERIFY(stages[0].target.id == "typed-relational-core");
        VERIFY(stages[1].source.id == "typed-relational-core");
        VERIFY(stages[1].target.id == "smt-lib" || stages[1].target.id == "omt");
        Diagnostics diagnostics;
        VERIFY(translation.semantics().validate(diagnostics));
        VERIFY(!diagnostics.hasErrors());

        int recorded = 0;
        for (const EncodingChoice& choice : translation.report().choices()) {
            if (choice.unified_op == "semantic-translation-stage") { ++recorded; }
        }
        VERIFY(recorded == 2);
    }

    // WCNF's objective lives in soft constraints rather than model.objectives.
    // Its target must still be OMT and its source order must be minimization.
    const Translation maxsat = run(cases[5]);
    VERIFY(maxsat.semantics().stages()[0].objectives.source
           == Sem::ObjectiveOrder::MINIMIZE);
    VERIFY(maxsat.semantics().stages()[0].objectives.source_directions.size() == 1);
    VERIFY(maxsat.semantics().stages()[1].target.id == "omt");

    const Translation safety = run(cases[12]);
    VERIFY(safety.semantics().stages()[0].decision.source
           == Sem::DecisionKind::SAFETY);
    VERIFY(!safety.semantics().targetSatMeansSourceYes());
    VERIFY(!safety.semantics().fidelity().complete);

    const Translation horn = run(cases[18]);
    VERIFY(horn.semantics().stages()[0].decision.source
           == Sem::DecisionKind::HORN_SATISFIABILITY);
    VERIFY(horn.semantics().targetSatMeansSourceYes());

    const Translation theorem = run(cases[19]);
    VERIFY(theorem.semantics().stages()[0].decision.source
           == Sem::DecisionKind::VALIDITY);
    VERIFY(!theorem.semantics().targetSatMeansSourceYes());

    std::cout << "All migrated frontend semantic contracts passed.\n";
    return 0;
}
