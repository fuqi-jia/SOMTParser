// `:requirements`, and the one option that relaxes it.
//
// A PDDL/HDDL `:requirements` list is part of what a file MEANS, not a
// formality: it declares which fragment of the language the author is writing
// in, and a conforming planner is entitled to reject constructs outside it. So
// the default here is strict, and accepting an undeclared construct silently
// would make this frontend read a file no planner does.
//
// The refusal was nevertheless unmeasurable. Four of the eight pairs in HDDL's
// OWN upstream corpus -- IPC test instances, written by the format's community
// -- use `forall`, `not` and conditional effects without declaring the
// requirement that licenses them. So the corpus reported a coverage figure
// about its own conformance rather than about this frontend, and the two could
// not be told apart from the number alone.
//
// `lenient_requirements=1` is how "what would coverage be if these files were
// accepted" becomes a number: strict 2/8, lenient 6/8, and the two that still
// fail are the real gap (method `:precondition`/`:effect` needs a state-aware
// decomposition). Splitting the figure that way is the whole point -- a corpus
// exists to produce a failure-cause distribution, and "the file is
// non-conforming" and "we have not implemented it" are different causes.
//
// The relaxation is recorded as an EncodingChoice rather than left in a
// warning, because a decision written only in a diagnostic is one no
// downstream consumer can group by (D31). It is `exact()`: the relaxation
// changes which FILES are accepted, not what an accepted file means -- every
// construct admitted is one this frontend already translates exactly.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

// An IPC test instance that uses `forall` without declaring
// `:universal-preconditions`. Used from the vendored corpus rather than
// re-written here, because a hand-made copy would stop being the file the
// corpus measures the moment either changed.
const char* kDomain  = "languages/hddl/instances/upstream/conditional-test.hddl";
const char* kProblem = "languages/hddl/instances/upstream/conditional-test-problem.hddl";

Translation run(bool lenient) {
    Lang::SourceUnit unit;
    unit.main_path = kDomain;
    unit.data_paths = {kProblem};
    TranslateOptions options;
    options.language_id = "hddl";
    options.profile_id = "bmc";
    options.parse.options["plan_horizon"] = "4";
    options.parse.options["decomposition_depth"] = "2";
    if (lenient) { options.parse.options["lenient_requirements"] = "1"; }
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

} // namespace

int main() {
    std::cout << "======= PDDL/HDDL :requirements =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // Strict is the default, and it names the requirement rather than the
        // construct alone -- the author's fix is a one-line edit to
        // `:requirements`, and a message that does not say which line to add
        // sends them looking at the formula instead.
        const Translation t = run(/*lenient=*/false);
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        bool named = false;
        for (const Diagnostic& d : t.diagnostics().all()) {
            if (d.severity == Severity::ERROR && has(d.message, ":requirements")) {
                named = true;
            }
        }
        VERIFY(named);
    }

    {
        const Translation t = run(/*lenient=*/true);
        VERIFY(t.ok());

        // A warning, so the relaxation is visible in an ordinary run...
        bool warned = false;
        for (const Diagnostic& d : t.diagnostics().all()) {
            if (d.severity == Severity::WARNING
                && has(d.message, "lenient_requirements")) { warned = true; }
        }
        VERIFY(warned);

        // ...and an EncodingChoice, so it is visible to something that reads
        // the report rather than the log.
        bool recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "lenient-requirements") {
                recorded = true;
                VERIFY(c.fidelity.sound && c.fidelity.complete && c.fidelity.preserves_optimum && c.fidelity.bounds.empty() && c.fidelity.count_status == CountStatus::UNASSESSED);
                // The rationale must name WHICH requirements were assumed; a
                // choice that records only that something was relaxed cannot
                // be audited against the file.
                VERIFY(has(c.rationale, ":"));
            }
        }
        VERIFY(recorded);
    }

    {
        // The option is off unless explicitly on, and an empty value must not
        // read as its own opposite: `lenient_requirements=` is a flag someone
        // meant to set.
        Lang::SourceUnit unit;
        unit.main_path = kDomain;
        unit.data_paths = {kProblem};
        TranslateOptions options;
        options.language_id = "hddl";
        options.profile_id = "bmc";
        options.parse.options["plan_horizon"] = "4";
        options.parse.options["decomposition_depth"] = "2";
        options.parse.options["lenient_requirements"] = "";
        VERIFY(translate(unit, options).ok());

        options.parse.options["lenient_requirements"] = "0";
        VERIFY(!translate(unit, options).ok());
    }

    {
        // A CONFORMING file records no relaxation. Without this, a choice
        // emitted unconditionally would tell every reader that requirements
        // were assumed even where none were.
        Lang::SourceUnit unit;
        unit.main_path = "languages/pddl/instances/ok/gripper.pddl";
        unit.data_paths = {"languages/pddl/instances/ok/gripper.problem.pddl"};
        TranslateOptions options;
        options.profile_id = "bmc";
        options.parse.options["plan_horizon"] = "4";
        options.parse.options["lenient_requirements"] = "1";
        const Translation t = translate(unit, options);
        VERIFY(t.ok());
        for (const EncodingChoice& c : t.report().choices()) {
            VERIFY(c.strategy != "lenient-requirements");
        }
    }

    std::cout << "All PDDL/HDDL requirements tests passed.\n";
    return 0;
}
