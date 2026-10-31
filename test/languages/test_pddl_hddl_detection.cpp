// Which frontend owns a `.pddl` file.
//
// PDDL and HDDL both claim the `.pddl` extension, so `LanguageRegistry::detect`
// falls through to `sniff()` -- and PDDL did not override it. Both frontends
// therefore scored the base 0.0, detect kept its FIRST candidate, and HDDL is
// registered first. So registration order decided, and a plain PDDL domain was
// handed to the HDDL parser, which refused it with "HDDL requires hierarchy
// declarations ... plain PDDL belongs to --from pddl".
//
// That message is correct and the situation it describes should never arise:
// the CLI is not where a user learns which of two registered frontends owns an
// extension. Every PDDL fixture and every vendored PDDL instance needed an
// explicit `--from pddl`, which is why the corpus read 0 of 6.
//
// The scores are ORDERED rather than mutually exclusive, because the two
// languages are not symmetric: HDDL is PDDL plus a task hierarchy, so a
// hierarchy marker means HDDL and nothing else, while everything a plain PDDL
// file contains an HDDL file contains too. PDDL answers "this is a PDDL-family
// file" (0.5) and HDDL answers "this is specifically HDDL" (0.95). Both
// directions are pinned below, because a detector that claims too little is
// exactly as wrong as one that claims too much -- and only testing the
// direction that was broken would leave the other free to break silently.

#include "somtparser/translation/translate.h"
#include "somtparser/translation/language.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

/** Detection only -- no parse, so the test says nothing about coverage. */
std::string detectedId(const std::string& source, const std::string& path) {
    Lang::SourceUnit unit;
    unit.main_path = path;
    unit.display_name = path;
    unit.inline_source = source;
    const Lang::Language* lang =
        Lang::LanguageRegistry::instance().detect(unit);
    return lang == nullptr ? "<none>" : lang->id();
}

// A plain classical domain: no `:method`, no `(:task `, no `:htn`.
const char* kPlainPddl =
    "(define (domain gripper)\n"
    "  (:requirements :strips :typing)\n"
    "  (:types room ball gripper)\n"
    "  (:predicates (at-robby ?r - room) (free ?g - gripper))\n"
    "  (:action move\n"
    "    :parameters (?from ?to - room)\n"
    "    :precondition (at-robby ?from)\n"
    "    :effect (and (at-robby ?to) (not (at-robby ?from)))))\n";

// The same file plus a hierarchy. This is what makes it HDDL.
const char* kHddlDomain =
    "(define (domain transport)\n"
    "  (:requirements :strips :typing :hierarchy)\n"
    "  (:types location package)\n"
    "  (:predicates (at ?p - package ?l - location))\n"
    "  (:task deliver :parameters (?p - package ?l - location))\n"
    "  (:method m-deliver\n"
    "    :parameters (?p - package ?l - location)\n"
    "    :task (deliver ?p ?l)\n"
    "    :ordered-subtasks (and (drop ?p ?l)))\n"
    "  (:action drop\n"
    "    :parameters (?p - package ?l - location)\n"
    "    :precondition ()\n"
    "    :effect (at ?p ?l)))\n";

} // namespace

int main() {
    std::cout << "======= PDDL / HDDL detection =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // The direction that was broken: a plain domain must reach PDDL.
    VERIFY(detectedId(kPlainPddl, "gripper.pddl") == "pddl");

    // The direction that must not break while fixing it. A hierarchy marker
    // means HDDL even though the file is PDDL-shaped in every other respect,
    // and it wins under BOTH extensions -- `.pddl` is the ambiguous one, and
    // an HDDL model written with it is ordinary.
    VERIFY(detectedId(kHddlDomain, "transport.pddl") == "hddl");
    VERIFY(detectedId(kHddlDomain, "transport.hddl") == "hddl");

    // `.hddl` has a single claimant, so it never reaches sniff() at all. Pinned
    // so a future extension list cannot quietly make it ambiguous.
    VERIFY(detectedId(kPlainPddl, "odd.hddl") == "hddl");

    {
        // Each of HDDL's three markers on its own is enough. Listing them
        // individually is what stops the score ordering from being mistaken for
        // a test of the marker LIST: if a marker is dropped from hddl.cpp, the
        // file silently becomes PDDL's, and PDDL will parse a hierarchy it
        // cannot represent rather than refuse it.
        const char* markers[] = {"  (:method m :task (t))\n",
                                 "  (:task t :parameters ())\n",
                                 "  (:htn :subtasks (and (t)))\n"};
        for (const char* marker : markers) {
            const std::string source =
                "(define (domain d)\n  (:requirements :strips)\n"
                + std::string(marker) + ")\n";
            VERIFY(detectedId(source, "d.pddl") == "hddl");
        }
    }

    {
        // A file that is neither: no `(define`, so PDDL scores 0.0 and HDDL
        // scores 0.0. detect() still has to return SOMETHING for a `.pddl`
        // path, and which one is arbitrary -- what matters is that it does not
        // crash and does not return null, since the extension was claimed.
        const std::string id = detectedId("; just a comment\n", "empty.pddl");
        VERIFY(id == "pddl" || id == "hddl");
    }

    // End to end: the fixture that needed `--from pddl` translates without one.
    {
        Lang::SourceUnit unit;
        unit.main_path = "languages/pddl/instances/ok/gripper.pddl";
        unit.data_paths = {"languages/pddl/instances/ok/gripper.problem.pddl"};
        TranslateOptions options;
        options.profile_id = "bmc";
        options.parse.options["plan_horizon"] = "6";
        const Translation t = translate(unit, options);
        VERIFY(t.ok());
    }

    std::cout << "All PDDL/HDDL detection tests passed.\n";
    return 0;
}
