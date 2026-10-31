// Cluster A decomposes its globals in the PASS, not in four frontends.
//
// `docs/languages-scoping.md` §3.1 makes MiniZinc, FlatZinc, XCSP3 and Essence'
// one cluster for one reason: the global-constraint decomposition library is
// written once and shared. Until 2026-08-17 it was written once and used by
// MiniZinc. The other three each expanded `allDifferent` pairwise inside the
// frontend, with three consequences and not one of them visible in the output:
//
//   * `--profile quantified` was accepted and silently produced the ground
//     encoding, so the ground/quantified axis -- the project's central
//     experimental parameter -- was variable for one language in four.
//   * No `EncodingChoice` was recorded, so a report could not distinguish
//     "this language is insensitive to the parameter" from "this language never
//     asked the question".
//   * The encoding decision lived in three places, which is the thing
//     `HirToParser makes no decisions` exists to prevent, one level up.
//
// It was also WHY a defect in the shared pipeline stayed hidden: `default` had
// an empty pipeline and refused every model containing a global constraint, and
// only one language could reach the pipeline to notice.
//
// The two shapes are not interchangeable and this file pins which is which.
// `alldifferent(array, lo, hi)` is the indexed shape, and it is the only one
// where the styles differ -- the quantified encoding needs an index set to bind
// over. `alldifferent(t1, ..., tn)` is the list shape and uses native distinct under
// both styles, deliberately, because a list of terms has no index set. A
// frontend that flattens its variable vector to scalars can therefore be routed
// through the pass and still not vary the axis, and saying which frontends are
// in that position is the honest form of the coverage claim.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation runFile(const std::string& lang, const std::string& path,
                    const std::string& profile, const std::string& data = "") {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    if (!data.empty()) { u.data_paths.push_back(data); }
    TranslateOptions opts;
    opts.language_id = lang;
    opts.profile_id = profile;
    return translate(u, opts);
}

Translation runSrc(const std::string& lang, const std::string& src,
                   const std::string& profile) {
    Lang::SourceUnit u;
    u.inline_source = src;
    u.display_name = "<test>";
    TranslateOptions opts;
    opts.language_id = lang;
    opts.profile_id = profile;
    return translate(u, opts);
}

/** Did the translation record a decomposition decision at all? */
bool recorded(const Translation& t) {
    for (const EncodingChoice& c : t.report().choices()) {
        if (c.unified_op == "alldifferent") { return true; }
    }
    return false;
}

} // namespace

int main() {
    std::cout << "======= cluster A: globals are decomposed by the pass =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- Every cluster-A language records the decision. ---------------------
    //
    // The claim is per LANGUAGE and it is what "one cluster" means. A frontend
    // that expands the constraint itself still translates, still emits correct
    // SMT-LIB, and reports nothing -- so `t.ok()` cannot catch a regression
    // here and the report is the only place that can.
    {
        const Translation t = runSrc(
            "minizinc",
            "array[1..3] of var int: a;\nconstraint alldifferent(a);\nsolve satisfy;\n",
            "ground");
        VERIFY(t.ok());
        VERIFY(recorded(t));
    }
    {
        const Translation t = runFile("xcsp3",
                                      "languages/xcsp3/instances/ok/alldifferent.xml",
                                      "ground");
        if (!t.ok()) {
            std::cout << "  xcsp3 refused: "
                      << t.diagnostics().all().front().message << "\n";
            VERIFY(false);
        }
        VERIFY(recorded(t));
    }
    {
        const Translation t = runSrc(
            "flatzinc",
            "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n"
            "constraint all_different_int([x, y, z]);\nsolve satisfy;\n",
            "ground");
        if (!t.ok()) {
            std::cout << "  flatzinc refused: "
                      << t.diagnostics().all().front().message << "\n";
            VERIFY(false);
        }
        VERIFY(recorded(t));
    }
    {
        const Translation t = runFile("essence",
                                      "languages/essence/instances/ok/queens.eprime",
                                      "ground",
                                      "languages/essence/instances/ok/queens.param");
        VERIFY(t.ok());
        VERIFY(recorded(t));
    }

    // ---- The indexed shape varies with the style; the list shape does not. --
    {
        // MiniZinc and Essence' declare a real HIR array, so both reach the
        // indexed shape and both must respond to the profile.
        const char* kMzn =
            "array[1..3] of var int: a;\nconstraint alldifferent(a);\nsolve satisfy;\n";
        const Translation g = runSrc("minizinc", kMzn, "ground");
        const Translation q = runSrc("minizinc", kMzn, "quantified");
        VERIFY(g.ok() && q.ok());
        VERIFY(!has(g.toSmt2(), "forall"));
        VERIFY(has(q.toSmt2(), "forall"));
    }
    {
        const Translation g = runFile("essence",
                                      "languages/essence/instances/ok/queens.eprime",
                                      "ground",
                                      "languages/essence/instances/ok/queens.param");
        const Translation q = runFile("essence",
                                      "languages/essence/instances/ok/queens.eprime",
                                      "quantified",
                                      "languages/essence/instances/ok/queens.param");
        VERIFY(g.ok() && q.ok());
        VERIFY(!has(g.toSmt2(), "forall"));
        VERIFY(has(q.toSmt2(), "forall"));
    }
    {
        // XCSP3 and FlatZinc flatten their variable vectors to scalars, so they
        // reach only the list shape -- native distinct under both styles. This
        // assertion is NOT a wish that they behaved otherwise; it pins the
        // honest statement of the limit, so that "the axis is variable for
        // cluster A" is never claimed more broadly than it holds. Making these
        // two vary needs them to declare HIR arrays, which changes every
        // variable reference they emit.
        const Translation g = runFile("xcsp3",
                                      "languages/xcsp3/instances/ok/alldifferent.xml",
                                      "ground");
        const Translation q = runFile("xcsp3",
                                      "languages/xcsp3/instances/ok/alldifferent.xml",
                                      "quantified");
        VERIFY(g.ok() && q.ok());
        VERIFY(g.toSmt2() == q.toSmt2());
        // ...and both use native distinct, as the list shape promises.
        VERIFY(has(g.toSmt2(), "distinct"));
        VERIFY(!has(g.toSmt2(), "forall"));
    }

    // ---- No frontend may quietly go back to expanding it itself. ------------
    {
        // The regression this file most needs to catch does not fail anything:
        // a frontend that expands `allDifferent` in place still translates and
        // still emits correct SMT-LIB. What it stops doing is recording, and
        // what it stops being is variable. Asserting BOTH per language is the
        // only way to see it, so the two loops above are the test -- this case
        // just states the invariant for the next reader.
        //
        // Essence' must still reach the shared indexed global, so the
        // quantified profile remains observable at this language boundary.
        const Translation t = runFile("essence",
                                      "languages/essence/instances/ok/queens.eprime",
                                      "quantified",
                                      "languages/essence/instances/ok/queens.param");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "forall"));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(t.toSmt2()));
    }

    std::cout << "All cluster-A global tests passed." << std::endl;
    return 0;
}
