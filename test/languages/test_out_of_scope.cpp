// SyGuS-IF and SYNTCOMP have executable adapters for deliberately small,
// semantics-preserving fragments. This test pins the refusal boundary: the
// frontends must not widen those fragments by silently dropping grammars,
// universal closure, temporal operators, or strategy semantics.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation runFile(const std::string& path, const std::string& lang = "") {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = lang;
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= synthesis adapter scope boundaries =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* sy = Lang::LanguageRegistry::instance().byId("sygus");
    Lang::Language* sc = Lang::LanguageRegistry::instance().byId("syntcomp");
    assert(sy != nullptr && sc != nullptr);

    // Coverage names both the implemented core and the unsupported remainder.
    {
        assert(sy->coverage().supported == 1 && sy->coverage().total == 2);
        assert(sc->coverage().supported == 1 && sc->coverage().total == 3);
        assert(!sy->coverage().missing.empty());
        assert(!sc->coverage().missing.empty());
        assert(!has(sy->displayName(), "pending"));
        assert(!has(sc->displayName(), "pending"));
    }

    // General LTL cannot be replaced by satisfiability of one bounded play.
    {
        const Translation t = runFile("languages/syntcomp/instances/reject/arbiter.tlsf");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        const std::string m = t.diagnostics().all()[0].message;
        assert(has(m, "LTL-to-automaton/parity-game"));
        assert(has(m, "not reactive realizability"));
    }

    // ---- A file that is not one of these is refused differently. -----------
    {
        // The refusal must be about the QUESTION, not about anything ending in
        // `.sl`. A file with no `synth-fun` is not a SyGuS instance, and saying
        // "out of scope" about it would be wrong.
        Lang::SourceUnit u;
        u.main_path = "x.sl";
        u.display_name = "x.sl";
        u.inline_source = "(set-logic LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n";
        TranslateOptions opts;
        opts.language_id = "sygus";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "not a SyGuS-IF file"));
    }
    {
        Lang::SourceUnit u;
        u.main_path = "x.tlsf";
        u.display_name = "x.tlsf";
        u.inline_source = "nothing here\n";
        TranslateOptions opts;
        opts.language_id = "syntcomp";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "not a TLSF file"));
    }

    // ---- They do not steal files from the languages that are in scope. -----
    {
        // A plain SMT-LIB script must not sniff as SyGuS: `.sl` and `.smt2` do
        // not overlap, but sniff() is consulted whenever an extension has more
        // than one claimant and a greedy one would win ties it should lose.
        assert(sy->sniff("(declare-fun x () Int)\n(assert (> x 0))\n") == 0.0);
        assert(sc->sniff("(declare-fun x () Int)\n(assert (> x 0))\n") == 0.0);
        // ...and an AIGER file is not TLSF, since SYNTCOMP has an AIGER track
        // and that track's files belong to the aiger frontend.
        assert(sc->sniff("aag 1 0 1 1 0\n2 3 0\n2\n") == 0.0);
    }
    {
        const Translation t = runFile("languages/sygus/instances/nosuch.sl", "sygus");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    std::cout << "All synthesis scope-boundary tests passed." << std::endl;
    return 0;
}
