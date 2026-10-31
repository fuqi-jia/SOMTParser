// The Model Counting Competition's headers, which DIMACS used to discard.
//
// `dimacs.cpp` read `if (first == "c") { continue; }` -- every comment line
// dropped. MCC writes its weights and projection scope in exactly those lines:
//
//     c t wmc                  the track
//     c p weight 1 0.3 0       literal 1 has weight 0.3
//     c p show 1 2 3 0         count projected onto these variables
//
// So a weighted instance translated as an unweighted one, silently, which is
// invariant 9 violated in the most visible possible place. The file is still
// a plain CNF and still translates the same way; what changes is that the data
// is now READ and recorded rather than thrown away.
//
// An MC-track instance has no headers at all and is byte-identical to a SAT
// instance. That is why there is no `languages/mcc`: the difference is not in
// the file but in what the caller asks.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& text) {
    Lang::SourceUnit unit;
    unit.inline_source = text;
    unit.display_name = "<dimacs-counting-test>";
    TranslateOptions options;
    options.language_id = "dimacs";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    return "<no error>";
}

bool hasWarningContaining(const Translation& t, const std::string& fragment) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::WARNING && has(d.message, fragment)) { return true; }
    }
    return false;
}

bool anyWarning(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::WARNING) { return true; }
    }
    return false;
}

const char* kPlain = "p cnf 2 1\n1 2 0\n";

} // namespace

int main() {
    std::cout << "======= DIMACS: model-counting headers =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // An MC instance is a plain CNF and must keep translating exactly as
        // before. This is the regression guard for the whole task.
        const Translation t = run(kPlain);
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(or"));
    }

    {
        // An ordinary comment is still a comment.
        const Translation t = run("c this is prose\np cnf 2 1\n1 2 0\n");
        VERIFY(t.ok());
    }

    {
        // Weights are read and recorded rather than dropped. The track (wmc)
        // and the directives present (a weight, no scope) agree, so this is
        // also the "consistent input raises nothing" half of the track check
        // below -- without it, a check that always warns would still pass
        // every other assertion in this file.
        const Translation t = run("c t wmc\np cnf 2 1\nc p weight 1 0.3 0\n"
                                  "c p weight -1 0.7 0\n1 2 0\n");
        VERIFY(t.ok());
        bool recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "counting-weights") {
                recorded = true;
                VERIFY(has(c.rationale, "0.3"));
            }
        }
        VERIFY(recorded);
        VERIFY(!anyWarning(t));
    }

    {
        // The projection scope likewise; track (pmc) and directives (a scope,
        // no weight) agree.
        const Translation t = run("c t pmc\np cnf 3 1\nc p show 1 2 0\n1 2 3 0\n");
        VERIFY(t.ok());
        bool recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "counting-projection") { recorded = true; }
        }
        VERIFY(recorded);
        VERIFY(!anyWarning(t));
    }

    {
        // `c t wmc` promises weights; none are present. The formula still
        // translates -- the mismatch is a warning about the label, not a
        // defect in the instance.
        const Translation t = run("c t wmc\np cnf 2 1\n1 2 0\n");
        VERIFY(t.ok());
        VERIFY(hasWarningContaining(t, "wmc"));
        VERIFY(hasWarningContaining(t, "weight"));
    }

    {
        // `c t mc` promises an unweighted count; a weight line is present
        // anyway.
        const Translation t = run("c t mc\np cnf 2 1\nc p weight 1 0.3 0\n1 2 0\n");
        VERIFY(t.ok());
        VERIFY(hasWarningContaining(t, "mc"));
        VERIFY(hasWarningContaining(t, "weight"));
    }

    {
        // A track name this reader does not recognise is named in the
        // warning, not silently accepted or refused.
        const Translation t = run("c t frobnicate\np cnf 2 1\n1 2 0\n");
        VERIFY(t.ok());
        VERIFY(hasWarningContaining(t, "frobnicate"));
    }

    {
        // An unrecognised `c p` directive is refused BY NAME. Silently
        // ignoring it is how the weights were lost in the first place, and a
        // directive this reader does not know may change what is being asked.
        const Translation t = run("p cnf 2 1\nc p frobnicate 7 0\n1 2 0\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(t), "frobnicate"));
    }

    {
        // A malformed weight is malformed INPUT -- E_PARSE, not a coverage gap.
        const Translation t = run("p cnf 2 1\nc p weight 1 notanumber 0\n1 2 0\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    {
        // The grammar of a `c p` line does not end at its last useful field.
        // Reading the first three and stopping is the same shortcut that lost
        // the weights in the first place, so each of these is a refusal.
        // Each pins its BUCKET as well as its refusal. `E_PARSE` against
        // `E_UNSUPPORTED_CONSTRUCT` is the difference between "this file is
        // malformed" and "this reader is incomplete", and those two feed
        // different statistics -- so a test that checks only `!ok()` leaves
        // the thing most likely to be wrong unpinned. Three of the four gaps
        // found in this frontend to date were wrong error codes, not wrong
        // answers.
        const Translation missing_zero = run("p cnf 2 1\nc p weight 1 0.3\n1 2 0\n");
        VERIFY(!missing_zero.ok());
        VERIFY(missing_zero.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);

        const Translation trailing = run("p cnf 2 1\nc p weight 1 0.3 0 9\n1 2 0\n");
        VERIFY(!trailing.ok());
        VERIFY(trailing.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);

        // `>>` into a long long fails on `x` and leaves the stream bad, so the
        // old loop simply ENDED here -- keeping {1, 2}, dropping the bad token
        // and never noticing the missing terminator.
        const Translation bad_token = run("p cnf 3 1\nc p show 1 2 x 0\n1 2 3 0\n");
        VERIFY(!bad_token.ok());
        VERIFY(bad_token.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);

        const Translation show_unterminated = run("p cnf 3 1\nc p show 1 2\n1 2 3 0\n");
        VERIFY(!show_unterminated.ok());
        VERIFY(show_unterminated.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);

        const Translation show_trailing = run("p cnf 3 1\nc p show 1 2 0 9\n1 2 3 0\n");
        VERIFY(!show_trailing.ok());
        VERIFY(show_trailing.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);

        // A weight is a term of a sum over satisfying assignments. A negative
        // one makes that sum something other than a count, so it is refused
        // rather than carried -- which the helper's own docstring already
        // claimed and its code did not enforce.
        const Translation negative = run("p cnf 2 1\nc p weight 1 -0.3 0\n1 2 0\n");
        VERIFY(!negative.ok());
        VERIFY(negative.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);

        // ...and the forms that are still good stay good.
        const Translation plus = run("p cnf 2 1\nc p weight 1 +0.3 0\n1 2 0\n");
        VERIFY(plus.ok());
    }

    {
        // A comment is a line whose FIRST CHARACTER is `c`. The space after it
        // is conventional, not required, and the MaxSAT Evaluation's own
        // standardised instances open with `c{` and continue `c "sha1sum": …`
        // -- a JSON block written one line at a time. Comparing the first
        // whitespace-delimited TOKEN to "c" refused all of them, reporting a
        // well-formed file as malformed input. Found by vendoring a corpus:
        // 10 of 25 files, which no hand-written fixture had covered.
        const Translation t = run("c{\nc \"nvars\": 2\nc}\np cnf 2 1\n1 2 0\n");
        VERIFY(t.ok());

        // ...and the exact token `c` still introduces a directive, because
        // `c p` and `c t` are defined with the separator. `cp` is prose.
        const Translation directive = run("c t mc\np cnf 2 1\n1 2 0\n");
        VERIFY(directive.ok());
        const Translation prose = run("cp weight 1 0.5 0\np cnf 2 1\n1 2 0\n");
        VERIFY(prose.ok());
        // Read as prose, not as a directive. Asserted as "no COUNTING choice"
        // rather than "no choices at all": every translation records two
        // semantic-stage choices, so the blanket form asserts something that
        // is never true and fails for a reason unrelated to what it is testing.
        for (const Uir::EncodingChoice& c : prose.report().choices()) {
            VERIFY(c.strategy != "counting-weights");
            VERIFY(c.strategy != "counting-projection");
        }
    }

    std::cout << "All DIMACS counting-header tests passed.\n";
    return 0;
}
