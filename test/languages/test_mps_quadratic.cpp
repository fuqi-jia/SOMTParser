// MPS quadratic objective sections: QUADOBJ, QMATRIX, QSECTION.
//
// The objective is `c'x + 1/2 x'Qx`, and the `1/2` is carried by the FILE
// FORMAT as a notation rather than written as a division. `lp.md` §4.5 states
// the consequence of getting it wrong, and it is the reason this file exists:
// every quadratic coefficient comes out scaled by two, in a model that still
// type-checks, still solves, and answers a different question.
//
// Which makes an example test nearly worthless here -- any convention produces
// plausible-looking output. What settles it is that HiGHS's own regression set
// states ONE model four ways:
//
//   2821.mps            QUADOBJ, one triangle, deduplicated
//   2821-quadobj.mps    QUADOBJ, the same
//   2821-duplicate.mps  QUADOBJ with a repeated entry (0.5 + 1.5 = 2.0)
//   2821-summation.mps  QUADOBJ with BOTH triangles (1.0 + 1.0 = 2.0)
//   2821-qmatrix.mps    QMATRIX, the full symmetric matrix
//
// Requiring all five to emit byte-identical output pins three separate rules at
// once, and no single file could pin any of them:
//
//   * a diagonal entry contributes (v/2) x_i^2, in every section;
//   * an off-diagonal contributes v x_i x_j in QUADOBJ/QSECTION, which give one
//     triangle, and (v/2) x_i x_j in QMATRIX, which gives both -- the halves
//     add back to v;
//   * repeats SUM rather than overwrite, and the unordered pair is the key, so
//     `X1 X2` and `X2 X1` are one monomial and not two.
//
// Getting the QMATRIX halving wrong, or reading repeats as last-wins, or keying
// on the ordered pair, each breaks a DIFFERENT member of the family while
// leaving the others passing. That is what a differential instrument buys.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation runFile(const std::string& path) {
    Lang::SourceUnit unit;
    unit.main_path = "languages/mps/instances/upstream/" + path;
    unit.display_name = path;
    TranslateOptions options;
    options.language_id = "mps";
    options.profile_id = "ground";
    return translate(unit, options);
}

Translation runText(const std::string& text) {
    Lang::SourceUnit unit;
    unit.inline_source = text;
    unit.display_name = "<mps-quadratic-test>";
    TranslateOptions options;
    options.language_id = "mps";
    options.profile_id = "ground";
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

/** A minimal model whose quadratic part is one diagonal and one off-diagonal. */
std::string model(const std::string& section, const std::string& body) {
    return "NAME t\nROWS\n N obj\n L c1\nCOLUMNS\n"
           "    x1 obj 0.0\n    x1 c1 1.0\n    x2 obj 0.0\n    x2 c1 1.0\n"
           "RHS\n    rhs c1 2.0\n"
         + section + "\n" + body + "ENDATA\n";
}

} // namespace

int main() {
    std::cout << "======= MPS quadratic objective sections =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // THE differential. Five spellings, one model, one script.
        const char* family[] = {"2821.mps", "2821-quadobj.mps", "2821-duplicate.mps",
                                "2821-summation.mps", "2821-qmatrix.mps"};
        std::string reference;
        for (const char* name : family) {
            const Translation t = runFile(name);
            VERIFY(t.ok());
            const std::string smt = t.toSmt2();
            if (reference.empty()) { reference = smt; }
            else { VERIFY(smt == reference); }
        }
        // ...and it is a quadratic script, not an empty one that trivially
        // matches itself five times.
        VERIFY(has(reference, "(* X0 X0)") || has(reference, "(* X1 X0)")
               || has(reference, "(* X0 X1)"));
    }

    {
        // The same across the QSECTION spelling, which names its row in the
        // header rather than implying the objective.
        const char* family[] = {"qjh.mps", "qjh_quadobj.mps", "qjh_qmatrix.mps"};
        std::string reference;
        for (const char* name : family) {
            const Translation t = runFile(name);
            VERIFY(t.ok());
            if (reference.empty()) { reference = t.toSmt2(); }
            else { VERIFY(t.toSmt2() == reference); }
        }
    }

    {
        // The arithmetic, read off qjh.mps directly: `x1 x1 2.0` is a diagonal
        // and must halve to 1, while `x1 x3 -1.0` is an off-diagonal in a
        // one-triangle section and must NOT halve. Asserting the pair is what
        // separates "halves everything" from "halves nothing" -- both of which
        // would pass the differential above, because the differential only
        // says the spellings agree with each OTHER.
        const Translation t = runFile("qjh.mps");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(* x1 x1)"));                       // coefficient 1
        VERIFY(has(smt, "(* (- 1.0) (* x1 x3))"));             // coefficient -1
        // 0.2 halves to exactly one tenth, as a rational and not a float.
        VERIFY(has(smt, "(/ 1 10)"));
        VERIFY(!has(smt, "0.1"));
    }

    {
        // A purely quadratic objective: the row has no COLUMNS entries, so the
        // linear part is a literal 0 that must not be added into the sum.
        const Translation t = runFile("qjh_uncon.mps");
        VERIFY(t.ok());
    }

    {
        // Two quadratic sections in one file ACCUMULATE.
        //
        // This was refused until 2026-09-22, on the grounds that reading both
        // would double every coefficient and picking one would be a silent
        // choice -- true of both, and the code said in place that what HiGHS
        // does with this file was "not recorded here".
        //
        // It is now. HiGHS 1.15.1 optimises `qjh`, `qjh_quadobj` and
        // `qjh_qmatrix` -- one model stated three ways -- to -5.25, and
        // `qjh_quadobj_qmatrix` to **-2.75**. A doubled quadratic form is
        // exactly what separates those, so the reference reader sums the
        // sections; and summing is already what this reader does for a
        // repeated entry WITHIN a section (`2821-duplicate.mps`).
        //
        // Pinned on the COEFFICIENTS rather than on an optimum, because z3's
        // quadratic optimisation does not terminate quickly on this model and
        // a test that needs a solver to answer is a test that can hang. The
        // doubling is the whole content of HiGHS's two numbers.
        const Translation both = runFile("qjh_quadobj_qmatrix.mps");
        const Translation one = runFile("qjh_quadobj.mps");
        VERIFY(both.ok());
        VERIFY(one.ok());
        const std::string b = both.toSmt2();
        const std::string o = one.toSmt2();
        // Single section: x1^2 and x3^2 at 1, x1*x3 at -1, x2^2 at 1/10.
        VERIFY(has(o, "(* x1 x1)"));
        VERIFY(has(o, "(* (- 1.0) (* x1 x3))"));
        VERIFY(has(o, "(* (* x2 x2) (/ 1 10))"));
        // Both sections: every quadratic coefficient doubled...
        VERIFY(has(b, "(* 2.0 (* x1 x1))"));
        VERIFY(has(b, "(* 2.0 (* x3 x3))"));
        VERIFY(has(b, "(* (- 2.0) (* x1 x3))"));
        VERIFY(has(b, "(* (* x2 x2) (/ 1 5))"));
        // ...and the LINEAR terms untouched, which is what rules out the
        // whole objective having been scaled rather than the quadratic part
        // having been read twice.
        VERIFY(has(b, "(* x3 (- 3.0))"));
        VERIFY(has(o, "(* x3 (- 3.0))"));
        VERIFY(has(b, "(* x2 (- 1.0))"));
        VERIFY(has(o, "(* x2 (- 1.0))"));
    }

    {
        // The same monomial written both ways round is ONE monomial. Keyed on
        // the ordered pair it would be two, and the emitted objective would
        // carry `x1*x2` twice at half the coefficient each -- which sums to
        // the same number here and would NOT in a QMATRIX file, so this is
        // pinned on the shape rather than on the value.
        const Translation a = runText(model("QUADOBJ", "    x1 x2 1.0\n    x2 x1 1.0\n"));
        const Translation b = runText(model("QUADOBJ", "    x1 x2 2.0\n"));
        VERIFY(a.ok());
        VERIFY(b.ok());
        VERIFY(a.toSmt2() == b.toSmt2());
    }

    {
        // A quadratic term makes the model non-linear, and that is a LOGIC
        // change rather than a fidelity loss: QF_LRA becomes QF_NRA, a
        // different decision problem with different solver support. It belongs
        // in the report as a feature (lp.md §4.5).
        const Translation t = runFile("qjh.mps");
        VERIFY(t.ok());
        bool nonlinear = false;
        for (const auto& [name, count] : t.report().featureCounts()) {
            if (name.find("nonlinear") != std::string::npos && count > 0) {
                nonlinear = true;
            }
        }
        VERIFY(nonlinear);
        // ...and a purely linear MPS model must NOT report it, or the feature
        // says nothing about the file.
        const Translation linear = runFile("afiro.mps");
        VERIFY(linear.ok());
        for (const auto& [name, count] : linear.report().featureCounts()) {
            VERIFY(name.find("nonlinear") == std::string::npos || count == 0);
        }
    }

    {
        // An undeclared column in a quadratic section is malformed input --
        // E_PARSE, not a coverage gap.
        const Translation t = runText(model("QUADOBJ", "    x1 nope 1.0\n"));
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        VERIFY(has(firstError(t), "undeclared column"));
    }

    {
        // `QSECTION` naming a row that is not the objective is a quadratic
        // CONSTRAINT -- a different construct, refused by name rather than
        // silently added to the objective.
        const Translation t = runText(model("QSECTION      c1", "    x1 x1 2.0\n"));
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }

    std::cout << "All MPS quadratic tests passed.\n";
    return 0;
}
