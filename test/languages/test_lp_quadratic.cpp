// LP quadratic expressions, and the cross-format oracle that settles them.
//
// CPLEX LP writes a quadratic form in brackets with an OPTIONAL divisor:
//
//     Minimize  - x2 - 3 x3 + [ 2 x1^2 - 2 x1*x3 + 0.2 x2^2 + 2 x3^2 ] / 2
//     c1: 10 x1 + [ x0 * x1 ] <= 10
//
// The `/ 2` is conventional in an OBJECTIVE and absent from a CONSTRAINT, and
// `qcqp.lp` carries both in one file. So the divisor is read from the text
// rather than assumed from the position -- which is exactly where LP differs
// from MPS, where the 1/2 is part of the format and never written (`mps.md`
// §4.7). Assuming it would halve every quadratic constraint coefficient;
// ignoring it would double every objective one. Both produce a model that
// still type-checks and still solves.
//
// HiGHS ships `qjh` as BOTH `qjh.lp` and `qjh.mps` -- one model, two formats,
// two independent frontends, and two completely different ways of stating the
// quadratic part (an explicit `/2` over written coefficients, against an
// implicit 1/2 over a triangle of a matrix). Requiring the two to emit the
// SAME objective is the strongest instrument available here: it cannot be
// satisfied by a consistent misreading, because the two readings have almost
// nothing in common. `x1 x3 -1.0` in the MPS triangle and `- 2 x1*x3` over two
// in the LP bracket arrive at the same `-1` by different routes.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation runFile(const std::string& path, const std::string& language) {
    Lang::SourceUnit unit;
    unit.main_path = path;
    unit.display_name = path;
    TranslateOptions options;
    options.language_id = language;
    options.profile_id = "ground";
    options.omt_dialect = Lower::OmtDialect::Z3;
    return translate(unit, options);
}

Translation runText(const std::string& text) {
    Lang::SourceUnit unit;
    unit.inline_source = text;
    unit.display_name = "<lp-quadratic-test>";
    TranslateOptions options;
    options.language_id = "lp";
    options.profile_id = "ground";
    options.omt_dialect = Lower::OmtDialect::Z3;
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

/** The `(minimize ...)` / `(maximize ...)` line alone. */
std::string objectiveLine(const std::string& smt) {
    for (const char* head : {"(minimize ", "(maximize "}) {
        const std::size_t at = smt.find(head);
        if (at == std::string::npos) { continue; }
        return smt.substr(at, smt.find('\n', at) - at);
    }
    return "<no objective>";
}

} // namespace

int main() {
    std::cout << "======= LP quadratic expressions =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // THE cross-format oracle. Same model, two formats, one objective.
        const Translation lp =
            runFile("languages/lp/instances/upstream/qjh.lp", "lp");
        const Translation mps =
            runFile("languages/mps/instances/upstream/qjh.mps", "mps");
        VERIFY(lp.ok());
        VERIFY(mps.ok());
        const std::string a = objectiveLine(lp.toSmt2());
        const std::string b = objectiveLine(mps.toSmt2());
        VERIFY(a == b);
        // ...and it is the quadratic objective, not two empty lines matching.
        VERIFY(has(a, "(* x1 x1)"));
        VERIFY(has(a, "(* (- 1.0) (* x1 x3))"));
        VERIFY(has(a, "(/ 1 10)"));
    }

    {
        // The unconstrained twin, which also exists in both formats.
        const Translation lp =
            runFile("languages/lp/instances/upstream/qjh_uncon.lp", "lp");
        const Translation mps =
            runFile("languages/mps/instances/upstream/qjh_uncon.mps", "mps");
        VERIFY(lp.ok());
        VERIFY(mps.ok());
        VERIFY(objectiveLine(lp.toSmt2()) == objectiveLine(mps.toSmt2()));
    }

    {
        // The divisor is READ, not assumed. Same bracket, with and without
        // `/ 2`, must differ by exactly a factor of two -- this is the pair
        // that separates "always halve" and "never halve" from "read it".
        const Translation halved = runText(
            "Minimize\n obj: [ 4 x ^ 2 ] / 2\nSubject To\n c1: x >= 1\nEnd\n");
        const Translation plain = runText(
            "Minimize\n obj: [ 4 x ^ 2 ]\nSubject To\n c1: x >= 1\nEnd\n");
        VERIFY(halved.ok());
        VERIFY(plain.ok());
        VERIFY(has(objectiveLine(halved.toSmt2()), "(* 2.0 (* x x))"));
        VERIFY(has(objectiveLine(plain.toSmt2()), "(* 4.0 (* x x))"));
    }

    {
        // `x ^ 2` and `x * x` are the same monomial, spelled two ways --
        // `qptestnw.lp` uses the second for a square.
        const Translation power = runText(
            "Minimize\n obj: [ 2 x ^ 2 ] / 2\nSubject To\n c1: x >= 1\nEnd\n");
        const Translation product = runText(
            "Minimize\n obj: [ 2 x * x ] / 2\nSubject To\n c1: x >= 1\nEnd\n");
        VERIFY(power.ok());
        VERIFY(product.ok());
        VERIFY(objectiveLine(power.toSmt2()) == objectiveLine(product.toSmt2()));
    }

    {
        // A quadratic CONSTRAINT, which carries no divisor. `qcqp.lp` has one
        // of each, so a reader that assumed the `/2` from the position rather
        // than the text would halve this.
        const Translation t =
            runFile("languages/lp/instances/upstream/qcqp.lp", "lp");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(* x0 x1)"));
        VERIFY(has(t.toSmt2(), "(<= (+ (* x1 10.0) (* x0 x1)) 10.0)"));
    }

    {
        // Division stays EXACT and reduced: 0.2/2 is one tenth, as a rational.
        const Translation t = runText(
            "Minimize\n obj: [ 0.2 x ^ 2 ] / 2\nSubject To\n c1: x >= 1\nEnd\n");
        VERIFY(t.ok());
        VERIFY(has(objectiveLine(t.toSmt2()), "(/ 1 10)"));
        VERIFY(!has(objectiveLine(t.toSmt2()), "0.1"));
        // ...and a non-terminating divisor is a rational rather than a
        // rounded decimal, which is the reason the quotient is not a decimal.
        const Translation third = runText(
            "Minimize\n obj: [ 1 x ^ 2 ] / 3\nSubject To\n c1: x >= 1\nEnd\n");
        VERIFY(third.ok());
        VERIFY(has(objectiveLine(third.toSmt2()), "(/ 1 3)"));
    }

    {
        // A quadratic term makes the model non-linear: QF_LRA becomes QF_NRA,
        // a different decision problem (§4.5). Recorded as a feature.
        const Translation t =
            runFile("languages/lp/instances/upstream/qjh.lp", "lp");
        VERIFY(t.ok());
        bool nonlinear = false;
        for (const auto& [name, count] : t.report().featureCounts()) {
            if (name.find("nonlinear") != std::string::npos && count > 0) {
                nonlinear = true;
            }
        }
        VERIFY(nonlinear);
    }

    {
        // A linear term inside the brackets is refused by name. The brackets
        // are what tell a reader the section is quadratic, so a linear term
        // in them is likelier a typo than an intention -- and silently reading
        // it as a term outside would apply the divisor to it.
        const Translation t = runText(
            "Minimize\n obj: [ 2 x ^ 2 + 3 y ] / 2\nSubject To\n c1: x >= 1\nEnd\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(t), "linear term"));
    }

    {
        // Degree above two is refused by name rather than truncated.
        const Translation t = runText(
            "Minimize\n obj: [ 2 x ^ 3 ] / 2\nSubject To\n c1: x >= 1\nEnd\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(t), "^3"));
    }

    {
        // An unterminated bracket is malformed input -- E_PARSE.
        const Translation t = runText(
            "Minimize\n obj: [ 2 x ^ 2 / 2\nSubject To\n c1: x >= 1\nEnd\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    {
        // Indicator constraints are still refused, and by their own name now
        // that the message no longer bundles them with quadratics.
        const Translation t = runText(
            "Minimize\n obj: x\nSubject To\n c1: b = 1 -> x >= 1\nEnd\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }

    std::cout << "All LP quadratic tests passed.\n";
    return 0;
}
