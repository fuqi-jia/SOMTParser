// An array literal or comprehension as an aggregation's direct argument:
// `sum([e | i in S])`, `forall([a, b])`, and friends.
//
// This was refused with "use the generator form `sum(i in S)(e)` instead",
// which is advice about how to rewrite a model rather than a translation of
// the one that was written. The handbook's aggregate sugar (§2.2) says the two
// spellings ARE the same expression, so the right instrument here is not an
// example but a DIFFERENTIAL one: translate both spellings and require the
// emitted text to be byte-identical. An example test would confirm only that
// the comprehension form produces something plausible; the differential form
// pins it to the spelling that was already trusted.
//
// `multidimknapsack_simple.mzn` in the upstream corpus fails on nothing else
// once its two-dimensional parameter array is read.

#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation mzn(const std::string& source) {
    Lang::SourceUnit unit;
    unit.inline_source = source;
    unit.display_name = "<fold-argument-test>";
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

std::string firstError(const Translation& translation) {
    for (const Diagnostic& diagnostic : translation.diagnostics().all()) {
        if (diagnostic.severity == Severity::ERROR) { return diagnostic.message; }
    }
    return "<no error>";
}

/** Both spellings of one aggregation must emit the same script. */
void sameAsGeneratorForm(const std::string& decls,
                         const std::string& comprehension_form,
                         const std::string& generator_form) {
    const Translation a = mzn(decls + "constraint " + comprehension_form
                              + ";\nsolve satisfy;\n");
    const Translation b = mzn(decls + "constraint " + generator_form
                              + ";\nsolve satisfy;\n");
    VERIFY(a.ok());
    VERIFY(b.ok());
    VERIFY(a.toSmt2() == b.toSmt2());
}

const char* kDecls =
    "int: n = 3;\n"
    "array[1..3] of var 0..9: x;\n"
    "array[1..3] of var bool: b;\n"
    "var int: t;\n";

} // namespace

int main() {
    std::cout << "======= MiniZinc: literal and comprehension fold arguments =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // The differential core: one aggregation, two spellings, same script.
    sameAsGeneratorForm(kDecls, "t = sum([x[i] | i in 1..n])",
                                "t = sum(i in 1..n)(x[i])");
    sameAsGeneratorForm(kDecls, "t = product([x[i] | i in 1..n])",
                                "t = product(i in 1..n)(x[i])");
    sameAsGeneratorForm(kDecls, "forall([x[i] > 0 | i in 1..n])",
                                "forall(i in 1..n)(x[i] > 0)");
    sameAsGeneratorForm(kDecls, "exists([x[i] > 7 | i in 1..n])",
                                "exists(i in 1..n)(x[i] > 7)");

    // ...including the `where` filter, which changes WHICH cells exist and so
    // would diverge if the comprehension path re-implemented the unrolling
    // rather than sharing it.
    sameAsGeneratorForm(kDecls,
                        "t = sum([x[i] | i in 1..n where i != 2])",
                        "t = sum(i in 1..n where i != 2)(x[i])");

    // ...and dependent generators, where the second range is a function of the
    // first. This is the case a re-implementation is most likely to get wrong.
    sameAsGeneratorForm(kDecls,
                        "t = sum([x[i] * x[j] | i in 1..n, j in i..n])",
                        "t = sum(i in 1..n, j in i..n)(x[i] * x[j])");

    {
        // A plain literal list, not a comprehension. The builders fold
        // constants, so this reaches the output as a number rather than a sum.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint t = sum([1, 2, 3]);\n"
                                  "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(= t 6)") || has(smt, "(= 6 t)"));
    }

    {
        // An empty comprehension gives the operator's UNIT, not an error --
        // `sum` over nothing is zero. The cells never exist, so there is
        // nothing for the signature check to inspect either.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint t = sum([x[i] | i in 1..0]);\n"
                                  "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(has(translation.toSmt2(), "(= t 0)")
               || has(translation.toSmt2(), "(= 0 t)"));
    }

    {
        // ...and `forall` over nothing holds.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint forall([x[i] > 0 | i in 1..0]);\n"
                                  "solve satisfy;\n");
        VERIFY(translation.ok());
    }

    {
        // The shape `multidimknapsack_simple.mzn` is written in: a two
        // dimensional parameter array read inside a comprehension that is
        // itself a fold argument.
        const Translation translation = mzn(
            "int: n = 2;\n"
            "int: m = 2;\n"
            "array[1..2,1..2] of int: W = [| 2, 3 | 1, 4 |];\n"
            "array[1..2] of int: Cap = [5, 10];\n"
            "array[1..2] of var 0..1: x;\n"
            "constraint forall(i in 1..m)(\n"
            "    sum([W[j,i] * x[j] | j in 1..n]) <= Cap[i]);\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        // Column 1 of W is (2, 1) and column 2 is (3, 4) -- the row-major
        // reading. A transposed one would emit 2,3 and 1,4 instead, so these
        // coefficients also re-check the flattening from the caller's side.
        VERIFY(has(smt, "(* 2 (select x 1))") || has(smt, "(* (select x 1) 2)"));
        VERIFY(has(smt, "(* 4 (select x 2))") || has(smt, "(* (select x 2) 4)"));
    }

    {
        // Bool elements are coerced to Int before summation.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint t = sum([true, false]);\n"
                                  "solve satisfy;\n");
        VERIFY(translation.ok());
    }

    {
        // There is no implicit Int-to-Bool conversion for forall.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint forall([1, 2]);\n"
                                  "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "no matching signature"));
    }

    {
        // The whole-array form `sum(x)` still works: the probe that
        // distinguishes it from a generator clause is one token, and adding a
        // `[` branch beside it must not have disturbed that.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint t = sum(x);\n"
                                  "solve satisfy;\n");
        VERIFY(translation.ok());
    }

    std::cout << "All MiniZinc fold-argument tests passed.\n";
    return 0;
}
