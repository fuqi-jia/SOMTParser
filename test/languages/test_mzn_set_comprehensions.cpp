// Fixed MiniZinc sets retain holes.  A sparse value domain is exact membership,
// while an array index set still has to be contiguous because HIR arrays expose
// one contiguous source index span.

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
    unit.display_name = "<set-comprehension-test>";
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

} // namespace

int main() {
    std::cout << "======= MiniZinc: fixed set comprehensions =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // The filter removes 2, so the source domain is {1,9,16}. Bounds 1..16
        // would admit k=10 and are therefore not an exact translation.
        const Translation translation = mzn(
            "set of int: S = {i * i | i in 1..4 where i != 2};\n"
            "var S: k;\n"
            "constraint k = 10;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(= 1 k)"));
        VERIFY(has(smt, "(= 9 k)"));
        VERIFY(has(smt, "(= k 16)"));
        VERIFY(!has(smt, "(>= k 1)"));
        VERIFY(!has(smt, "(<= k 16)"));
        VERIFY(has(smt, "(= k 10)"));
        // The sparse type domain is A_Sigma in the public translation
        // contract; the user-written k=10 constraint belongs to alpha.
        VERIFY(translation.semantics().stages().front().target_axioms.size() == 1);
    }

    {
        // Union preserves disjoint pieces, and a generator enumerates every
        // member once. The equality folds to true only if {1,4,8,9} is used.
        const Translation translation = mzn(
            "set of int: S = {1, 4} union 8..9;\n"
            "constraint sum(i in S)(i) = 22;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(has(translation.toSmt2(), "(assert true)"));
    }

    {
        // Sparse named domains apply to every array cell as membership, not as
        // the bounding interval from the first to the last member.
        const Translation translation = mzn(
            "set of int: S = {1, 4, 9};\n"
            "array[1..2] of var S: a;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(select a 1)"));
        VERIFY(has(smt, "(select a 2)"));
        VERIFY(has(smt, "(= 9 (select a 1))")
               || has(smt, "(= (select a 1) 9)"));
        VERIFY(!has(smt, "(>= (select a 1) 1)"));
        VERIFY(translation.semantics().stages().front().target_axioms.size() == 2);
    }

    {
        // The same sparse set cannot be an array index space: HIR would have to
        // widen it and thereby invent source indices 2 and 3.
        const Translation translation = mzn(
            "set of int: INDEX = {1, 4};\n"
            "array[INDEX] of var int: a;\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(translation), "holes"));
        VERIFY(has(firstError(translation), "index set"));
    }

    {
        // A scalar initializer is a relational equality. Its partial body must
        // keep MiniZinc's zero-division guard in the same Boolean scope.
        const Translation translation = mzn(
            "var int: denominator;\n"
            "var int: quotient = 12 div denominator;\n"
            "constraint denominator = 0;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(distinct 0 denominator)"));
        VERIFY(has(smt, "(= quotient (div 12 denominator))")
               || has(smt, "(= (div 12 denominator) quotient)"));
    }

    std::cout << "All MiniZinc fixed-set-comprehension tests passed.\n";
    return 0;
}
