// Finite MiniZinc array comprehensions are elaborated into an ordered vector of
// relational expressions.  These tests pin the source order, inferred index
// set, row-major mapping, empty-set identity, and propagation of undefinedness.

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
    unit.display_name = "<array-comprehension-test>";
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

std::size_t occurrences(const std::string& text, const std::string& fragment) {
    std::size_t count = 0;
    for (std::size_t pos = text.find(fragment); pos != std::string::npos;
         pos = text.find(fragment, pos + fragment.size())) {
        ++count;
    }
    return count;
}

} // namespace

int main() {
    std::cout << "======= MiniZinc: array comprehensions =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // The inner range depends on the outer binding.  Source order is
        // (1,2), (1,3), (2,3), and array[int] therefore means 1..3.
        const Translation translation = mzn(
            "int: m = 3;\n"
            "array[1..m] of var int: mark;\n"
            "array[int] of var int: differences =\n"
            "  [mark[j] - mark[i] | i in 1..m-1, j in i+1..m];\n"
            "constraint differences[3] = mark[3] - mark[2];\n"
            "solve satisfy;\n");
        if (!translation.ok()) {
            std::cout << "  refused dependent generators: "
                      << firstError(translation) << "\n";
            VERIFY(false);
        }
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(select differences 1)"));
        VERIFY(has(smt, "(select differences 3)"));
        VERIFY(!has(smt, "(select differences 4)"));
        // Three initializer equalities plus the source constraint read the
        // inferred array exactly four times.
        VERIFY(occurrences(smt, "(select differences ") == 4);
    }

    {
        // A multi-dimensional source array is already flattened row-major.
        // The comprehension must enumerate the same source order when filling
        // the explicitly indexed one-dimensional result.
        const Translation translation = mzn(
            "array[1..2, 1..2] of var int: matrix;\n"
            "array[5..8] of var int: flat =\n"
            "  array1d(5..8, [matrix[row, column] | row in 1..2, column in 1..2]);\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(select flat 5)"));
        VERIFY(has(smt, "(select flat 8)"));
        VERIFY(has(smt, "(select matrix 0)"));
        VERIFY(has(smt, "(select matrix 3)"));
    }

    {
        // Filtering changes the inferred index set to 1..2, independent of
        // the generator's original four-element source.
        const Translation translation = mzn(
            "array[int] of var int: even =\n"
            "  [i | i in 1..4 where i mod 2 = 0];\n"
            "constraint even[2] = 4;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(select even 1)"));
        VERIFY(has(smt, "(select even 2)"));
        VERIFY(!has(smt, "(select even 3)"));
    }

    {
        // An empty comprehension has MiniZinc's 1..0 index set.  It is a real
        // initializer, but produces no equality and no select.
        const Translation translation = mzn(
            "array[int] of var int: empty = [i | i in 1..0];\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(!has(translation.toSmt2(), "(select empty "));
    }

    {
        // Explicit index sets do not resize to fit an initializer.  Accepting
        // this would silently change either the declaration or the value.
        const Translation translation = mzn(
            "array[1..2] of var int: wrong = [1];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "indexes differ"));
    }

    {
        // Initializer equality is a relational Boolean scope.  MiniZinc's
        // undefined 10 div 0 must make it false; SMT's total div-by-zero value
        // must not be allowed to satisfy the equality accidentally.
        const Translation translation = mzn(
            "var int: denominator;\n"
            "array[1..1] of var int: quotient = [10 div denominator];\n"
            "constraint denominator = 0;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(distinct 0 denominator)"));
        VERIFY(has(smt, "(select quotient 1)"));
    }

    std::cout << "All MiniZinc array-comprehension tests passed.\n";
    return 0;
}
