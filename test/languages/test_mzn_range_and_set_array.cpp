#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {
Translation run(const std::string& source) {
    Lang::SourceUnit unit;
    unit.display_name = "range-set-array-review.mzn";
    unit.main_path = unit.display_name;
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

bool has(const std::string& source, const std::string& fragment) {
    return source.find(fragment) != std::string::npos;
}
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // Variable endpoints are range expressions even though the left endpoint
    // is a numeric literal. Parentheses around the range do not change meaning.
    const std::string dynamic_source =
        "var 0..5: x; var 0..5: hi;\n"
        "constraint x in 1..hi;\n"
        "constraint hi = 0; constraint x = 1; solve satisfy;\n";
    const Translation dynamic = run(dynamic_source);
    VERIFY(dynamic.ok());
    VERIFY(has(dynamic.toSmt2(), "(and (<= x hi) (>= x 1))"));
    const Translation parenthesized = run(
        "var 0..5: x; var 0..5: hi;\n"
        "constraint x in (1..hi);\n"
        "constraint hi = 0; constraint x = 1; solve satisfy;\n");
    VERIFY(parenthesized.ok());
    VERIFY(has(parenthesized.toSmt2(), "(and (<= x hi) (>= x 1))"));

    // A potentially undefined upper endpoint must stay guarded on the same
    // Boolean path: positive membership is false when div-by-zero is undefined,
    // while negating that undefined membership follows MiniZinc's false-value
    // rule and is satisfiable.
    const Translation positive_undefined = run(
        "var 0..1: d; var 0..5: x; constraint d = 0;\n"
        "constraint x in 1..(1 div d); solve satisfy;\n");
    VERIFY(positive_undefined.ok());
    VERIFY(has(positive_undefined.toSmt2(), "(distinct 0 d)"));
    const Translation negated_undefined = run(
        "var 0..1: d; var 0..5: x; constraint d = 0;\n"
        "constraint not (x in 1..(1 div d)); solve satisfy;\n");
    VERIFY(negated_undefined.ok());
    VERIFY(has(negated_undefined.toSmt2(), "(not (and (and (distinct 0 d)"));

    // Fixed set arrays retain both non-1-based index sets and enum element
    // identity through array1d construction and concatenation.
    const std::string fixed_enum_array =
        "enum E = {A, B, C, D};\n"
        "array[3..4] of set of E: S = array1d(3..4, [{A,C}, {B}]);\n"
        "array[7..8] of set of E: T = array1d(7..8, [{C}, {D}]);\n"
        "array[1..4] of set of E: U = S ++ T;\n"
        "var E: x; constraint x in S[3]; constraint x = A;\n"
        "constraint x in U[1]; solve satisfy;\n";
    const Translation array_translation = run(fixed_enum_array);
    VERIFY(array_translation.ok());
    VERIFY(has(array_translation.toSmt2(), "(or (= 1 x) (= 3 x))"));
    VERIFY(has(array_translation.toSmt2(), "(= 1 x)"));

    // Both index-axis and element enum types are checked rather than compared
    // only by their integer ordinals.
    const Translation wrong_element_enum = run(
        "enum E = {A, B}; enum F = {C, D};\n"
        "array[3..4] of set of E: S = array1d(3..4, [{A}, {B}]);\n"
        "var F: y; constraint y in S[3]; solve satisfy;\n");
    VERIFY(!wrong_element_enum.ok());
    VERIFY(wrong_element_enum.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    const Translation wrong_index_enum = run(
        "enum I = {I0, I1}; enum J = {J0, J1}; enum E = {A, B};\n"
        "array[I] of set of E: S = array1d(I, [{A}, {B}]);\n"
        "var E: x; constraint x in S[J0]; solve satisfy;\n");
    VERIFY(!wrong_index_enum.ok());
    VERIFY(wrong_index_enum.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);

    // Empty ranges retain their nominal lower bound while the body is
    // type-checked and discarded. Folding 1..0 to a normalized empty set
    // loses that bound and incorrectly checks x[0] instead of x[1].
    const Translation empty_range = run(
        "array[1..1] of int: x = [2];\n"
        "constraint forall(i in 1..0)(x[i] = 99);\n"
        "solve satisfy;\n");
    VERIFY(empty_range.ok());
    VERIFY(!has(empty_range.toSmt2(), "false"));

    // A range inside set algebra is still a fixed set operand. These cases
    // guard the distinction from a pure decision-dependent range: named and
    // literal unions, both bare and parenthesized, must remain membership in
    // the union rather than be reparsed as a single range.
    const std::string named_set = "set of int: S = {1};\n";
    const std::string prefix = "var 0..3: x; ";
    const std::string suffix = " constraint x = 3; solve satisfy;\n";
    const std::string unions[] = {
        prefix + "constraint x in {1} union 2..3;" + suffix,
        prefix + named_set + "constraint x in S union (2..3);" + suffix,
        prefix + "constraint x in ({1} union (2..3));" + suffix,
        prefix + named_set + "constraint x in (S union (2..3));" + suffix,
    };
    for (const auto& source : unions) {
        const Translation union_membership = run(source);
        if (!union_membership.ok()) {
            for (const auto& diagnostic : union_membership.diagnostics().all()) {
                std::cerr << diagnostic.loc.file << ':' << diagnostic.loc.line << ':'
                          << diagnostic.loc.column << ": " << diagnostic.message << '\n';
            }
        }
        VERIFY(union_membership.ok());
        VERIFY(has(union_membership.toSmt2(), "(= 3 x)"));
        VERIFY(!has(union_membership.toSmt2(), "false"));
    }
}
