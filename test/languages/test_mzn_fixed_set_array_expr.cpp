#include "somtparser/languages/minizinc.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {
Translation run(const std::string& source) {
    Lang::SourceUnit unit;
    unit.main_path = "fixed-set-array-expr.mzn";
    unit.display_name = unit.main_path;
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& needle) {
    return text.find(needle) != std::string::npos;
}
}

int main() {
    Lang::LanguageRegistry::instance().add(Lang::mkMiniZincLanguage());

    // This mirrors the source-level shape of the official IS constructor:
    // concatenate a named fixed set array with a final singleton, then
    // explicitly index the result with array1d. Set intervals remain compact
    // throughout; no interval member expansion is required.
    {
        const auto result = run(
            "set of int: I = 1..3;\n"
            "array[1..2] of set of int: base = [{1}, {2, 3}];\n"
            "array[I] of set of int: joined = array1d(I,\n"
            "  base ++ array1d(3..3, [I]));\n"
            "constraint joined[1] = {1};\n"
            "constraint joined[2] = {2, 3};\n"
            "constraint joined[3] = I;\n"
            "constraint 3 in joined[3];\n"
            "constraint not (4 in joined[3]);\n"
            "solve satisfy;\n");
        if (!result.ok()) {
            for (const auto& diagnostic : result.diagnostics().all()) {
                std::cerr << diagnostic.loc.file << ':' << diagnostic.loc.line << ':'
                          << diagnostic.loc.column << ": " << diagnostic.message << '\n';
            }
        }
        VERIFY(result.ok());
        VERIFY(!has(result.toSmt2(), "false"));

        const auto wrong_cell = run(
            "set of int: I = 1..3;\n"
            "array[1..2] of set of int: base = [{1}, {2, 3}];\n"
            "array[I] of set of int: joined = array1d(I,\n"
            "  base ++ array1d(3..3, [I]));\n"
            "constraint 4 in joined[2];\n"
            "solve satisfy;\n");
        VERIFY(wrong_cell.ok());
        VERIFY(has(wrong_cell.toSmt2(), "false"));
    }

    // arrayNd preserves every explicit index origin and row-major cell order.
    {
        const auto result = run(
            "array[1..2, 0..1] of set of int: matrix =\n"
            "  array2d(1..2, 0..1, [{1}, {2}, {3}, {4}]);\n"
            "constraint matrix[1, 0] = {1};\n"
            "constraint matrix[1, 1] = {2};\n"
            "constraint matrix[2, 0] = {3};\n"
            "constraint matrix[2, 1] = {4};\n"
            "solve satisfy;\n");
        VERIFY(result.ok());
        VERIFY(!has(result.toSmt2(), "false"));

        const auto mismatched_extent = run(
            "array[1..2, 0..1] of set of int: matrix =\n"
            "  array2d(1..2, 0..2, [{1}, {2}, {3}, {4}, {5}, {6}]);\n"
            "solve satisfy;\n");
        VERIFY(!mismatched_extent.ok());

        const auto mismatched_count = run(
            "array[1..2, 0..1] of set of int: matrix =\n"
            "  array2d(1..2, 0..1, [{1}, {2}]);\n"
            "solve satisfy;\n");
        VERIFY(!mismatched_count.ok());
    }

    // The enum identity belongs to each set cell's member sort and survives
    // concatenation, including when a declaration supplies the target type.
    {
        const auto mismatch = run(
            "enum E = {a, b}; enum F = {c, d};\n"
            "array[1..1] of set of E: left = [{a}];\n"
            "array[1..1] of set of F: right = [{c}];\n"
            "array[1..2] of set of E: joined = left ++ right;\n"
            "solve satisfy;\n");
        VERIFY(!mismatch.ok());
    }

    // FixedIntSet stores this as a single interval even though the array
    // pipeline copies and concatenates it.
    {
        const auto result = run(
            "set of int: large_domain = 1..1000000;\n"
            "array[1..1] of set of int: large = [large_domain];\n"
            "constraint 999999 in large[1];\n"
            "constraint not (1000001 in large[1]);\n"
            "solve satisfy;\n");
        VERIFY(result.ok());
        VERIFY(!has(result.toSmt2(), "false"));
    }

    // The single-argument array1d overload linearizes a set-array and
    // reindexes it to the ordinary 1-based result.
    {
        const auto result = run(
            "array[4..5] of set of int: source = array1d(4..5, [{1}, {2}]);\n"
            "array[1..2] of set of int: linear = array1d(source);\n"
            "constraint linear[1] = {1};\n"
            "constraint linear[2] = {2};\n"
            "solve satisfy;\n");
        VERIFY(result.ok());
        VERIFY(!has(result.toSmt2(), "false"));
    }

    // Fixed set expressions are consumed as one generator source. The
    // precedence matches MiniZinc: intersection binds more tightly than
    // union/difference, whose chains associate left-to-right.
    {
        const auto difference_intersection = run(
            "set of int: A = 1..5;\n"
            "set of int: B = {2, 3};\n"
            "set of int: C = {3, 4};\n"
            "constraint sum(i in A diff B intersect C)(i) = 12;\n"
            "solve satisfy;\n");
        VERIFY(difference_intersection.ok());
        VERIFY(!has(difference_intersection.toSmt2(), "false"));

        const auto difference_union = run(
            "set of int: A = 1..5;\n"
            "set of int: B = {2, 3};\n"
            "set of int: C = {3, 4};\n"
            "constraint sum(i in A diff B union C)(i) = 13;\n"
            "solve satisfy;\n");
        VERIFY(difference_union.ok());
        VERIFY(!has(difference_union.toSmt2(), "false"));

        const auto wrong_precedence = run(
            "set of int: A = 1..5;\n"
            "set of int: B = {2, 3};\n"
            "set of int: C = {3, 4};\n"
            "constraint sum(i in A diff B intersect C)(i) = 13;\n"
            "solve satisfy;\n");
        VERIFY(wrong_precedence.ok());
        VERIFY(has(wrong_precedence.toSmt2(), "false"));

        // The second operand may be a forward-declared set assigned later;
        // this verifies operand parsing does not stop after the first name.
        const auto forward_assignment = run(
            "set of int: S = 1..3;\n"
            "set of int: T;\n"
            "constraint sum(i in S diff T)(i) = 4;\n"
            "T = {2};\n"
            "solve satisfy;\n");
        if (!forward_assignment.ok()) {
            for (const auto& diagnostic : forward_assignment.diagnostics().all()) {
                std::cerr << diagnostic.loc.file << ':' << diagnostic.loc.line << ':'
                          << diagnostic.loc.column << ": " << diagnostic.message << '\n';
            }
        }
        VERIFY(forward_assignment.ok());
        VERIFY(!has(forward_assignment.toSmt2(), "false"));

        const auto array_read = run(
            "array[1..2] of set of int: domains = [{1, 2}, {2}];\n"
            "constraint sum(i in (domains[1] diff domains[2]))(i) = 1;\n"
            "solve satisfy;\n");
        VERIFY(array_read.ok());
        VERIFY(!has(array_read.toSmt2(), "false"));
    }

    // `xor` shares MiniZinc's precedence tier with `\\/` and is left
    // associative. It also appears in the official IS objective's
    // conditional branch, so it must parse as a Boolean operator there.
    {
        const auto precedence = run(
            "constraint (true \\/ false xor true) = false;\n"
            "constraint if true then true xor false else false endif;\n"
            "solve satisfy;\n");
        if (!precedence.ok()) {
            for (const auto& diagnostic : precedence.diagnostics().all()) {
                std::cerr << diagnostic.loc.file << ':' << diagnostic.loc.line << ':'
                          << diagnostic.loc.column << ": " << diagnostic.message << '\n';
            }
        }
        VERIFY(precedence.ok());
        VERIFY(!has(precedence.toSmt2(), "false"));

        const auto false_case = run(
            "constraint true xor true;\n"
            "solve satisfy;\n");
        VERIFY(false_case.ok());
        VERIFY(has(false_case.toSmt2(), "false"));
    }

    // Membership in a decision-dependent range is the conjunction of its
    // endpoint comparisons, so an empty range admits no element and partial
    // array reads on either endpoint remain guarded.
    {
        const auto dynamic = run(
            "var int: x; var int: lo; var int: hi;\n"
            "constraint x in lo..hi;\n"
            "constraint x = 3 /\\ lo = 2 /\\ hi = 4;\n"
            "solve satisfy;\n");
        if (!dynamic.ok()) {
            for (const auto& diagnostic : dynamic.diagnostics().all()) {
                std::cerr << diagnostic.loc.file << ':' << diagnostic.loc.line << ':'
                          << diagnostic.loc.column << ": " << diagnostic.message << '\n';
            }
        }
        VERIFY(dynamic.ok());
        VERIFY(has(dynamic.toSmt2(), "(>= "));
        VERIFY(has(dynamic.toSmt2(), "(<= "));

        const auto empty = run(
            "var int: x; var int: lo; var int: hi;\n"
            "constraint x in (lo..hi);\n"
            "constraint x = 3 /\\ lo = 4 /\\ hi = 2;\n"
            "solve satisfy;\n");
        VERIFY(empty.ok());
        VERIFY(has(empty.toSmt2(), "(>= "));
        VERIFY(has(empty.toSmt2(), "(<= "));
    }

    // Parenthesized constant ranges inside `card` remain parse-time sets even
    // when set algebra separates them. This is the form used by the official
    // IS dominance predicate for parameter-array entries.
    {
        const auto cardinality = run(
            "array[1..1] of int: lo1 = [1];\n"
            "array[1..1] of int: hi1 = [3];\n"
            "array[1..1] of int: lo2 = [2];\n"
            "array[1..1] of int: hi2 = [4];\n"
            "constraint forall(i in 1..1)(\n"
            "  card((lo1[i]..hi1[i]) intersect (lo2[i]..hi2[i])) = 2);\n"
            "solve satisfy;\n");
        if (!cardinality.ok()) {
            for (const auto& diagnostic : cardinality.diagnostics().all()) {
                std::cerr << diagnostic.loc.file << ':' << diagnostic.loc.line << ':'
                          << diagnostic.loc.column << ": " << diagnostic.message << '\n';
            }
        }
        VERIFY(cardinality.ok());
        VERIFY(!has(cardinality.toSmt2(), "false"));
    }

    // Membership uses the same finite-set algebra parser, including a
    // parenthesized range on the right of a union.
    {
        const auto membership = run(
            "var int: x;\n"
            "constraint x in {0} union (31..35);\n"
            "constraint x = 33;\n"
            "solve satisfy;\n");
        if (!membership.ok()) {
            for (const auto& diagnostic : membership.diagnostics().all()) {
                std::cerr << diagnostic.loc.file << ':' << diagnostic.loc.line << ':'
                          << diagnostic.loc.column << ": " << diagnostic.message << '\n';
            }
        }
        VERIFY(membership.ok());
        VERIFY(!has(membership.toSmt2(), "false"));
    }
    return 0;
}
