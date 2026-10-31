// Fixed arrays of sets may name a finite parameter set as their element
// domain. The domain is a membership constraint and must remain sparse: using
// its min/max would admit values the MiniZinc type excludes.

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
    unit.display_name = "<named-set-domain-test>";
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

} // namespace

int main() {
    std::cout << "======= MiniZinc: named finite set element domains =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        const Translation t = mzn(
            "set of int: Ori = {1, 3};\n"
            "array[1..2] of set of Ori: rm_ori = [{1, 3}, {3}];\n"
            "constraint 1 in rm_ori[1];\n"
            "constraint 3 in rm_ori[2];\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(!t.toSmt2().empty());
    }

    {
        // A sparse domain is not its bounding interval. The middle value 2
        // must be rejected even though it lies between min(Ori) and max(Ori).
        const Translation t = mzn(
            "set of int: Ori = {1, 3};\n"
            "array[1..1] of set of Ori: rm_ori = [{1, 2, 3}];\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    {
        // The type-inst name must resolve to a previously established fixed
        // set. Accepting an unknown identifier as an unconstrained int set
        // would erase the declaration's domain.
        const Translation t = mzn(
            "array[1..1] of set of Missing: rm_ori = [{1}];\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
    }

    {
        // Both an empty named domain and empty set-valued cells are legal;
        // empty values satisfy every finite element-domain restriction.
        const Translation t = mzn(
            "set of int: Empty = {};\n"
            "set of int: D = {-2, 2};\n"
            "array[1..2] of set of Empty: no_members = [{}, {}];\n"
            "array[1..2] of set of D: maybe_members = [{}, {-2, 2}];\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
    }

    {
        // The signed endpoints are preserved as individual members, without
        // overflowing while checking a sparse domain or widening its span.
        const Translation t = mzn(
            "set of int: D = {-9223372036854775807, 9223372036854775807};\n"
            "array[1..1] of set of D: edge = "
            "[{-9223372036854775807, 9223372036854775807}];\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
    }

    return 0;
}
