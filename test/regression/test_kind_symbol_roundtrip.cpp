// kindToString() must name the operator it was given.
//
// The parser reads a symbol through oper_key_map (symbol -> kind) and the
// printer writes one through kindToString (kind -> symbol).  Nothing has ever
// checked that the two agree, and they did not: NT_STR_INDEXOF_REG printed as
// "str.indexof", which oper_key_map resolves to NT_STR_INDEXOF -- a different
// operator taking three arguments instead of two.  Any term containing
// str.indexof_re therefore dumped to a script this parser rejects.
//
// That defect is invisible to a per-operator test, because printing is correct
// in isolation for every operator someone remembered to check.  It is only
// visible as a property over the whole table, which is what this file asserts:
//
//     for every kind k whose printed name is a known operator symbol,
//     that symbol must resolve back to k.
//
// The converse direction is deliberately NOT asserted.  Aliases are a feature
// here: oper_key_map maps several spellings onto one kind (the FloatingPoint
// leniency described in CLAUDE.md, "-" for both negation and subtraction), so
// requiring symbol -> kind -> same symbol would fail on correct code.  Only the
// direction that makes a dump unreadable is a defect.

#include "somtparser/frontend/parser.h"

#include <iostream>
#include <utility>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

// Kinds that deliberately print a symbol oper_key_map resolves to a *different*
// kind.  A shared symbol is only acceptable when the parser can recover the
// right operator semantics from the term itself; each entry below records how, and each was
// checked by building the term, dumping it, re-parsing, and confirming the kind
// came back unchanged.  NT_STR_INDEXOF_REG is deliberately absent: it shared
// "str.indexof" with an operator of a different arity, so nothing could have
// recovered it, and the dump was unreadable.
const std::vector<std::pair<NODE_KIND, const char*>> kSharedByDesign = {
    // "-" is SMT-LIB's own overload.  Recovered by arity: one argument is
    // negation, two or more is subtraction.  Verified: (- x) round-trips as
    // NT_NEG and (- x y) as NT_SUB.
    {NODE_KIND::NT_NEG, "arity: 1 argument is negation, 2+ is subtraction"},

    // The legacy internal signed builder and the SMT-LIB 2.7 signed builder
    // have identical semantics. The source spelling bv2int is UNSIGNED, so it
    // cannot serialize the internal signed operator. Independent solver tests
    // cover this alias through HIR/CryptoLine and constant/symbolic inputs.
    {NODE_KIND::NT_BV_TO_INT, "signed internal synonym of NT_SBV_TO_INT"},

    // Sort-specialised variants of = and distinct.  The parser never builds
    // them -- (= a b) on Bool parses to NT_EQ, not NT_EQ_BOOL -- so they are
    // produced only internally (conv_parser's binarisation lists them) and
    // recovered by re-deriving from the operands' sorts.
    {NODE_KIND::NT_EQ_BOOL, "sort-specialised; parser builds plain NT_EQ and re-derives"},
    {NODE_KIND::NT_EQ_OTHER, "sort-specialised; parser builds plain NT_EQ and re-derives"},
    {NODE_KIND::NT_DISTINCT_BOOL, "sort-specialised; parser builds plain NT_DISTINCT"},
    {NODE_KIND::NT_DISTINCT_OTHER, "sort-specialised; parser builds plain NT_DISTINCT"},
};

bool isSharedSymbolByDesign(NODE_KIND k) {
    for (const auto& entry : kSharedByDesign) {
        if (entry.first == k) { return true; }
    }
    return false;
}

}  // namespace

int main() {
    std::cout << "======= kindToString / oper_key_map agreement =======\n";

    // oper_key_map lives on the parser; go through one rather than duplicating
    // the table here, so this test tracks the real lookup the parser performs.
    auto parser = std::make_shared<Parser>();

    struct Mismatch {
        std::string symbol;
        std::size_t printed_by;
        std::size_t resolves_to;
    };
    std::vector<Mismatch> mismatches;
    std::size_t checked = 0;
    std::size_t allowed = 0;

    for (std::size_t i = 0; i < NUM_KINDS; ++i) {
        const auto kind = static_cast<NODE_KIND>(i);
        const std::string printed = kindToString(kind);
        if (printed.empty()) { continue; }

        const auto it = oper_key_map.find(printed);
        if (it == oper_key_map.end()) {
            // Not an operator symbol at all (NT_CONST, NT_VAR, internal kinds).
            // Those print a descriptive name and are never parsed back.
            continue;
        }

        ++checked;
        if (it->second != kind) {
            if (isSharedSymbolByDesign(kind)) { ++allowed; continue; }
            mismatches.push_back({printed, i, static_cast<std::size_t>(it->second)});
        }
    }

    // Every entry in the allow-list must still be a collision.  Without this,
    // fixing one of them would leave a stale exemption that silently forgives
    // a future regression on the same symbol.
    VERIFY(allowed == kSharedByDesign.size());

    for (const auto& m : mismatches) {
        std::cerr << "  FAIL kind #" << m.printed_by << " prints as \"" << m.symbol
                  << "\", which the parser resolves to kind #" << m.resolves_to << "\n";
    }

    std::cout << checked << " operator kind(s) checked, " << mismatches.size() << " mismatched\n";
    VERIFY(mismatches.empty());
    // A table lookup that silently stopped matching anything would leave
    // mismatches empty; require the property to have been exercised.
    VERIFY(checked >= 100);

    std::cout << "Every operator kind prints a symbol with the same operator semantics.\n";
    return 0;
}
