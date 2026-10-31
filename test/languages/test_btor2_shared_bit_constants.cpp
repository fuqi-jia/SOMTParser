#include "somtparser/languages/btor2.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <unordered_set>
#include <vector>

namespace H = SOMTParser::Uir::Hir;

int main() {
    SOMTParser::Lang::ParseOutcome parsed;
    {
        SOMTParser::Lang::SourceUnit source;
        source.main_path = "released-source.btor2";
        source.inline_source = "1 sort bitvec 1\n2 input 1 input signal\n"
            "3 state 1 state signal\n4 eq 1 2 3\n5 neq 1 2 3\n"
            "6 ite 1 4 2 3\n7 implies 1 4 5\n8 iff 1 4 5\n"
            "9 next 1 3 6\n10 constraint 7\n11 bad -8\n"
            "12 output 6 selected output\n13 output 7 implication output\n"
            "14 output 8 equivalence output\n";
        SOMTParser::Lang::ParseOptions options;
        options.options["bmc_depth"] = "2";
        parsed = SOMTParser::Lang::mkBtor2Language()->parse(source, options);
        VERIFY(parsed.ok());
        source.inline_source.assign(source.inline_source.size(), 'x');
    }
    // This is a memory regression: with no explicit constant records, all
    // literal nodes belong to the repeated Bool/BV1 adapters. A larger graph
    // must not allocate two fresh constants for every comparison/time frame.
    std::vector<const H::Expr*> pending;
    for (const auto& c : parsed.model->constraints) { pending.push_back(c.formula.get()); }
    std::unordered_set<const H::Expr*> seen, literals;
    std::size_t literal_edges = 0;
    while (!pending.empty()) {
        const auto* e = pending.back(); pending.pop_back();
        if (e->kind == H::ExprKind::LIT_BITVEC) {
            ++literal_edges;
            VERIFY(e->sort.width == 1 && (e->name == "#b0" || e->name == "#b1"));
            literals.insert(e);
        }
        if (!seen.insert(e).second) { continue; }
        for (const auto& child : e->args) { pending.push_back(child.get()); }
    }
    VERIFY(literal_edges >= 20);
    VERIFY(literals.size() == 2);
    SOMTParser::Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(*parsed.model, diagnostics));
    VERIFY(parsed.semantics.validate(diagnostics));
    return 0;
}
