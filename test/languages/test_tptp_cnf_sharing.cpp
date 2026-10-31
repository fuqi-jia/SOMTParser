#include "somtparser/languages/tptp.h"
#include "test_helpers.h"

#include <string>
#include <unordered_set>
#include <vector>

using namespace SOMTParser;
namespace H = Uir::Hir;

static std::vector<H::ExprPtr> variables(const H::ExprPtr& root) {
    std::unordered_set<const H::Expr*> seen;
    std::vector<H::ExprPtr> pending{root}, found;
    while (!pending.empty()) {
        auto expression = pending.back();
        pending.pop_back();
        if (!seen.insert(expression.get()).second) { continue; }
        if (expression->kind == H::ExprKind::BOUND_VAR) { found.push_back(expression); }
        pending.insert(pending.end(), expression->args.begin(), expression->args.end());
    }
    return found;
}

int main() {
    auto language = Lang::mkTptpLanguage();
    Lang::SourceUnit source;
    source.display_name = "cnf-sharing.p";
    source.main_path = source.display_name;
    std::string clause = "cnf(first,axiom,(";
    for (int literal = 0; literal < 64; ++literal) {
        if (literal) { clause += " | "; }
        if (literal == 32) { clause += '\n'; }
        clause += "p(";
        for (int argument = 0; argument < 64; ++argument) {
            if (argument) { clause += ','; }
            clause += "X";
        }
        clause += ')';
    }
    clause += ")).cnf(second,axiom,q(X,X)).";
    source.inline_source = clause;
    const auto parsed = language->parse(source, {});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->constraints.size() == 2);
    const auto first = variables(parsed.model->constraints[0].formula);
    const auto second = variables(parsed.model->constraints[1].formula);
    // Thousands of occurrences need only one node for their clause binding.
    // Its source location is the first use; applications retain their own
    // locations, and a later clause gets an independent binding.
    VERIFY(first.size() == 1);
    VERIFY(second.size() == 1);
    VERIFY(first[0]->loc.file == source.display_name);
    VERIFY(first[0]->loc.line == 1);
    VERIFY(second[0]->loc.line == 2);
    for (const auto& node : first) {
        VERIFY(node != second.front());
        VERIFY(node->name == "X");
    }
    VERIFY(parsed.model->constraints[0].formula->binders.size() == 1);
    VERIFY(parsed.model->constraints[1].formula->binders.size() == 1);
    source.inline_source = "cnf(a,axiom,p(X)).fof(b,axiom,q(X)).";
    VERIFY(!language->parse(source, {}).ok());
}
