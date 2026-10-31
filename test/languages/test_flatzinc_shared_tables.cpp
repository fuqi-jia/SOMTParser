#include "somtparser/languages/flatzinc.h"
#include "somtparser/translation/translate.h"
#include "../test_helpers.h"

#include <string>
#include <unordered_set>
#include <vector>

using namespace SOMTParser;
namespace H = Uir::Hir;

int main() {
    auto language = Lang::mkFlatZincLanguage();
    Lang::LanguageRegistry::instance().add(language);
    std::string table;
    for (int i = 0; i < 512; ++i) {
        if (!table.empty()) { table += ','; }
        table += std::to_string(i % 16) + ',' + std::to_string((i / 16) % 16)
            + ',' + std::to_string(i / 256);
    }
    std::string source = "array [1..1536] of int: table = [" + table + "];\n"
        + "array [1..1536] of int: same = [" + table + "];\n";
    for (int i = 0; i < 80; ++i) {
        const auto n = std::to_string(i);
        source += "var int: x" + n + "; var int: y" + n + "; var int: z" + n + ";\n";
        source += "constraint gecode_table_int([x" + n + ",y" + n + ",z" + n
            + "]," + (i % 2 ? "same" : "table") + ");\n";
    }
    // Fresh helper names must also avoid declarations after their first use.
    source += "var int: __somt_fzn_table_0; solve satisfy;\n";
    Lang::SourceUnit unit;
    unit.inline_source = source;
    unit.main_path = "shared-table.fzn";
    const auto parsed = language->parse(unit, {});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->funs.size() == 1);
    const auto& definition = parsed.model->funs.front();
    VERIFY(definition.auxiliary && definition.body && definition.binders.size() == 3);
    VERIFY(definition.name != "__somt_fzn_table_0");
    VERIFY(parsed.model->constraints.size() == 80);
    for (const auto& constraint : parsed.model->constraints) {
        VERIFY(constraint.formula->kind == H::ExprKind::APPLY);
        VERIFY(constraint.formula->name == definition.name);
    }
    // The 80 calls must not allocate 80 copies of 512*3 equalities, and
    // repeated column/value tests must share their immutable HIR nodes.
    std::unordered_set<const H::Expr*> visited;
    std::vector<H::ExprPtr> pending{definition.body};
    while (!pending.empty()) {
        const auto expression = pending.back();
        pending.pop_back();
        if (!visited.insert(expression.get()).second) { continue; }
        pending.insert(pending.end(), expression->args.begin(), expression->args.end());
    }
    VERIFY(visited.size() < 650);
    TranslateOptions options;
    options.language_id = "flatzinc";
    const auto translated = translate(unit, options);
    VERIFY(translated.ok());
    VERIFY(translated.toSmt2().find("define-fun") != std::string::npos);
    return 0;
}
