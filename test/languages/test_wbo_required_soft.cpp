#include "somtparser/languages/opb.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir::Hir;
    auto language = Lang::mkOpbLanguage();
    Lang::SourceUnit unit;
    unit.main_path = "required-soft.wbo";
    unit.inline_source = "soft: +000349 ;\n";
    constexpr int rows = 5000;
    for (int i = 0; i < rows; ++i) {
        unit.inline_source += "[+00349] +1 x1 +1 ~x2 >= 1 ;\n";
    }
    unit.inline_source += "[1] +1 x3 = 1 ;\n";
    auto parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    // The 5000 rows are mandatory under the strict threshold. Only the last
    // row has a relaxation variable; its objective remains to be minimised.
    VERIFY(parsed.model->decls.size() == 4);
    VERIFY(parsed.model->constraints.size() == rows + 2);
    for (int i = 0; i < rows; ++i) {
        const auto& constraint = parsed.model->constraints[i];
        VERIFY(constraint.formula->op == Op::GE);
        VERIFY(!constraint.soft);
        VERIFY(constraint.loc.line == i + 2);
        VERIFY(constraint.formula->loc.line == i + 2);
    }
    VERIFY(parsed.model->constraints[rows].formula->op == Op::EQ);
    VERIFY(parsed.model->objectives.size() == 1);

    unit.inline_source = "soft: +0001 ;\n[9007199254740993] +1 x1 = 1 ;\n";
    parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->decls.size() == 1);
    VERIFY(parsed.model->constraints[0].formula->op == Op::EQ);
    VERIFY(parsed.model->objectives[0].term->name == "0");

    // Without a finite, constraining threshold there is no justification for
    // hardening any row, even a very expensive one.
    unit.inline_source = "soft: ;\n[9007199254740993] +1 x1 = 1 ;\n";
    parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->constraints[0].soft);
    unit.inline_source = "soft: 9007199254740994 ;\n[9007199254740993] +1 x1 = 1 ;\n";
    parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->constraints[0].soft);

    for (const std::string cost : {"-1", "-9007199254740993", "0", "00", "+0", "-0"}) {
        unit.inline_source = "soft: 1 ;\n[" + cost + "] +1 x1 = 1 ;\n";
        VERIFY(!language->parse(unit, Lang::ParseOptions{}).ok());
    }
}
