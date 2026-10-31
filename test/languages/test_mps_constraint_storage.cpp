#include "somtparser/languages/mps.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir::Hir;
    constexpr int count = 16385;
    Lang::SourceUnit unit;
    unit.main_path = "constraint-storage.mps";
    unit.inline_source = "NAME storage\nOBJNAME objective\nROWS\n N free\n N objective\n";
    for (int i = 0; i < count; ++i) {
        unit.inline_source += std::string(" ") + "LGE"[i % 3]
            + " r" + std::to_string(i) + "\n";
    }
    unit.inline_source += "COLUMNS\n x objective 1\n x free 99\n";
    for (int i = 0; i < count; ++i) {
        unit.inline_source += " x r" + std::to_string(i) + " 1\n";
    }
    unit.inline_source += "RHS\n";
    for (int i = 0; i < count; ++i) {
        unit.inline_source += " rhs r" + std::to_string(i) + " 10\n";
    }
    unit.inline_source += "RANGES\n";
    for (int i = 0; i < count; ++i) {
        if (i % 6 >= 3) {
            unit.inline_source += " range r" + std::to_string(i) + " -2\n";
        }
    }
    unit.inline_source += "BOUNDS\n LO bound x 2\n SC bound x 20\nENDATA\n";
    auto language = Lang::mkMpsLanguage();
    auto parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->constraints.size() == count + 1);
    VERIFY(parsed.model->objectives.size() == 1);
    VERIFY(parsed.model->objectives.front().name == "objective");
    VERIFY(parsed.model->objectives.front().term->name == "x");
    VERIFY(parsed.model->constraints.front().formula->op == Op::OR);
    for (int i = 0; i < count; ++i) {
        const auto& constraint = parsed.model->constraints[i + 1];
        VERIFY(constraint.loc.line == i + 6);
        VERIFY(constraint.formula->loc.line == i + 6);
        const auto& formula = constraint.formula;
        if (i % 6 < 3) {
            VERIFY(formula->op == (i % 3 == 0 ? Op::LE : i % 3 == 1 ? Op::GE : Op::EQ));
            VERIFY(formula->args.front()->name == "x");
            VERIFY(formula->args.back()->name == "10");
        } else {
            VERIFY(formula->op == Op::AND);
            VERIFY(formula->args.size() == 2);
            const auto& lower = formula->args.front();
            const auto& upper = formula->args.back();
            VERIFY(lower->op == Op::LE && upper->op == Op::LE);
            VERIFY(lower->args.front()->name == (i % 3 == 1 ? "10" : "8"));
            VERIFY(upper->args.back()->name == (i % 3 == 1 ? "12" : "10"));
            VERIFY(lower->args.back()->name == "x");
            VERIFY(upper->args.front()->name == "x");
        }
    }
    // No-N input still has one constraint per ordinary row. An all-N input
    // retains its objective without inventing a constraint for a free row.
    Lang::SourceUnit boundary;
    boundary.inline_source = "NAME no_objective\nROWS\n E row\nCOLUMNS\n x row 1\nENDATA\n";
    auto no_objective = language->parse(boundary, Lang::ParseOptions{});
    VERIFY(no_objective.ok());
    VERIFY(no_objective.model->constraints.size() == 1);
    VERIFY(no_objective.model->objectives.empty());
    boundary.inline_source = "NAME no_constraints\nROWS\n N objective\n N free\nCOLUMNS\n x objective 1\n x free 2\nENDATA\n";
    auto no_constraints = language->parse(boundary, Lang::ParseOptions{});
    VERIFY(no_constraints.ok());
    VERIFY(no_constraints.model->constraints.empty());
    VERIFY(no_constraints.model->objectives.size() == 1);
}
