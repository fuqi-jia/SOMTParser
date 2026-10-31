#include "somtparser/languages/mps.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir::Hir;
    constexpr int count = 4096;
    auto coefficient = [](int i) {
        return std::string("9007199254740993") + std::to_string(10000 + i);
    };
    Lang::SourceUnit unit;
    unit.main_path = "unique-coefficients.mps";
    unit.inline_source = "NAME coefficient_pool\nROWS\n N obj\n";
    for (int i = 0; i < count; ++i) {
        unit.inline_source += " L r" + std::to_string(i) + "\n";
    }
    unit.inline_source += "COLUMNS\n x obj 0\n";
    for (int i = 0; i < count; ++i) {
        unit.inline_source += " x r" + std::to_string(i) + " " + coefficient(i) + "\n";
    }
    unit.inline_source += "RHS\n";
    for (int i = 0; i < count; ++i) {
        unit.inline_source += " rhs r" + std::to_string(i) + " 1\n";
    }
    unit.inline_source += "ENDATA\n";
    auto language = Lang::mkMpsLanguage();
    auto result = language->parse(unit, Lang::ParseOptions{});
    VERIFY(result.ok());
    VERIFY(result.model->constraints.size() == count);
    for (int i = 0; i < count; ++i) {
        const auto& formula = result.model->constraints[i].formula;
        VERIFY(formula->op == Op::LE);
        const auto& term = formula->args.front();
        VERIFY(term->op == Op::MUL);
        VERIFY(term->args.front()->kind == ExprKind::LIT_REAL);
        VERIFY(term->args.front()->name == coefficient(i));
        VERIFY(term->args.back()->name == "x");
    }
    // Rehashing the intern table must not alter earlier coefficients, and all
    // values above 2^53 and 2^63 are retained as exact decimal text.
    Lang::SourceUnit repeated;
    repeated.inline_source = "NAME duplicates\nROWS\n N obj\n E row\nCOLUMNS\n"
        " x obj 1\n x row 9007199254740993\n x row -9007199254740992\n"
        "RHS\n rhs row 1\nENDATA\n";
    auto exact = language->parse(repeated, Lang::ParseOptions{});
    VERIFY(exact.ok());
    VERIFY(exact.model->constraints.front().formula->args.front()->op == Op::ADD);
    VERIFY(exact.model->constraints.front().formula->args.front()->args.size() == 2);
    Lang::ParseOptions recover;
    recover.options["highs_warning_recovery"] = "1";
    auto first = language->parse(repeated, recover);
    VERIFY(first.ok());
    VERIFY(first.model->constraints.front().formula->args.front()->op == Op::MUL);
    VERIFY(first.model->constraints.front().formula->args.front()->args.front()->name
           == "9007199254740993");
}
