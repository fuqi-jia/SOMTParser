// DIMACS literal sharing preserves clause, header and counting semantics.
#include "somtparser/languages/dimacs.h"
#include "somtparser/hir/hir.h"

#include "test_helpers.h"
#include <string>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir;
    using namespace SOMTParser::Uir::Hir;
    using SOMTParser::Uir::ErrorCode;

    Lang::SourceUnit unit;
    unit.main_path = "literal-sharing.cnf";
    unit.display_name = unit.main_path;
    unit.inline_source =
        "c t pwmc\n"
        "c p weight 1 0.25 0\n"
        "c p show 1 3 0\n"
        "p cnf 4 5\n"
        "1 1 -2 0\n"
        "1 -2 -1 0\n"
        "-1 2 0\n"
        "0\n"
        "3 0\n";

    auto language = Lang::mkDimacsLanguage();
    const Lang::ParseOutcome parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    const auto& model = *parsed.model;

    // The header still defines x1..x4, including the unused x4.
    VERIFY(model.decls.size() == 4);
    VERIFY(model.decls[3].name == "x4");
    VERIFY(model.constraints.size() == 5);

    // Formula/constraint roots retain each original clause line.
    for (std::size_t i = 0; i < model.constraints.size(); ++i) {
        VERIFY(model.constraints[i].loc.line == static_cast<int>(5 + i));
    }
    VERIFY(model.constraints[0].formula->loc.line == 5);
    VERIFY(model.constraints[1].formula->loc.line == 6);
    VERIFY(model.constraints[2].formula->loc.line == 7);
    VERIFY(model.constraints[3].formula->kind == ExprKind::LIT_BOOL);
    VERIFY(!model.constraints[3].formula->bool_value); // empty clause is FALSE

    // Repeated positive and negative literals point at one immutable HIR node
    // per (variable, sign); the NOT wrapper itself is shared as well.
    const auto& c0 = model.constraints[0].formula;
    const auto& c1 = model.constraints[1].formula;
    const auto& c2 = model.constraints[2].formula;
    VERIFY(c0->kind == ExprKind::OP && c0->op == Op::OR);
    VERIFY(c1->kind == ExprKind::OP && c1->op == Op::OR);
    VERIFY(c2->kind == ExprKind::OP && c2->op == Op::OR);
    VERIFY(c0->args[0].get() == c0->args[1].get()); // repeated x1 in one clause
    VERIFY(c0->args[0].get() == c1->args[0].get()); // x1 across clauses
    VERIFY(c0->args[2].get() == c1->args[1].get()); // not x2 across clauses
    VERIFY(c1->args[2].get() == c2->args[0].get()); // not x1 across clauses
    VERIFY(c0->args[2]->kind == ExprKind::OP && c0->args[2]->op == Op::NOT);
    VERIFY(c0->args[0]->loc.line == 4); // canonical variable-vocabulary location

    bool saw_weights = false;
    bool saw_projection = false;
    for (const EncodingChoice& choice : parsed.report.choices()) {
        saw_weights |= choice.strategy == "counting-weights"
            && choice.rationale.find("0.25") != std::string::npos;
        saw_projection |= choice.strategy == "counting-projection"
            && choice.rationale.find("2 variable") != std::string::npos;
    }
    VERIFY(saw_weights && saw_projection);

    // An unterminated clause still points to its original source line.
    Lang::SourceUnit bad;
    bad.main_path = "bad-line.cnf";
    bad.inline_source = "p cnf 1 1\n1\n";
    const auto rejected = language->parse(bad, Lang::ParseOptions{});
    VERIFY(!rejected.ok());
    VERIFY(!rejected.diagnostics.all().empty());
    VERIFY(rejected.diagnostics.all().front().loc.line == 2);

    // abs(LLONG_MIN) is not representable and must be rejected before the
    // cached variable-index lookup can overflow.
    Lang::SourceUnit boundary;
    boundary.main_path = "boundary.cnf";
    boundary.inline_source = "p cnf 1 1\n-9223372036854775808 0\n";
    const auto boundary_rejected = language->parse(boundary, Lang::ParseOptions{});
    VERIFY(!boundary_rejected.ok());
    VERIFY(!boundary_rejected.diagnostics.all().empty());
    VERIFY(boundary_rejected.diagnostics.all().front().code == ErrorCode::E_PARSE);
    VERIFY(boundary_rejected.diagnostics.all().front().loc.line == 2);
}
