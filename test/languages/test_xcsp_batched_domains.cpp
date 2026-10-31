// Array membership metadata should scale with declarations, not cell count.
#include "somtparser/languages/xcsp3.h"
#include "somtparser/hir/hir.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"
#include <string>

int main() {
    using namespace SOMTParser;
    namespace H = Uir::Hir;
    Lang::SourceUnit unit;
    unit.display_name = std::string(200, 'p') + ".xml";
    unit.inline_source =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables>\n"
        "<array id=\"a\" size=\"[5000]\">-1 1</array>\n"
        "<var id=\"b\" as=\"a\"/>\n"
        "<array id=\"c\" size=\"[3]\"><domain for=\"c[0]\">0..1</domain>"
        "<domain for=\"others\">1 3</domain></array>\n"
        "<var id=\"d\" as=\"c[2]\"/>\n"
        "</variables></instance>";
    auto outcome = Lang::mkXcsp3Language()->parse(unit, {});
    VERIFY(outcome.ok());
    if (!outcome.model) { return 1; }
    const auto& model = *outcome.model;
    VERIFY(model.decls.size() == 10004);
    VERIFY(model.constraints.size() == 4);
    VERIFY(model.funs.size() == 1);
    const auto& domain = model.funs.front();
    VERIFY(domain.auxiliary && domain.params.size() == 1);
    VERIFY(domain.params.front().kind == H::SortKind::INT);
    VERIFY(domain.binders.size() == 1);
    VERIFY(domain.body->op == H::Op::OR && domain.body->args.size() == 2);
    for (std::size_t i = 0; i < 2; ++i) {
        const auto& equality = domain.body->args[i];
        VERIFY(equality->op == H::Op::EQ && equality->args.size() == 2);
        VERIFY(equality->args[0]->kind == H::ExprKind::BOUND_VAR);
        VERIFY(equality->args[0]->name == domain.binders[0].name);
        VERIFY(equality->args[1]->kind == H::ExprKind::LIT_INT);
        VERIFY(equality->args[1]->name == (i == 0 ? "-1" : "1"));
    }
    // Keep exact cell predicates and the source locations of their declarations.
    const std::size_t arities[] = {5000, 5000, 2};
    for (std::size_t i = 0; i < 3; ++i) {
        const auto& constraint = model.constraints[i];
        VERIFY(constraint.formula->op == H::Op::AND);
        VERIFY(constraint.formula->args.size() == arities[i]);
        VERIFY(constraint.loc.file == unit.display_name);
        VERIFY(constraint.loc.line == static_cast<int>(i + 2));
        for (const auto& member : constraint.formula->args) {
            if (i == 0) {
                VERIFY(member->kind == H::ExprKind::APPLY);
                VERIFY(member->name == domain.name && member->args.size() == 1);
                VERIFY(member->args[0]->kind == H::ExprKind::IDENT);
            } else {
                VERIFY(member->op == H::Op::DISTINCT);
            }
            const auto& location = member->loc.file.empty() ? constraint.loc : member->loc;
            VERIFY(location.file == unit.display_name);
            VERIFY(location.line == static_cast<int>(i + 2));
        }
    }
    VERIFY(model.constraints[3].formula->op == H::Op::DISTINCT);
    VERIFY(model.constraints[3].loc.line == 5);
    // A generated child with no own location must still report the array
    // declaration, rather than dropping the source name during type checking.
    H::ConstraintModel invalid = model;
    auto args = invalid.constraints[0].formula->args;
    args[0] = H::mkInt(42);
    invalid.constraints[0].formula = H::mkOp(H::Op::AND, std::move(args));
    Uir::Diagnostics diagnostics;
    VERIFY(!H::typeCheck(invalid, diagnostics));
    VERIFY(diagnostics.hasErrors());
    for (const auto& diagnostic : diagnostics.all()) {
        if (diagnostic.severity == Uir::Severity::ERROR) {
            VERIFY(diagnostic.loc.file == unit.display_name);
            VERIFY(diagnostic.loc.line == 2);
        }
    }
    return 0;
}
