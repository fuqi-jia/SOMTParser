#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <string>
#include <vector>

using namespace SOMTParser;
namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

static void numericContext(const std::string& expression) {
    auto parser = newParser();
    VERIFY(parser->parseStr("(set-logic QF_LIRA)(declare-const p Bool)"
        "(declare-const r Real)(declare-const i Int)(assert (= " + expression + " r))(check-sat)"));
    Lower::ParserToHir lift(parser);
    H::ConstraintModel model;
    U::Diagnostics diagnostics;
    VERIFY(lift.lift(model, diagnostics));
    VERIFY(H::typeCheck(model, diagnostics));
    VERIFY(!diagnostics.hasErrors());
    auto restored = newParser();
    Lower::HirToParser lower(restored);
    U::TranslationReport report;
    VERIFY(lower.lower(model, report, diagnostics));
    VERIFY(restored->getAssertions().size() == 1);
}

int main() {
    // A linear chain that previously overflowed liftExpr/liftNumericChild.
    // The alternate branches prevent the native simplifier from cancelling it.
    auto parser = newParser();
    auto p = parser->mkVarBool("p");
    auto q = parser->mkVarBool("q");
    auto root = p;
    constexpr std::size_t depth = 12000;
    for (std::size_t i = 0; i < depth; ++i) {
        root = parser->mkIte(p, root, q);
    }
    std::vector<H::ExprPtr> keepalive;
    {
        Lower::ParserToHir lift(parser);
        U::Diagnostics diagnostics;
        auto term = lift.liftExpr(root, diagnostics);
        VERIFY(term != nullptr);
        VERIFY(!diagnostics.hasErrors());
        std::size_t observed = 0;
        auto current = term;
        while (current->kind == H::ExprKind::OP && current->op == H::Op::ITE) {
            VERIFY(current->args.size() == 3);
            keepalive.push_back(current);
            current = current->args[1];
            ++observed;
        }
        VERIFY(observed == depth);
        // Shared native terms must remain shared HIR, not be expanded per path.
        VERIFY(lift.liftExpr(root, diagnostics).get() == term.get());
    }
    for (auto& expression : keepalive) { expression.reset(); }

    numericContext("(ite p 0 r)");
    numericContext("(ite p r 0)");
    numericContext("(ite p i r)");
    numericContext("(ite p 0 (ite p 1 r))");
    numericContext("(ite p 0 1)");
    numericContext("(ite p (ite p 0 1) r)");

    // Explicit Int/Real embedding is local to the SMT frontend. Ill-typed HIR
    // still violates the unchanged type checker contract.
    H::ConstraintModel invalid;
    invalid.decls.push_back({"b", H::Sort::boolean(), {}, {}, {}});
    invalid.constraints.push_back({H::mkOp(H::Op::EQ, {
        H::mkOp(H::Op::ITE, {H::mkIdent("b", H::Sort::boolean()), H::mkInt(1), H::mkReal("1.0")}),
        H::mkReal("1.0")})});
    U::Diagnostics mismatch;
    VERIFY(!H::typeCheck(invalid, mismatch));

    // Scope-sensitive memoization must not capture an outer let value under a
    // same-named inner quantifier.
    auto scoped = newParser();
    VERIFY(scoped->parseStr("(assert (forall ((x Int)) (let ((a x))"
        "(forall ((x Int)) (= a x)))))(assert true)"));
    Lower::ParserToHir scoped_lift(scoped);
    H::ConstraintModel scoped_model;
    U::Diagnostics scoped_diagnostics;
    VERIFY(scoped_lift.lift(scoped_model, scoped_diagnostics));
    VERIFY(H::typeCheck(scoped_model, scoped_diagnostics));
    return 0;
}
