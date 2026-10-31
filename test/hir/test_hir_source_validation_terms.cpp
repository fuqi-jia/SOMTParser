#include "somtparser/translation/translate.h"
#include "test_helpers.h"

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

int main() {
    SOMTParser::TranslateOptions options;
    options.omt_dialect = SOMTParser::Lower::OmtDialect::Z3;
    H::ConstraintModel model;
    model.decls.push_back({"x", H::Sort::integer(), {}, {}, {}});
    auto x = H::mkIdent("x", H::Sort::integer());
    model.constraints.push_back({H::mkOp(H::Op::GE, {x, H::mkInt(0)})});
    const auto plain = SOMTParser::translate(model, options);
    VERIFY(plain.ok());
    {
        // False is checked, never asserted. No symbol or binder is exported.
        auto bound = H::mkBoundVar("source@only", H::Sort::integer());
        auto closed = H::mkForall({{"source@only", H::Sort::integer()}},
            H::mkOp(H::Op::EQ, {bound, bound}));
        std::vector<H::LocatedExpr> terms{
            {H::mkBool(false), {"empty.fold.body", 5, 2}},
            {closed, {"empty.fold.body", 6, 2}},
        };
        auto checked = SOMTParser::translate(model, options, terms);
        VERIFY(checked.ok());
        VERIFY(checked.toSmt2() == plain.toSmt2());
        VERIFY(checked.toSmt2().find("source@only") == std::string::npos);
        VERIFY(model.constraints.size() == 1);
        VERIFY(terms[0].expression->kind == H::ExprKind::LIT_BOOL);
    }
    {
        auto malformed = H::mkOp(H::Op::ADD, {H::mkBool(true), H::mkInt(1)});
        const auto checked = SOMTParser::translate(model, options,
            {{malformed, {"constraints[0].expr.body", 12, 7}}});
        VERIFY(!checked.ok());
        bool located = false;
        for (const auto& diagnostic : checked.diagnostics().all())
            located |= diagnostic.loc.file == "constraints[0].expr.body"
                && diagnostic.loc.line == 12 && diagnostic.loc.column == 7;
        VERIFY(located);
        VERIFY(SOMTParser::translate(model, options).ok());
    }
    {
        auto bound = H::mkBoundVar("q", H::Sort::boolean());
        auto closed = H::mkForall({{"q", H::Sort::boolean()}}, bound);
        VERIFY(SOMTParser::translate(model, options, {{closed, {}}}).ok());
        VERIFY(!SOMTParser::translate(model, options,
            {{closed, {}}, {bound, {"unbound-source", 1, 1}}}).ok());
        auto wrong_scope = H::mkForall({{"q", H::Sort::integer()}}, bound);
        VERIFY(!SOMTParser::translate(model, options, {{wrong_scope, {}}}).ok());
    }
    {
        H::ConstraintModel malformed = model;
        malformed.constraints.push_back({H::mkInt(3)});
        VERIFY(!SOMTParser::translate(malformed, options,
            {{H::mkBool(true), {}}}).ok());
    }
    return 0;
}
