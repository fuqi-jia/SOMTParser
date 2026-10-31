#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <memory>
#include <string>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

int main() {
    {
        // A source gate can be an integer or an array, without being an
        // assertion. Sharing it between roots must not add a constraint.
        H::ConstraintModel context;
        const auto array_sort = H::Sort::array(H::Sort::integer(), H::Sort::bitvec(8));
        context.decls.push_back({"a", array_sort, {}, {}, {}});
        auto array = H::mkIdent("a", array_sort);
        auto integer = H::mkInt(3);
        std::vector<H::LocatedExpr> terms{{array, {}}, {integer, {}}, {array, {}}};
        U::Diagnostics diagnostics;
        VERIFY(H::typeCheckTerms(context, terms, diagnostics));
        VERIFY(!diagnostics.hasErrors());
        VERIFY(context.constraints.empty());
        VERIFY(terms[0].expression == array);
    }
    {
        // Checking every root retains errors in nodes unused by any output.
        H::ConstraintModel context;
        // Build deliberately malformed input without the checked factory.
        auto wrong_arity = std::make_shared<H::Expr>();
        wrong_arity->kind = H::ExprKind::OP;
        wrong_arity->op = H::Op::NOT;
        wrong_arity->sort = H::Sort::boolean();
        auto unknown = H::mkIdent("missing", H::Sort::integer());
        std::vector<H::LocatedExpr> terms{
            {H::mkBool(true), {}},
            {wrong_arity, {"gates.btor2", 7, 1}},
            {unknown, {"gates.btor2", 9, 1}},
        };
        U::Diagnostics diagnostics;
        VERIFY(!H::typeCheckTerms(context, terms, diagnostics));
        bool arity_location = false, identifier_location = false;
        for (const auto& diagnostic : diagnostics.all()) {
            if (diagnostic.loc.file == "gates.btor2") {
                arity_location |= diagnostic.loc.line == 7;
                identifier_location |= diagnostic.loc.line == 9;
            }
        }
        VERIFY(arity_location && identifier_location);
    }
    {
        // A common source name must keep precise per-root locations. Explicit
        // root and expression locations take precedence, as in ordinary checks.
        H::ConstraintModel context;
        auto intrinsic = H::mkIdent("intrinsic_missing", H::Sort::integer(),
                                    {"included.hir", 31, 4});
        std::vector<H::LocatedExpr> terms{
            {H::mkIdent("first_missing", H::Sort::integer()), {"", 7, 2}},
            {H::mkIdent("second_missing", H::Sort::integer()), {"", 9, 3}},
            {H::mkIdent("explicit_missing", H::Sort::integer()), {"explicit.hir", 11, 5}},
            {intrinsic, {"", 13, 6}},
        };
        U::Diagnostics diagnostics;
        VERIFY(!H::typeCheckTerms(context, terms, diagnostics, "shared.btor2"));
        VERIFY(diagnostics.all().size() == 4);
        const std::vector<U::SourceLoc> expected{
            {"shared.btor2", 7, 2}, {"shared.btor2", 9, 3},
            {"explicit.hir", 11, 5}, {"included.hir", 31, 4},
        };
        for (std::size_t i = 0; i < expected.size(); ++i) {
            VERIFY(diagnostics.all()[i].loc.file == expected[i].file);
            VERIFY(diagnostics.all()[i].loc.line == expected[i].line);
            VERIFY(diagnostics.all()[i].loc.column == expected[i].column);
        }
        VERIFY(terms[0].loc.file.empty());
        VERIFY(terms[1].loc.file.empty());
    }
    {
        // A successful quantified use does not validate the same node outside
        // its binder, nor under a binder with a different sort.
        H::ConstraintModel context;
        auto body = H::mkBoundVar("q", H::Sort::boolean());
        auto good = H::mkForall({H::Binder{"q", H::Sort::boolean()}}, body);
        auto wrong = H::mkForall({H::Binder{"q", H::Sort::integer()}}, body);
        U::Diagnostics unbound;
        VERIFY(!H::typeCheckTerms(context,
            {{good, {}}, {body, {"scope.hir", 33, 2}}}, unbound));
        VERIFY(unbound.all().back().loc.file == "scope.hir");
        VERIFY(unbound.all().back().loc.line == 33);
        U::Diagnostics mismatch;
        VERIFY(!H::typeCheckTerms(context, {{good, {}}, {wrong, {}}}, mismatch));
        U::Diagnostics accepted;
        VERIFY(H::typeCheckTerms(context, {{good, {}}, {good, {}}}, accepted));
    }
    {
        // Cache ownership ends with the call. Reusing the same expression
        // address with a changed declaration must be checked again.
        H::ConstraintModel context;
        context.decls.push_back({"x", H::Sort::integer(), {}, {}, {}});
        auto value = H::mkIdent("x", H::Sort::integer());
        std::vector<H::LocatedExpr> terms{{value, {}}};
        U::Diagnostics first;
        VERIFY(H::typeCheckTerms(context, terms, first));
        context.decls[0].sort = H::Sort::boolean();
        U::Diagnostics changed;
        VERIFY(!H::typeCheckTerms(context, terms, changed));
    }
    {
        // The surrounding model is still validated, even for an empty batch.
        H::ConstraintModel context;
        context.constraints.push_back({H::mkInt(1)});
        U::Diagnostics diagnostics;
        VERIFY(!H::typeCheckTerms(context, {}, diagnostics));
        VERIFY(diagnostics.hasErrors());
    }
    {
        H::ConstraintModel context;
        U::Diagnostics diagnostics;
        VERIFY(!H::typeCheckTerms(context, {{nullptr, {"null.hir", 5, 1}}}, diagnostics));
        VERIFY(diagnostics.all().back().loc.file == "null.hir");
    }
    {
        auto cyclic = std::make_shared<H::Expr>();
        cyclic->kind = H::ExprKind::OP;
        cyclic->op = H::Op::NOT;
        cyclic->sort = H::Sort::boolean();
        cyclic->args.push_back(cyclic);
        U::Diagnostics diagnostics;
        const bool accepted = H::typeCheckTerms({}, {{cyclic, {}}}, diagnostics);
        cyclic->args.clear();
        VERIFY(!accepted);
        VERIFY(diagnostics.firstErrorCode() == U::ErrorCode::E_INTERNAL);
    }
    {
        // Every gate is a root and also part of later roots. Resetting the
        // cache per root turns this linear-sized source DAG into quadratic
        // validation work. All roots must remain checked, including the last.
        H::ConstraintModel context;
        context.decls.push_back({"b", H::Sort::boolean(), {}, {}, {}});
        std::vector<H::LocatedExpr> terms;
        terms.reserve(20002);
        terms.push_back({H::mkIdent("b", H::Sort::boolean()), {}});
        for (int i = 0; i < 20000; ++i) {
            terms.push_back({H::mkOp(H::Op::NOT, {terms.back().expression}), {}});
        }
        U::Diagnostics accepted;
        VERIFY(H::typeCheckTerms(context, terms, accepted));
        terms.push_back({H::mkOp(H::Op::NOT, {H::mkInt(1)}), {"last.btor2", 20002, 1}});
        U::Diagnostics rejected;
        const bool bad_accepted = H::typeCheckTerms(context, terms, rejected);
        // Release parents before children to keep teardown independent of
        // recursive shared_ptr destruction on a deep, valid DAG.
        for (auto it = terms.rbegin(); it != terms.rend(); ++it) { it->expression.reset(); }
        VERIFY(!bad_accepted);
        VERIFY(rejected.all().back().loc.file == "last.btor2");
    }
    return 0;
}
