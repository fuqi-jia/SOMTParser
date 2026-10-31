#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <memory>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

// Keep test teardown independent of recursive shared_ptr destruction. These
// expressions are intentionally unshared while the checker traverses them.
static void releaseChain(H::ConstraintModel& model, H::ExprPtr& root) {
    std::vector<H::ExprPtr> parents_first;
    for (auto current = root; current; current = current->args.empty() ? nullptr : current->args[0]) {
        parents_first.push_back(current);
    }
    model.constraints.clear();
    root.reset();
    for (auto& expression : parents_first) { expression.reset(); }
}

int main() {
    {
        H::ConstraintModel model;
        model.decls.push_back({"b", H::Sort::boolean(), {}, {}, {}});
        auto root = H::mkIdent("b", H::Sort::boolean());
        for (int i = 0; i < 20000; ++i) { root = H::mkOp(H::Op::NOT, {root}); }
        model.constraints.push_back({root});
        U::Diagnostics diagnostics;
        VERIFY(H::typeCheck(model, diagnostics));
        VERIFY(!diagnostics.hasErrors());
        releaseChain(model, root);
    }
    {
        H::ConstraintModel model;
        model.decls.push_back({"x", H::Sort::integer(), {}, {}, {}});
        auto root = H::mkIdent("x", H::Sort::integer());
        const auto one = H::mkInt(1);
        for (int i = 0; i < 20000; ++i) { root = H::mkOp(H::Op::ADD, {root, one}); }
        root = H::mkOp(H::Op::GE, {root, H::mkInt(0)});
        model.constraints.push_back({root});
        U::Diagnostics diagnostics;
        VERIFY(H::typeCheck(model, diagnostics));
        releaseChain(model, root);
    }
    {
        H::ConstraintModel model;
        auto body = H::mkBoundVar("q", H::Sort::boolean());
        for (int i = 0; i < 3000; ++i) { body = H::mkOp(H::Op::NOT, {body}); }
        auto good = H::mkForall({H::Binder{"q", H::Sort::boolean()}}, body);
        model.constraints.push_back({good});
        U::Diagnostics accepted;
        VERIFY(H::typeCheck(model, accepted));
        auto wrong_scope = H::mkForall({H::Binder{"q", H::Sort::integer()}}, body);
        model.constraints = {{H::mkOp(H::Op::AND, {good, wrong_scope})}};
        U::Diagnostics mismatch;
        VERIFY(!H::typeCheck(model, mismatch));
        VERIFY(mismatch.hasErrors());
        // A cached body from the quantified root must not leak into a later
        // unbound root, and inherited source locations must survive the stack.
        model.constraints = {{good}, {body}};
        model.constraints.back().loc = U::SourceLoc{"deep-input.tlsf", 33, 5};
        U::Diagnostics unbound;
        VERIFY(!H::typeCheck(model, unbound));
        VERIFY(unbound.hasErrors());
        VERIFY(unbound.all().back().loc.file == "deep-input.tlsf");
        good.reset();
        wrong_scope.reset();
        releaseChain(model, body);
    }
    {
        auto cyclic = std::make_shared<H::Expr>();
        cyclic->kind = H::ExprKind::OP;
        cyclic->op = H::Op::NOT;
        cyclic->sort = H::Sort::boolean();
        cyclic->args.push_back(cyclic);
        H::ConstraintModel model;
        model.constraints.push_back({cyclic});
        U::Diagnostics diagnostics;
        const bool accepted = H::typeCheck(model, diagnostics);
        cyclic->args.clear();
        VERIFY(!accepted);
        VERIFY(diagnostics.firstErrorCode() == U::ErrorCode::E_INTERNAL);
    }
    {
        // Wide signatures retain full nested sorts, even with long names and
        // after a subsequent call receives a relocated or modified model.
        H::ConstraintModel model;
        const auto nested = H::Sort::array(H::Sort::integer(), H::Sort::bitvec(17));
        for (int i = 0; i < 4096; ++i) {
            const auto name = "long_source_declaration_for_borrowed_signature_" + std::to_string(i);
            model.decls.push_back({name, nested, {}, {}, {}});
        }
        const auto name = model.decls.back().name;
        const auto value = H::mkIdent(name, nested);
        model.constraints.push_back({H::mkOp(H::Op::EQ, {value, value})});
        U::Diagnostics accepted;
        VERIFY(H::typeCheck(model, accepted));
        H::ConstraintModel changed = model;
        changed.decls.back().sort = H::Sort::array(H::Sort::integer(), H::Sort::bitvec(18));
        U::Diagnostics mismatch;
        VERIFY(!H::typeCheck(changed, mismatch));
        VERIFY(mismatch.hasErrors());
        U::Diagnostics original;
        VERIFY(H::typeCheck(model, original));
        changed = model;
        changed.decls.push_back({name, H::Sort::integer(), {}, {}, {"wide.hir", 17, 2}});
        U::Diagnostics duplicate;
        VERIFY(!H::typeCheck(changed, duplicate));
        VERIFY(duplicate.all().front().message.find("declared more than once") != std::string::npos);
        VERIFY(duplicate.all().front().loc.file == "wide.hir");
    }
    return 0;
}
