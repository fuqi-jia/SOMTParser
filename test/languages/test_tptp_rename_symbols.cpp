#include "../../languages/tptp/src/rename_symbols.h"
#include "test_helpers.h"

#include <iostream>
#include <unordered_map>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
using SOMTParser::Lang::detail::TptpSymbolRenamer;
using SOMTParser::Lang::detail::tptpSignatureKey;

int main() {
    const H::Sort boolean = H::Sort::boolean();
    const H::Sort integer = H::Sort::integer();

    // With no applicable mapping, return the original whole formula and nodes.
    {
        H::ExprPtr atom = H::mkApply("p", boolean, {});
        H::ExprPtr root = H::mkOp(H::Op::NOT, {atom});
        const std::unordered_map<std::string, std::string> targets = {
            {tptpSignatureKey("q", 0), "renamed_q"}
        };
        const std::unordered_map<std::string, H::Sort> sorts;
        TptpSymbolRenamer renamer(targets, sorts);
        H::ExprPtr rewritten = renamer.apply(root);
        VERIFY(rewritten == root);
        VERIFY(rewritten->args[0] == atom);
    }

    // A local rename copies only the path to the changed application. The
    // untouched sibling remains shared with the original formula.
    {
        H::ExprPtr untouched = H::mkApply("keep", boolean, {});
        H::ExprPtr changed = H::mkApply("quoted name", boolean, {});
        H::ExprPtr root = H::mkOp(H::Op::AND, {untouched, changed});
        const std::unordered_map<std::string, std::string> targets = {
            {tptpSignatureKey("quoted name", 0), "tptp$symbol$71756f746564206e616d65$0"}
        };
        const std::unordered_map<std::string, H::Sort> sorts;
        TptpSymbolRenamer renamer(targets, sorts);
        H::ExprPtr rewritten = renamer.apply(root);
        VERIFY(rewritten != root);
        VERIFY(rewritten->args[0] == untouched);
        VERIFY(rewritten->args[1] != changed);
        VERIFY(rewritten->args[1]->name == "tptp$symbol$71756f746564206e616d65$0");
        VERIFY(H::sameSort(rewritten->sort, root->sort));
        VERIFY(H::sameSort(rewritten->args[1]->sort, changed->sort));
    }

    // Shared input subexpressions are visited once and stay shared after a
    // change, including across two parent edges.
    {
        H::ExprPtr shared = H::mkApply("f", integer, {});
        H::ExprPtr root = H::mkOp(H::Op::EQ, {shared, shared});
        const std::unordered_map<std::string, std::string> targets = {
            {tptpSignatureKey("f", 0), "renamed_f"}
        };
        const std::unordered_map<std::string, H::Sort> sorts;
        TptpSymbolRenamer renamer(targets, sorts);
        H::ExprPtr rewritten = renamer.apply(root);
        VERIFY(rewritten != root);
        VERIFY(rewritten->args[0] == rewritten->args[1]);
        VERIFY(rewritten->args[0] != shared);
        VERIFY(rewritten->args[0]->name == "renamed_f");
    }

    // A deep chain of diamonds is traversed once per shared node, not once per
    // expanded path. A no-op mapping must leave the entire DAG intact.
    {
        constexpr std::size_t depth = 256;
        H::ExprPtr root = H::mkApply("p", boolean, {});
        for (std::size_t i = 0; i < depth; ++i) {
            root = H::mkOp(H::Op::AND, {root, root});
        }
        const std::unordered_map<std::string, std::string> targets = {
            {tptpSignatureKey("absent", 0), "still_absent"}
        };
        const std::unordered_map<std::string, H::Sort> sorts;
        TptpSymbolRenamer renamer(targets, sorts);
        H::ExprPtr rewritten = renamer.apply(root);
        VERIFY(rewritten == root);
        VERIFY(renamer.traversedNodes() == depth + 1);
    }

    // Symbol identity includes arity: rewriting f/1 leaves f/0 untouched.
    {
        H::ExprPtr nullary = H::mkApply("f", integer, {});
        H::ExprPtr argument = H::mkInt(1);
        H::ExprPtr unary = H::mkApply("f", integer, {argument});
        const std::unordered_map<std::string, std::string> targets = {
            {tptpSignatureKey("f", 1), "f_unary"}
        };
        const std::unordered_map<std::string, H::Sort> sorts;
        TptpSymbolRenamer renamer(targets, sorts);
        H::ExprPtr renamed_nullary = renamer.apply(nullary);
        H::ExprPtr renamed_unary = renamer.apply(unary);
        VERIFY(renamed_nullary == nullary);
        VERIFY(renamed_unary != unary && renamed_unary->name == "f_unary");
        VERIFY(renamed_unary->args[0] == argument);
    }

    // Type information is updated from the same original-signature key as the
    // name, so a later TFF declaration can repair earlier default typing.
    {
        H::ExprPtr application = H::mkApply("typed_later", boolean, {});
        const std::unordered_map<std::string, std::string> targets;
        const std::unordered_map<std::string, H::Sort> sorts = {
            {tptpSignatureKey("typed_later", 0), integer}
        };
        TptpSymbolRenamer renamer(targets, sorts);
        H::ExprPtr rewritten = renamer.apply(application);
        VERIFY(rewritten != application);
        VERIFY(rewritten->name == application->name);
        VERIFY(H::sameSort(rewritten->sort, integer));
    }

    // Symbol rewriting does not rename binders or BOUND_VAR occurrences, even
    // when two nested quantifiers deliberately reuse the same spelling.
    {
        H::ExprPtr x = H::mkBoundVar("X", integer);
        H::ExprPtr app = H::mkApply("quoted name", integer, {x});
        H::ExprPtr inner = H::mkForall({H::Binder{"X", integer}}, app);
        H::ExprPtr outer = H::mkForall({H::Binder{"X", integer}}, inner);
        const std::unordered_map<std::string, std::string> targets = {
            {tptpSignatureKey("quoted name", 1), "renamed_quoted_name"},
            {tptpSignatureKey("X", 1), "must_not_touch_bound_var"}
        };
        const std::unordered_map<std::string, H::Sort> sorts;
        TptpSymbolRenamer renamer(targets, sorts);
        H::ExprPtr rewritten = renamer.apply(outer);
        VERIFY(rewritten != outer);
        VERIFY(rewritten->binders.size() == 1 && rewritten->binders[0].name == "X");
        const H::ExprPtr& new_inner = rewritten->args[0];
        VERIFY(new_inner->binders.size() == 1 && new_inner->binders[0].name == "X");
        const H::ExprPtr& new_app = new_inner->args[0];
        VERIFY(new_app->name == "renamed_quoted_name");
        VERIFY(new_app->args[0]->kind == H::ExprKind::BOUND_VAR);
        VERIFY(new_app->args[0]->name == "X");
    }

    std::cout << "TPTP persistent symbol rewrite checks passed\n";
}
