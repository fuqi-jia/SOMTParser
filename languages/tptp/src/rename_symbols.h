#pragma once

#include "somtparser/hir/hir.h"

#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace SOMTParser::Lang::detail {

namespace H = Uir::Hir;

inline std::string tptpSignatureKey(const std::string& name, std::size_t arity) {
    return name + std::string(1, '\x1e') + std::to_string(arity);
}

/** Persistent, memoized symbol rewriting for the TPTP HIR expression DAG.
 *
 * Unchanged subtrees are returned by identity. Changed paths are copied only
 * once, and repeated references to the same input node share the same output
 * node. Binding nodes and variable names are never rewritten; only APPLY
 * symbols and their declared result sorts are subject to the signature map.
 */
class TptpSymbolRenamer {
public:
    TptpSymbolRenamer(
        const std::unordered_map<std::string, std::string>& targets,
        const std::unordered_map<std::string, H::Sort>& result_sorts)
        : targets_(targets), result_sorts_(result_sorts) {}

    H::ExprPtr apply(const H::ExprPtr& expression) {
        if (!expression || (targets_.empty() && result_sorts_.empty())) {
            return expression;
        }
        const auto prior = memo_.find(expression.get());
        if (prior != memo_.end()) { return prior->second; }
        ++traversed_nodes_;
        // A unique node is reached only once through its owning edge, so it
        // does not need a memo entry. Shared nodes do: caching even an
        // unchanged shared node prevents repeated (and, for diamond chains,
        // exponential) traversal while keeping the cache proportional to the
        // shared part of the DAG rather than the entire tree.
        const bool shared = expression.use_count() > 1;

        std::vector<H::ExprPtr> rewritten_args;
        bool args_changed = false;
        for (std::size_t i = 0; i < expression->args.size(); ++i) {
            const H::ExprPtr& argument = expression->args[i];
            H::ExprPtr rewritten = apply(argument);
            if (rewritten != argument) {
                if (!args_changed) {
                    rewritten_args.reserve(expression->args.size());
                    rewritten_args.insert(rewritten_args.end(), expression->args.begin(),
                                          expression->args.begin() + i);
                    args_changed = true;
                }
                rewritten_args.push_back(std::move(rewritten));
            } else if (args_changed) {
                rewritten_args.push_back(argument);
            }
        }

        const std::string* target_name = nullptr;
        const H::Sort* result_sort = nullptr;
        bool own_changed = false;
        if (expression->kind == H::ExprKind::APPLY) {
            const std::string key = tptpSignatureKey(expression->name,
                                                      expression->args.size());
            const auto target = targets_.find(key);
            if (target != targets_.end() && target->second != expression->name) {
                target_name = &target->second;
                own_changed = true;
            }
            const auto sort = result_sorts_.find(key);
            if (sort != result_sorts_.end()
                && !H::sameSort(sort->second, expression->sort)) {
                result_sort = &sort->second;
                own_changed = true;
            }
        }

        if (!own_changed && !args_changed) {
            if (shared) { memo_.emplace(expression.get(), expression); }
            return expression;
        }

        auto rewritten = std::make_shared<H::Expr>(*expression);
        if (args_changed) { rewritten->args = std::move(rewritten_args); }
        if (target_name) { rewritten->name = *target_name; }
        if (result_sort) { rewritten->sort = *result_sort; }
        H::ExprPtr result = std::move(rewritten);
        if (shared) { memo_.emplace(expression.get(), result); }
        return result;
    }

    std::size_t traversedNodes() const { return traversed_nodes_; }

private:
    const std::unordered_map<std::string, std::string>& targets_;
    const std::unordered_map<std::string, H::Sort>& result_sorts_;
    std::unordered_map<const H::Expr*, H::ExprPtr> memo_;
    std::size_t traversed_nodes_ = 0;
};

} // namespace SOMTParser::Lang::detail
