#pragma once

#include "somtparser/hir/hir.h"

#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang::detail {

// These analyses run on immutable HIR DAGs. Keep their worklists independent
// of parser frames, and memoize shared subexpressions rather than following
// every incoming edge through the same suffix again.
inline bool expressionReferencesDecision(
    const Uir::Hir::ExprPtr& expression,
    const std::unordered_map<std::string, Uir::Hir::Sort>& scope) {
    namespace H = Uir::Hir;
    std::vector<const H::Expr*> pending;
    if (expression) pending.push_back(expression.get());
    std::unordered_set<const H::Expr*> seen;
    while (!pending.empty()) {
        const auto* current = pending.back();
        pending.pop_back();
        if (!current || !seen.insert(current).second) continue;
        if (current->kind == H::ExprKind::IDENT && scope.count(current->name)) return true;
        for (auto child = current->args.rbegin(); child != current->args.rend(); ++child)
            pending.push_back(child->get());
    }
    return false;
}

inline std::string enumTypeOfExpression(
    const Uir::Hir::ExprPtr& expression,
    const std::unordered_map<Uir::Hir::ExprPtr, std::string>& explicit_types,
    const std::unordered_map<std::string, std::string>& symbol_types) {
    namespace H = Uir::Hir;
    const auto leaf = [&](const H::ExprPtr& e) -> std::optional<std::string> {
        if (!e || e->sort.kind != H::SortKind::INT) return std::string();
        const auto explicit_type = explicit_types.find(e);
        if (explicit_type != explicit_types.end()) return explicit_type->second;
        const auto symbol_type = [&](const std::string& name) {
            const auto symbol = symbol_types.find(name);
            return symbol == symbol_types.end() ? std::string() : symbol->second;
        };
        if (e->kind == H::ExprKind::IDENT) return symbol_type(e->name);
        if (e->kind != H::ExprKind::OP) return std::string();
        if (e->op == H::Op::SELECT && !e->args.empty()
            && e->args[0]->kind == H::ExprKind::IDENT) return symbol_type(e->args[0]->name);
        if (e->op == H::Op::ITE && e->args.size() == 3) return std::nullopt;
        return std::string();
    };
    // The common annotated/symbol/scalar case still needs no worklist storage.
    if (auto type = leaf(expression)) return *type;
    struct Frame { const H::Expr* expression; std::size_t next = 1; };
    std::vector<Frame> pending{{expression.get(), 1}};
    std::unordered_map<const H::Expr*, std::string> types;
    while (!pending.empty()) {
        auto& frame = pending.back();
        if (frame.next != 3) {
            const auto& child = frame.expression->args[frame.next++];
            if (types.count(child.get())) continue;
            if (auto type = leaf(child)) types.emplace(child.get(), std::move(*type));
            else pending.push_back({child.get(), 1});
            continue;
        }
        const auto& yes = types.at(frame.expression->args[1].get());
        const auto& no = types.at(frame.expression->args[2].get());
        types.emplace(frame.expression, yes == no ? yes : std::string());
        pending.pop_back();
    }
    return types.at(expression.get());
}

} // namespace SOMTParser::Lang::detail
