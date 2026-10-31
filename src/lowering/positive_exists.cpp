#include "somtparser/lowering/positive_exists.h"

#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>

namespace SOMTParser::Lower {
namespace H = Uir::Hir;
namespace {

std::string canonical(const std::string& name) {
    return name.size() >= 2 && name.front() == '|' && name.back() == '|'
        ? name.substr(1, name.size() - 2) : name;
}

using Bindings = std::unordered_map<std::string, H::ExprPtr>;
struct Scope {
    Bindings bindings;
    std::unordered_map<const H::Expr*, H::ExprPtr> memo;
};

// Replace BOUND_VAR, never IDENT: a free global may share a binder's spelling.
// Each scope has its own DAG memo. Inner quantifiers shadow their own binders.
// Explicit traversal avoids C++ stack growth for long CP conjunctions.
H::ExprPtr substitute(const H::ExprPtr& root, Bindings bindings) {
    struct Frame { H::ExprPtr term; std::size_t scope; bool finish; std::size_t inner; };
    std::vector<Scope> scopes;
    scopes.push_back({std::move(bindings), {}});
    std::vector<Frame> pending{{root, 0, false, 0}};
    while (!pending.empty()) {
        auto frame = std::move(pending.back()); pending.pop_back();
        const auto& term = frame.term;
        if (scopes[frame.scope].memo.count(term.get())) { continue; }
        if (!frame.finish) {
            const auto& env = scopes[frame.scope].bindings;
            if (term->kind == H::ExprKind::BOUND_VAR) {
                const auto it = env.find(term->name);
                scopes[frame.scope].memo.emplace(term.get(), it == env.end() ? term : it->second);
                continue;
            }
            if (term->args.empty() || env.empty()) {
                scopes[frame.scope].memo.emplace(term.get(), term); continue;
            }
            auto inner = frame.scope;
            if (term->kind == H::ExprKind::FORALL || term->kind == H::ExprKind::EXISTS) {
                auto nested = env;
                for (const auto& binder : term->binders) { nested.erase(binder.name); }
                if (nested.size() != env.size()) {
                    inner = scopes.size(); scopes.push_back({std::move(nested), {}});
                }
            }
            pending.push_back({term, frame.scope, true, inner});
            for (auto it = term->args.rbegin(); it != term->args.rend(); ++it) {
                pending.push_back({*it, inner, false, 0});
            }
        } else {
            auto children = term->args;
            bool changed = false;
            for (auto& child : children) {
                auto replacement = scopes[frame.inner].memo.at(child.get());
                changed |= replacement != child;
                child = std::move(replacement);
            }
            auto result = term;
            if (changed) {
                auto copy = std::make_shared<H::Expr>(*term);
                copy->args = std::move(children); result = std::move(copy);
            }
            scopes[frame.scope].memo.emplace(term.get(), std::move(result));
        }
    }
    return scopes[0].memo.at(root.get());
}

} // namespace

std::vector<ExistentialWitness> liftPositiveExists(H::ConstraintModel& model) {
    // Memoize eligibility, not rewritten witnesses. This skips shared AND
    // DAGs with no positive exists even when they sit beside a lifted term.
    // Retaining the key prevents pointer reuse for substituted temporary DAGs.
    std::unordered_map<H::ExprPtr, bool> eligible;
    const auto has_witness = [&](const H::ExprPtr& root) {
        std::vector<std::pair<H::ExprPtr, bool>> stack{{root, false}};
        while (!stack.empty()) {
            auto frame = std::move(stack.back()); stack.pop_back();
            const auto& term = frame.first;
            if (eligible.count(term)) { continue; }
            if (term->kind == H::ExprKind::EXISTS) {
                eligible.emplace(term, true);
            } else if (term->kind != H::ExprKind::OP || term->op != H::Op::AND) {
                eligible.emplace(term, false);
            } else if (!frame.second) {
                stack.emplace_back(term, true);
                for (const auto& child : term->args) { stack.emplace_back(child, false); }
            } else {
                bool found = false;
                for (const auto& child : term->args) { found |= eligible.at(child); }
                eligible.emplace(term, found);
            }
        }
        return eligible.at(root);
    };
    bool needed = false;
    for (const auto& constraint : model.constraints) {
        if (!constraint.soft && constraint.formula) { needed |= has_witness(constraint.formula); }
    }
    if (!needed) { return {}; }
    std::unordered_set<std::string> taken;
    std::vector<H::ExprPtr> pending;
    for (const auto& decl : model.decls) {
        taken.insert(canonical(decl.name));
        pending.push_back(decl.lower_bound); pending.push_back(decl.upper_bound);
    }
    for (const auto& fun : model.funs) {
        taken.insert(canonical(fun.name)); pending.push_back(fun.body);
        for (const auto& binder : fun.binders) { taken.insert(canonical(binder.name)); }
    }
    for (const auto& datatype : model.datatypes) {
        taken.insert(canonical(datatype.name));
        for (const auto& constructor : datatype.constructors) {
            taken.insert(canonical(constructor.name));
            for (const auto& selector : constructor.selectors) { taken.insert(canonical(selector.name)); }
        }
    }
    for (const auto& sort : model.uninterpreted_sorts) { taken.insert(canonical(sort.name)); }
    for (const auto& constraint : model.constraints) { pending.push_back(constraint.formula); }
    for (const auto& objective : model.objectives) { pending.push_back(objective.term); }
    std::unordered_set<const H::Expr*> seen;
    while (!pending.empty()) {
        auto term = std::move(pending.back()); pending.pop_back();
        if (!term || !seen.insert(term.get()).second) { continue; }
        if (!term->name.empty()) { taken.insert(canonical(term->name)); }
        for (const auto& binder : term->binders) { taken.insert(canonical(binder.name)); }
        pending.insert(pending.end(), term->args.begin(), term->args.end());
    }
    std::size_t next_name = 0, next_quantifier = 0;
    const auto fresh = [&]() {
        for (;;) {
            const auto name = "!somt_exists_" + std::to_string(next_name++);
            bool reserved = taken.count(name) != 0;
            for (const auto& range : model.bool_var_ranges) { reserved |= range.contains(name); }
            for (const auto& range : model.scalar_var_ranges) { reserved |= range.contains(name); }
            if (!reserved) { taken.insert(name); return name; }
        }
    };
    std::vector<ExistentialWitness> witnesses;
    struct Frame { H::ExprPtr term; bool finish; std::size_t first; };
    for (std::size_t i = 0; i < model.constraints.size(); ++i) {
        auto& constraint = model.constraints[i];
        if (constraint.soft || !constraint.formula) { continue; }
        std::vector<Frame> stack{{constraint.formula, false, 0}};
        std::vector<H::ExprPtr> results;
        while (!stack.empty()) {
            auto frame = std::move(stack.back()); stack.pop_back();
            const auto& term = frame.term;
            if (!frame.finish && !has_witness(term)) {
                results.push_back(term); continue;
            }
            if (frame.finish) {
                std::vector<H::ExprPtr> children(results.begin() + frame.first, results.end());
                results.resize(frame.first);
                auto result = term;
                if (children != term->args) {
                    auto copy = std::make_shared<H::Expr>(*term);
                    copy->args = std::move(children); result = std::move(copy);
                }
                results.push_back(std::move(result));
            } else if (term->kind == H::ExprKind::EXISTS) {
                if (term->args.size() != 1 || term->binders.empty()) {
                    throw std::logic_error("positive exists requires a typed quantifier");
                }
                const auto quantifier = next_quantifier++;
                Bindings bindings;
                for (const auto& binder : term->binders) {
                    auto name = fresh();
                    model.decls.push_back({name, binder.sort, {}, {}, term->loc, true});
                    witnesses.push_back({i, quantifier, binder.name, name, binder.sort});
                    bindings.emplace(binder.name, H::mkIdent(name, binder.sort, term->loc));
                }
                stack.push_back({substitute(term->args[0], std::move(bindings)), false, 0});
            } else if (term->kind == H::ExprKind::OP && term->op == H::Op::AND) {
                stack.push_back({term, true, results.size()});
                for (auto it = term->args.rbegin(); it != term->args.rend(); ++it) {
                    stack.push_back({*it, false, 0});
                }
            } else {
                results.push_back(term);
            }
        }
        if (results.size() != 1) { throw std::logic_error("positive exists traversal imbalance"); }
        constraint.formula = std::move(results.back());
    }
    return witnesses;
}

} // namespace SOMTParser::Lower
