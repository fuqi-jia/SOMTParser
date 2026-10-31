#include "somtparser/hir/planning_derived.h"
#include "somtparser/hir/typecheck.h"

#include <functional>
#include <unordered_map>
#include <unordered_set>

namespace SOMTParser::Uir::Hir::Planning {
namespace {

using AtomMap = std::unordered_map<std::string, std::size_t>;

ExprPtr either(std::vector<ExprPtr> values) {
    std::vector<ExprPtr> kept;
    std::unordered_set<const Expr*> seen;
    for (auto& value : values) {
        if (value->kind == ExprKind::LIT_BOOL) {
            if (value->bool_value) { return value; }
        } else if (seen.insert(value.get()).second) {
            kept.push_back(std::move(value));
        }
    }
    if (kept.empty()) { return mkBool(false); }
    if (kept.size() == 1) { return kept.front(); }
    return mkOp(Op::OR, std::move(kept));
}

// One memo per layer: a shared source node is rewritten once at that layer.
ExprPtr replace(const ExprPtr& expression, const AtomMap& atoms,
                const std::vector<ExprPtr>& previous,
                std::unordered_map<const Expr*, ExprPtr>& memo) {
    const auto found = memo.find(expression.get());
    if (found != memo.end()) { return found->second; }
    if (expression->kind == ExprKind::IDENT) {
        const auto atom = atoms.find(expression->name);
        if (atom != atoms.end()) {
            return memo.emplace(expression.get(), previous[atom->second]).first->second;
        }
    }
    bool changed = false;
    std::vector<ExprPtr> arguments;
    for (const auto& arg : expression->args) {
        arguments.push_back(replace(arg, atoms, previous, memo));
        changed |= arguments.back() != arg;
    }
    ExprPtr result = expression;
    if (changed) {
        auto copy = std::make_shared<Expr>(*expression);
        copy->args = std::move(arguments);
        result = std::move(copy);
    }
    memo.emplace(expression.get(), result);
    return result;
}

struct Reads {
    std::set<std::size_t> derived;
    std::set<std::string> basic;
    std::set<std::string> functions;
};

bool analyze(const ExprPtr& expression, int polarity, const AtomMap& atoms,
             Reads& reads, std::set<std::string>& reserved,
             std::set<std::pair<const Expr*, int>>& seen,
             Diagnostics& diagnostics) {
    if (!seen.emplace(expression.get(), polarity).second) { return true; }
    for (const auto& binder : expression->binders) {
        reserved.insert(binder.name);
        if (atoms.count(binder.name)) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "a derived atom cannot be shadowed by a rule binder", expression->loc);
            return false;
        }
    }
    if (expression->kind == ExprKind::IDENT) {
        reserved.insert(expression->name);
        const auto derived = atoms.find(expression->name);
        if (derived != atoms.end()) {
            if (polarity <= 0) {
                diagnostics.error(ErrorCode::E_TYPE,
                    "derived atoms must occur positively in least-fixed-point rule bodies", expression->loc);
                return false;
            }
            reads.derived.insert(derived->second);
        } else { reads.basic.insert(expression->name); }
        return true;
    }
    if (expression->kind == ExprKind::APPLY) { reads.functions.insert(expression->name); }
    const auto visit = [&](const ExprPtr& child, int sign) {
        return analyze(child, sign, atoms, reads, reserved, seen, diagnostics);
    };
    if (expression->kind == ExprKind::FORALL || expression->kind == ExprKind::EXISTS) {
        return visit(expression->args[0], polarity);
    }
    if (expression->kind == ExprKind::OP) {
        if (expression->op == Op::AND || expression->op == Op::OR) {
            for (const auto& child : expression->args) {
                if (!visit(child, polarity)) { return false; }
            }
            return true;
        }
        if (expression->op == Op::NOT) { return visit(expression->args[0], -polarity); }
        if (expression->op == Op::IMPLIES) {
            return visit(expression->args[0], -polarity) && visit(expression->args[1], polarity);
        }
        if (expression->op == Op::ITE && expression->sort.kind == SortKind::BOOL) {
            return visit(expression->args[0], 0) && visit(expression->args[1], polarity)
                && visit(expression->args[2], polarity);
        }
        // Boolean equality to a literal is a positive/negative literal, not
        // a hidden non-monotone dependency. General equivalence is rejected.
        if (expression->op == Op::EQ && expression->args.size() == 2) {
            for (std::size_t i = 0; i < 2; ++i) {
                if (expression->args[i]->kind == ExprKind::LIT_BOOL) {
                    return visit(expression->args[1 - i],
                                 expression->args[i]->bool_value ? polarity : -polarity);
                }
            }
        }
    }
    for (const auto& child : expression->args) {
        if (!visit(child, 0)) { return false; }
    }
    return true;
}

} // namespace

std::optional<DerivedClosure> buildDerivedClosure(
    const ConstraintModel& context, const std::vector<ExprPtr>& atoms,
    const std::vector<DerivedRule>& rules, const std::string& prefix,
    Diagnostics& diagnostics) {
    AtomMap indices;
    std::set<std::string> reserved;
    std::vector<LocatedExpr> terms;
    for (std::size_t i = 0; i < atoms.size(); ++i) {
        const auto& atom = atoms[i];
        if (!atom || atom->kind != ExprKind::IDENT || atom->sort.kind != SortKind::BOOL
            || !indices.emplace(atom->name, i).second) {
            diagnostics.error(ErrorCode::E_TYPE, "derived universe requires distinct Bool identifiers");
            return std::nullopt;
        }
        terms.push_back({atom, atom->loc});
    }
    for (const auto& rule : rules) {
        if (rule.head >= atoms.size() || !rule.body || rule.body->sort.kind != SortKind::BOOL) {
            diagnostics.error(ErrorCode::E_TYPE, "derived rule requires a valid ground head and Bool body", rule.loc);
            return std::nullopt;
        }
        terms.push_back({rule.body, rule.loc});
    }
    // The caller can be assembling a model. Validate the complete signature
    // and rule roots without asserting or depending on unrelated constraints.
    ConstraintModel scope;
    scope.decls = context.decls;
    scope.funs = context.funs;
    scope.datatypes = context.datatypes;
    scope.uninterpreted_sorts = context.uninterpreted_sorts;
    scope.bool_var_ranges = context.bool_var_ranges;
    scope.scalar_var_ranges = context.scalar_var_ranges;
    if (!typeCheckTerms(scope, terms, diagnostics)) { return std::nullopt; }

    std::unordered_map<std::string, Reads> function_reads;
    for (const auto& function : context.funs) {
        reserved.insert(function.name);
        if (function.body) {
            Reads reads;
            std::set<std::pair<const Expr*, int>> seen;
            // Hidden global captures would evade the layer substitution.
            if (!analyze(function.body, 0, indices, reads, reserved, seen, diagnostics)) {
                return std::nullopt;
            }
            function_reads.emplace(function.name, std::move(reads));
        }
    }
    DerivedClosure result;
    result.rounds = atoms.size();
    result.base_dependencies.resize(atoms.size());
    result.base_function_dependencies.resize(atoms.size());
    std::vector<std::set<std::size_t>> dependencies(atoms.size());
    std::vector<std::vector<ExprPtr>> bodies(atoms.size());
    for (const auto& rule : rules) {
        Reads reads;
        std::set<std::pair<const Expr*, int>> seen;
        if (!analyze(rule.body, 1, indices, reads, reserved, seen, diagnostics)) { return std::nullopt; }
        std::vector<std::string> pending(reads.functions.begin(), reads.functions.end());
        std::set<std::string> visited;
        while (!pending.empty()) {
            const auto name = pending.back(); pending.pop_back();
            if (!visited.insert(name).second) { continue; }
            const auto found = function_reads.find(name);
            if (found == function_reads.end()) { continue; }
            reads.basic.insert(found->second.basic.begin(), found->second.basic.end());
            reads.functions.insert(found->second.functions.begin(), found->second.functions.end());
            pending.insert(pending.end(), found->second.functions.begin(), found->second.functions.end());
        }
        dependencies[rule.head].insert(reads.derived.begin(), reads.derived.end());
        result.base_dependencies[rule.head].insert(reads.basic.begin(), reads.basic.end());
        result.base_function_dependencies[rule.head].insert(reads.functions.begin(), reads.functions.end());
        bodies[rule.head].push_back(rule.body);
    }
    bool grew = true;
    while (grew) {
        grew = false;
        for (std::size_t head = 0; head < atoms.size(); ++head) {
            for (const auto dependency : dependencies[head]) {
                for (const auto& name : result.base_dependencies[dependency]) {
                    grew |= result.base_dependencies[head].insert(name).second;
                }
                for (const auto& name : result.base_function_dependencies[dependency]) {
                    grew |= result.base_function_dependencies[head].insert(name).second;
                }
            }
        }
    }
    for (const auto& declaration : context.decls) { reserved.insert(declaration.name); }
    for (const auto& objective : context.objectives) { reserved.insert(objective.name); }
    for (const auto& datatype : context.datatypes) {
        for (const auto& constructor : datatype.constructors) {
            reserved.insert(constructor.name);
            for (const auto& selector : constructor.selectors) { reserved.insert(selector.name); }
        }
    }
    const auto occupied = [&](const std::string& name) {
        if (reserved.count(name)) { return true; }
        for (const auto& range : context.bool_var_ranges) { if (range.contains(name)) { return true; } }
        for (const auto& range : context.scalar_var_ranges) { if (range.contains(name)) { return true; } }
        return false;
    };
    const std::string stem = prefix.empty() ? "__derived_lfp" : prefix;
    std::size_t serial = 0;
    result.values.assign(atoms.size(), mkBool(false));
    for (std::size_t layer = 0; layer < atoms.size(); ++layer) {
        std::unordered_map<const Expr*, ExprPtr> memo;
        std::vector<ExprPtr> next;
        for (std::size_t head = 0; head < atoms.size(); ++head) {
            std::vector<ExprPtr> alternatives{result.values[head]};
            for (const auto& body : bodies[head]) {
                alternatives.push_back(replace(body, indices, result.values, memo));
            }
            const auto value = either(std::move(alternatives));
            if (value->kind == ExprKind::LIT_BOOL || value == result.values[head]) {
                next.push_back(value);
                continue;
            }
            std::string name = stem + "_" + std::to_string(serial++);
            // Do not enumerate a huge compact declaration interval just to
            // find a fresh spelling. A non-numeric suffix leaves that interval.
            while (occupied(name)) { name += "_fresh"; }
            reserved.insert(name);
            VarDecl declaration;
            declaration.name = name;
            declaration.sort = Sort::boolean();
            declaration.auxiliary = true;
            result.declarations.push_back(std::move(declaration));
            const auto identifier = mkIdent(name, Sort::boolean());
            Constraint constraint;
            constraint.formula = mkOp(Op::EQ, {identifier, value});
            result.constraints.push_back(std::move(constraint));
            next.push_back(identifier);
        }
        result.values = std::move(next);
    }
    return result;
}

} // namespace SOMTParser::Uir::Hir::Planning
