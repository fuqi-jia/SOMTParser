#include "somtparser/hir/planning_numeric.h"
#include "somtparser/hir/typecheck.h"

#include <algorithm>
#include <map>
#include <set>
#include <unordered_set>

namespace SOMTParser::Uir::Hir::Planning {
namespace {

bool sortedAs(const ExprPtr& expression, SortKind sort) {
    return expression && expression->sort.kind == sort;
}

bool valueShape(const NumericValue& value, Diagnostics& diagnostics) {
    if (sortedAs(value.value, SortKind::REAL) && sortedAs(value.defined, SortKind::BOOL)) {
        return true;
    }
    diagnostics.error(ErrorCode::E_TYPE, "planning numeric value requires Real value and Bool definedness");
    return false;
}

bool conditionShape(const NumericCondition& value, Diagnostics& diagnostics) {
    if (sortedAs(value.value, SortKind::BOOL) && sortedAs(value.defined, SortKind::BOOL)) {
        return true;
    }
    diagnostics.error(ErrorCode::E_TYPE, "planning condition requires Bool value and definedness");
    return false;
}

ExprPtr logical(Op op, std::vector<ExprPtr> args) {
    if (args.empty()) { return mkBool(op == Op::AND); }
    if (args.size() == 1) { return args.front(); }
    return mkOp(op, std::move(args));
}

ExprPtr sum(std::vector<ExprPtr> terms) {
    if (terms.empty()) { return mkReal("0"); }
    if (terms.size() == 1) { return terms.front(); }
    return mkOp(Op::ADD, std::move(terms));
}

ExprPtr product(std::vector<ExprPtr> terms) {
    if (terms.empty()) { return mkReal("1"); }
    if (terms.size() == 1) { return terms.front(); }
    return mkOp(Op::MUL, std::move(terms));
}

ExprPtr nonzero(ExprPtr value) {
    return mkOp(Op::NOT, {mkOp(Op::EQ, {std::move(value), mkReal("0")})});
}

void appendReads(std::vector<std::size_t>& destination, const std::vector<std::size_t>& source) {
    destination.insert(destination.end(), source.begin(), source.end());
}

void uniqueReads(std::vector<std::size_t>& reads) {
    std::sort(reads.begin(), reads.end());
    reads.erase(std::unique(reads.begin(), reads.end()), reads.end());
}

void require(NumericTransition& result, ExprPtr guard, ExprPtr requirement) {
    result.constraints.push_back(mkOp(Op::IMPLIES, {std::move(guard), std::move(requirement)}));
}

void atMostOne(NumericTransition& result, const std::vector<ExprPtr>& guards) {
    if (guards.size() < 2) { return; }
    std::vector<ExprPtr> indicators;
    indicators.reserve(guards.size());
    for (const auto& guard : guards) {
        indicators.push_back(mkOp(Op::ITE, {guard, mkInt(1), mkInt(0)}));
    }
    result.constraints.push_back(mkOp(Op::LE, {mkOp(Op::ADD, std::move(indicators)), mkInt(1)}));
}

bool isStateCell(const NumericStateCell& cell) {
    return sortedAs(cell.value, SortKind::REAL) && sortedAs(cell.defined, SortKind::BOOL)
        && cell.value->kind == ExprKind::IDENT && cell.defined->kind == ExprKind::IDENT;
}

} // namespace

std::optional<NumericValue> numericConstant(const std::string& exact, Diagnostics& diagnostics) {
    auto value = mkReal(exact);
    ConstraintModel empty;
    if (!typeCheckTerms(empty, {{value, {}}}, diagnostics)) { return std::nullopt; }
    return NumericValue{value, mkBool(true), {}};
}

std::optional<NumericValue> numericRead(const NumericStateCell& cell, std::size_t index,
                                       Diagnostics& diagnostics) {
    if (!isStateCell(cell)) {
        diagnostics.error(ErrorCode::E_TYPE, "planning numeric read requires declared Real/Bool state identifiers");
        return std::nullopt;
    }
    return NumericValue{cell.value, cell.defined, {index}};
}

std::optional<NumericValue> numericArithmetic(Op op, const std::vector<NumericValue>& args,
                                             Diagnostics& diagnostics) {
    const bool unary = op == Op::NEG;
    const bool binary = op == Op::SUB || op == Op::DIV_REAL;
    if ((!unary && !binary && op != Op::ADD && op != Op::MUL)
        || (unary && args.size() != 1) || (binary && args.size() != 2)
        || ((!unary && !binary) && args.size() < 2)) {
        diagnostics.error(ErrorCode::E_TYPE, "planning numeric arithmetic has invalid operator or arity");
        return std::nullopt;
    }
    std::vector<ExprPtr> values, definitions;
    std::vector<std::size_t> reads;
    for (const auto& arg : args) {
        if (!valueShape(arg, diagnostics)) { return std::nullopt; }
        values.push_back(arg.value);
        definitions.push_back(arg.defined);
        appendReads(reads, arg.reads);
    }
    if (op == Op::DIV_REAL) { definitions.push_back(nonzero(args[1].value)); }
    uniqueReads(reads);
    auto defined = logical(Op::AND, std::move(definitions));
    auto expression = mkOp(op, std::move(values));
    // SMT division is total; this canonical inactive branch prevents its
    // arbitrary division-by-zero interpretation from becoming an observation.
    return NumericValue{mkOp(Op::ITE, {defined, expression, mkReal("0")}), defined, std::move(reads)};
}

std::optional<NumericCondition> numericCompare(Op op, const NumericValue& lhs,
                                               const NumericValue& rhs, Diagnostics& diagnostics) {
    if (op != Op::EQ && op != Op::LE && op != Op::LT && op != Op::GE && op != Op::GT) {
        diagnostics.error(ErrorCode::E_TYPE, "unsupported planning numeric comparison operator");
        return std::nullopt;
    }
    if (!valueShape(lhs, diagnostics) || !valueShape(rhs, diagnostics)) { return std::nullopt; }
    std::vector<std::size_t> reads = lhs.reads;
    appendReads(reads, rhs.reads);
    uniqueReads(reads);
    return NumericCondition{mkOp(op, {lhs.value, rhs.value}),
                            logical(Op::AND, {lhs.defined, rhs.defined}), std::move(reads)};
}

std::optional<NumericCondition> numericPredicate(ExprPtr predicate, Diagnostics& diagnostics) {
    if (!sortedAs(predicate, SortKind::BOOL)) {
        diagnostics.error(ErrorCode::E_TYPE, "planning predicate must have Bool sort");
        return std::nullopt;
    }
    return NumericCondition{std::move(predicate), mkBool(true), {}};
}

std::optional<NumericCondition> numericLogical(Op op, const std::vector<NumericCondition>& args,
                                               Diagnostics& diagnostics) {
    if ((op != Op::NOT && op != Op::AND && op != Op::OR && op != Op::IMPLIES)
        || (op == Op::NOT && args.size() != 1) || (op == Op::IMPLIES && args.size() != 2)) {
        diagnostics.error(ErrorCode::E_TYPE, "planning condition has invalid logical operator or arity");
        return std::nullopt;
    }
    std::vector<ExprPtr> values, definitions;
    std::vector<std::size_t> reads;
    for (const auto& arg : args) {
        if (!conditionShape(arg, diagnostics)) { return std::nullopt; }
        values.push_back(arg.value);
        definitions.push_back(arg.defined);
        appendReads(reads, arg.reads);
    }
    uniqueReads(reads);
    auto value = op == Op::AND || op == Op::OR ? logical(op, std::move(values)) : mkOp(op, std::move(values));
    return NumericCondition{std::move(value), logical(Op::AND, std::move(definitions)), std::move(reads)};
}

ExprPtr numericSatisfied(const NumericCondition& condition) {
    return logical(Op::AND, {condition.defined, condition.value});
}

std::optional<NumericTransition> buildNumericTransition(
    const ConstraintModel& context, const std::vector<NumericStateCell>& before,
    const std::vector<NumericStateCell>& after, const std::vector<NumericUpdate>& updates,
    Diagnostics& diagnostics) {
    if (before.size() != after.size()) {
        diagnostics.error(ErrorCode::E_TYPE, "planning numeric state vectors have different sizes");
        return std::nullopt;
    }
    std::vector<LocatedExpr> terms;
    std::set<std::string> names, future;
    for (std::size_t i = 0; i < before.size(); ++i) {
        if (!isStateCell(before[i]) || !isStateCell(after[i])) {
            diagnostics.error(ErrorCode::E_TYPE, "planning numeric states require Real/Bool identifiers");
            return std::nullopt;
        }
        for (const auto& term : {before[i].value, before[i].defined, after[i].value, after[i].defined}) {
            if (!names.insert(term->name).second) {
                diagnostics.error(ErrorCode::E_TYPE, "planning numeric state identifiers must be distinct");
                return std::nullopt;
            }
            terms.push_back({term, {}});
        }
        future.insert(after[i].value->name);
        future.insert(after[i].defined->name);
    }
    std::vector<std::vector<const NumericUpdate*>> groups(before.size());
    std::vector<ExprPtr> pending;
    for (const auto& update : updates) {
        if (update.target_index >= before.size() || update.owner_id.empty()
            || !sortedAs(update.guard, SortKind::BOOL) || !valueShape(update.rhs, diagnostics)) {
            diagnostics.error(ErrorCode::E_TYPE, "invalid planning numeric update target, owner, guard or value");
            return std::nullopt;
        }
        if (std::any_of(update.rhs.reads.begin(), update.rhs.reads.end(),
                        [&](std::size_t index) { return index >= before.size(); })) {
            diagnostics.error(ErrorCode::E_TYPE, "planning numeric read index is outside the old state");
            return std::nullopt;
        }
        for (const auto& term : {update.guard, update.rhs.value, update.rhs.defined}) {
            terms.push_back({term, {}});
            pending.push_back(term);
        }
        groups[update.target_index].push_back(&update);
    }
    if (!typeCheckTerms(context, terms, diagnostics)) { return std::nullopt; }
    std::map<std::string, ExprPtr> defined_bodies;
    for (const auto& function : context.funs) {
        if (function.body) { defined_bodies.emplace(function.name, function.body); }
    }
    // A defined function may capture a free state identifier in its body.
    // Follow only reachable definitions; scanning arguments alone would let
    // a nullary helper conceal a successor-state read or old-state dependency.
    // BOUND_VAR nodes remain lexical and are never treated as state names.
    // Each traversal below has its own visited set, including recursive
    // function bodies, so this does not inline or repeatedly expand a DAG.
    const auto appendDependencies = [&](const ExprPtr& term, std::vector<ExprPtr>& pending_terms) {
        pending_terms.insert(pending_terms.end(), term->args.begin(), term->args.end());
        if (term->kind == ExprKind::APPLY) {
            const auto body = defined_bodies.find(term->name);
            if (body != defined_bodies.end()) { pending_terms.push_back(body->second); }
        }
    };
    std::map<std::string, std::size_t> old_names;
    for (std::size_t i = 0; i < before.size(); ++i) {
        old_names.emplace(before[i].value->name, i);
        old_names.emplace(before[i].defined->name, i);
    }
    for (const auto& update : updates) {
        std::vector<ExprPtr> rhs_terms{update.rhs.value, update.rhs.defined};
        std::unordered_set<const Expr*> rhs_seen;
        std::set<std::size_t> actual_reads;
        while (!rhs_terms.empty()) {
            auto term = rhs_terms.back();
            rhs_terms.pop_back();
            if (!rhs_seen.insert(term.get()).second) { continue; }
            const auto found = old_names.find(term->name);
            if (term->kind == ExprKind::IDENT && found != old_names.end()) { actual_reads.insert(found->second); }
            appendDependencies(term, rhs_terms);
        }
        if (actual_reads != std::set<std::size_t>(update.rhs.reads.begin(), update.rhs.reads.end())) {
            diagnostics.error(ErrorCode::E_TYPE, "planning numeric RHS read metadata does not match its old-state terms");
            return std::nullopt;
        }
    }
    std::unordered_set<const Expr*> visited;
    while (!pending.empty()) {
        auto term = pending.back();
        pending.pop_back();
        if (!visited.insert(term.get()).second) { continue; }
        if (term->kind == ExprKind::IDENT && future.count(term->name)) {
            diagnostics.error(ErrorCode::E_TYPE, "planning simultaneous updates must read the old state only");
            return std::nullopt;
        }
        appendDependencies(term, pending);
    }
    NumericTransition result;
    for (std::size_t index = 0; index < before.size(); ++index) {
        const auto& now = before[index];
        const auto& next = after[index];
        std::vector<ExprPtr> assign_guards, add_guards, scale_guards, assignments, additions, multipliers, divisors;
        std::map<std::string, std::vector<ExprPtr>> scale_owners;
        for (const auto* update : groups[index]) {
            const auto guard = update->guard;
            const auto rhs = update->rhs.value;
            require(result, guard, update->rhs.defined);
            if (update->kind != NumericUpdateKind::ASSIGN) { require(result, guard, now.defined); }
            switch (update->kind) {
            case NumericUpdateKind::ASSIGN:
                assign_guards.push_back(guard);
                assignments.push_back(mkOp(Op::ITE, {guard, rhs, mkReal("0")}));
                break;
            case NumericUpdateKind::INCREASE:
            case NumericUpdateKind::DECREASE:
                add_guards.push_back(guard);
                additions.push_back(mkOp(Op::ITE, {guard,
                    update->kind == NumericUpdateKind::INCREASE ? rhs : mkOp(Op::NEG, {rhs}), mkReal("0")}));
                break;
            case NumericUpdateKind::SCALE_UP:
            case NumericUpdateKind::SCALE_DOWN:
                scale_guards.push_back(guard);
                scale_owners[update->owner_id].push_back(guard);
                if (update->kind == NumericUpdateKind::SCALE_DOWN) {
                    require(result, guard, nonzero(rhs));
                    divisors.push_back(mkOp(Op::ITE, {guard, rhs, mkReal("1")}));
                } else {
                    multipliers.push_back(mkOp(Op::ITE, {guard, rhs, mkReal("1")}));
                }
                break;
            default:
                diagnostics.error(ErrorCode::E_TYPE, "invalid planning numeric assignment kind");
                return std::nullopt;
            }
        }
        const auto assigned = logical(Op::OR, assign_guards);
        const auto added = logical(Op::OR, add_guards);
        const auto scaled = logical(Op::OR, scale_guards);
        atMostOne(result, assign_guards);
        atMostOne(result, {assigned, added, scaled});
        std::vector<ExprPtr> active_scale_owners;
        for (const auto& entry : scale_owners) {
            active_scale_owners.push_back(logical(Op::OR, entry.second));
        }
        atMostOne(result, active_scale_owners);
        auto value = additions.empty() ? now.value : mkOp(Op::ADD, {now.value, sum(std::move(additions))});
        if (!scale_guards.empty()) {
            auto scale_value = multipliers.empty() ? now.value
                : mkOp(Op::MUL, {now.value, product(std::move(multipliers))});
            if (!divisors.empty()) { scale_value = mkOp(Op::DIV_REAL, {scale_value, product(std::move(divisors))}); }
            value = mkOp(Op::ITE, {scaled, scale_value, value});
        }
        if (!assign_guards.empty()) { value = mkOp(Op::ITE, {assigned, sum(std::move(assignments)), value}); }
        const auto defined = logical(Op::OR, {now.defined, assigned});
        require(result, mkOp(Op::NOT, {now.defined}), mkOp(Op::EQ, {now.value, mkReal("0")}));
        result.constraints.push_back(mkOp(Op::EQ, {next.defined, defined}));
        result.constraints.push_back(mkOp(Op::EQ, {next.value, mkOp(Op::ITE, {defined, value, mkReal("0")})}));
    }
    return result;
}

} // namespace SOMTParser::Uir::Hir::Planning
