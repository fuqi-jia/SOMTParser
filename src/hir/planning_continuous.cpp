#include "somtparser/hir/planning_continuous.h"
#include "somtparser/hir/typecheck.h"

#include <algorithm>
#include <functional>
#include <unordered_map>
#include <unordered_set>

namespace SOMTParser::Uir::Hir::Planning {
namespace {
using Replacement = std::unordered_map<std::string, ExprPtr>;

ExprPtr zero() { return mkReal("0"); }
ExprPtr op(Op operation, ExprPtr left, ExprPtr right) {
    return mkOp(operation, {std::move(left), std::move(right)});
}
ExprPtr conjunction(std::vector<ExprPtr> terms) {
    if (terms.empty()) { return mkBool(true); }
    if (terms.size() == 1) { return terms.front(); }
    return mkOp(Op::AND, std::move(terms));
}
ExprPtr implies(ExprPtr guard, ExprPtr formula) { return op(Op::IMPLIES, std::move(guard), std::move(formula)); }
ExprPtr negation(ExprPtr value) { return mkOp(Op::NOT, {std::move(value)}); }
ExprPtr absolute(ExprPtr value) {
    return mkOp(Op::ITE, {op(Op::GE, value, zero()), value, mkOp(Op::NEG, {value})});
}
bool sortedAs(const ExprPtr& value, SortKind kind) { return value && value->sort.kind == kind; }
bool stateCell(const NumericStateCell& cell) {
    return sortedAs(cell.value, SortKind::REAL) && cell.value->kind == ExprKind::IDENT
        && sortedAs(cell.defined, SortKind::BOOL) && cell.defined->kind == ExprKind::IDENT;
}

// Only free occurrences of the designated BOUND_VAR placeholders change.
// Inner quantifiers shadow those placeholders; IDENT parameters never do.
// All inserted binders are fresh across both the model and input templates.
// HIR currently has no LET expression kind; a future binding kind needs an
// explicit scope rule before being accepted here.
ExprPtr instantiate(const ExprPtr& expression, const Replacement& replacements) {
    std::unordered_map<const Expr*, ExprPtr> cache;
    std::function<ExprPtr(const ExprPtr&)> visit = [&](const ExprPtr& term) -> ExprPtr {
        if (!term) { return term; } // Preserve malformed children for typecheck diagnostics.
        const auto cached = cache.find(term.get());
        if (cached != cache.end()) { return cached->second; }
        if (term->kind == ExprKind::BOUND_VAR) {
            const auto found = replacements.find(term->name);
            return found == replacements.end() ? term : found->second;
        }
        if (term->kind == ExprKind::FORALL || term->kind == ExprKind::EXISTS) {
            Replacement inner = replacements;
            for (const auto& binder : term->binders) { inner.erase(binder.name); }
            auto copy = std::make_shared<Expr>(*term);
            for (auto& argument : copy->args) { argument = instantiate(argument, inner); }
            cache.emplace(term.get(), copy);
            return copy;
        }
        if (term->args.empty()) { return term; }
        auto copy = std::make_shared<Expr>(*term);
        for (auto& argument : copy->args) { argument = visit(argument); }
        cache.emplace(term.get(), copy);
        return copy;
    };
    return visit(expression);
}

struct Names {
    std::unordered_set<std::string> used;
    std::unordered_set<const Expr*> seen;
    std::size_t serial = 0;
    void add(const ExprPtr& term) {
        if (!term || !seen.insert(term.get()).second) { return; }
        if (!term->name.empty()) { used.insert(term->name); }
        for (const auto& binder : term->binders) { used.insert(binder.name); }
        for (const auto& argument : term->args) { add(argument); }
    }
    std::string fresh() {
        for (;;) {
            const auto name = "__flow_bound_" + std::to_string(serial++);
            if (used.insert(name).second) { return name; }
        }
    }
};

ExprPtr quantify(ExprKind kind, const ExprPtr& variable, ExprPtr body) {
    const std::vector<Binder> binders{{variable->name, Sort::real()}};
    return kind == ExprKind::FORALL ? mkForall(binders, std::move(body))
                                   : mkExists(binders, std::move(body));
}

ExprPtr inside(const ContinuousSegment& segment, const ExprPtr& time, bool left, bool right) {
    return conjunction({op(left ? Op::LE : Op::LT, segment.start, time),
                        op(right ? Op::LE : Op::LT, time, segment.end)});
}

ExprPtr polynomial(const std::vector<ExprPtr>& coefficients, const ExprPtr& elapsed) {
    ExprPtr value = zero();
    for (auto item = coefficients.rbegin(); item != coefficients.rend(); ++item) {
        value = op(Op::ADD, *item, op(Op::MUL, elapsed, value));
    }
    return value;
}

ExprPtr polynomialDerivative(const std::vector<ExprPtr>& coefficients, const ExprPtr& elapsed) {
    ExprPtr value = zero();
    for (std::size_t index = coefficients.size(); index > 1; --index) {
        value = op(Op::ADD, op(Op::MUL, mkReal(std::to_string(index - 1)), coefficients[index - 1]),
                   op(Op::MUL, elapsed, value));
    }
    return value;
}

std::optional<ContinuousEncoding> encode(
    const ConstraintModel& context, const ContinuousSegment& segment,
    const std::vector<std::vector<ExprPtr>>* coefficients, Diagnostics& diagnostics) {
    const auto reject = [&](const std::string& reason) -> std::optional<ContinuousEncoding> {
        diagnostics.error(ErrorCode::E_TYPE, "continuous flow: " + reason);
        return std::nullopt;
    };
    if (!sortedAs(segment.enabled, SortKind::BOOL) || !sortedAs(segment.start, SortKind::REAL)
        || !sortedAs(segment.end, SortKind::REAL) || segment.time_variable.empty()
        || !segment.derivative_domain
        || (*segment.derivative_domain != FlowDerivativeDomain::INTERIOR
            && *segment.derivative_domain != FlowDerivativeDomain::CLOSED_ONE_SIDED)) {
        return reject("requires Bool activation, Real endpoints, a time placeholder and explicit derivative domain");
    }
    if (coefficients && coefficients->size() != segment.coordinates.size()) {
        return reject("polynomial coordinate count does not match the state vector");
    }
    if (!typeCheckTerms(context, {}, diagnostics)) { return std::nullopt; }
    Names names;
    std::unordered_set<std::string> symbols, state_names, placeholders{segment.time_variable};
    for (const auto& declaration : context.decls) {
        names.used.insert(declaration.name); symbols.insert(declaration.name);
        names.add(declaration.lower_bound); names.add(declaration.upper_bound);
    }
    for (const auto& function : context.funs) {
        names.used.insert(function.name); symbols.insert(function.name); names.add(function.body);
        for (const auto& binder : function.binders) { names.used.insert(binder.name); }
    }
    for (const auto& constraint : context.constraints) { names.add(constraint.formula); }
    for (const auto& objective : context.objectives) { names.add(objective.term); }
    names.used.insert(segment.time_variable);
    names.add(segment.enabled); names.add(segment.start); names.add(segment.end);
    std::vector<LocatedExpr> direct{{segment.enabled, {}}, {segment.start, {}}, {segment.end, {}}};
    for (const auto& coordinate : segment.coordinates) {
        if (coordinate.trajectory_name.empty() || !symbols.insert(coordinate.trajectory_name).second
            || coordinate.variable.empty() || !placeholders.insert(coordinate.variable).second
            || !stateCell(coordinate.initial) || !stateCell(coordinate.terminal)
            || !sortedAs(coordinate.active, SortKind::BOOL)
            || !sortedAs(coordinate.rate.value, SortKind::REAL)
            || !sortedAs(coordinate.rate.defined, SortKind::BOOL)) {
            return reject("invalid/duplicate trajectory, placeholder, state coordinate or rate sort");
        }
        names.used.insert(coordinate.trajectory_name); names.used.insert(coordinate.variable);
        for (const auto& cell_term : {coordinate.initial.value, coordinate.initial.defined,
                                     coordinate.terminal.value, coordinate.terminal.defined}) {
            if (!state_names.insert(cell_term->name).second) {
                return reject("initial/terminal state identifiers must be distinct across all coordinates; express equality explicitly");
            }
        }
        for (const auto& term : {coordinate.initial.value, coordinate.initial.defined,
                                coordinate.terminal.value, coordinate.terminal.defined, coordinate.active}) {
            direct.push_back({term, {}}); names.add(term);
        }
        names.add(coordinate.rate.value); names.add(coordinate.rate.defined);
    }
    for (const auto& invariant : segment.invariants) {
        if (!sortedAs(invariant.guard, SortKind::BOOL)
            || !sortedAs(invariant.condition.value, SortKind::BOOL)
            || !sortedAs(invariant.condition.defined, SortKind::BOOL)) {
            return reject("invariant guard, value and definedness must be Bool");
        }
        direct.push_back({invariant.guard, {}});
        names.add(invariant.guard); names.add(invariant.condition.value); names.add(invariant.condition.defined);
    }
    if (coefficients) {
        for (const auto& coordinate : *coefficients) {
            for (const auto& coefficient : coordinate) {
                if (!sortedAs(coefficient, SortKind::REAL)) { return reject("polynomial coefficient must be exact Real"); }
                // Checked in the enclosing context, with NO placeholder scope.
                direct.push_back({coefficient, {}}); names.add(coefficient);
            }
        }
    }
    if (!typeCheckTerms(context, direct, diagnostics)) { return std::nullopt; }

    Replacement validation;
    std::vector<Binder> scope;
    for (const auto& placeholder : placeholders) {
        const auto fresh = names.fresh();
        validation.emplace(placeholder, mkBoundVar(fresh, Sort::real()));
        scope.push_back({fresh, Sort::real()});
    }
    std::vector<LocatedExpr> templates;
    for (const auto& coordinate : segment.coordinates) {
        // Typecheck the unmodified template first under fresh binder aliases.
        // A malformed node in an inactive source branch is still refused.
        templates.push_back({mkForall(scope, conjunction({
            op(Op::EQ, instantiate(coordinate.rate.value, validation), zero()),
            instantiate(coordinate.rate.defined, validation)})), {}});
    }
    for (const auto& invariant : segment.invariants) {
        templates.push_back({mkForall(scope, conjunction({
            instantiate(invariant.condition.value, validation),
            instantiate(invariant.condition.defined, validation)})), {}});
    }
    if (!typeCheckTerms(context, templates, diagnostics)) { return std::nullopt; }

    ContinuousEncoding result;
    result.derivative_domain = *segment.derivative_domain;
    result.polynomial_witness = coefficients != nullptr;
    result.requires_trajectory_source_observations = coefficients == nullptr;
    const auto fresh = [&]() { return mkBoundVar(names.fresh(), Sort::real()); };
    const auto point = fresh();
    const auto read = [&](std::size_t index, const ExprPtr& at) {
        return mkApply(segment.coordinates[index].trajectory_name, Sort::real(), {at});
    };
    const auto substitution = [&](const ExprPtr& at) {
        Replacement map{{segment.time_variable, at}};
        for (std::size_t index = 0; index < segment.coordinates.size(); ++index) {
            map.emplace(segment.coordinates[index].variable, read(index, at));
        }
        return map;
    };
    for (std::size_t index = 0; index < segment.coordinates.size(); ++index) {
        FunDecl function;
        function.name = segment.coordinates[index].trajectory_name;
        function.params = {Sort::real()}; function.result = Sort::real();
        if (coefficients) {
            const auto argument = fresh();
            function.binders = {{argument->name, Sort::real()}};
            function.body = mkOp(Op::ITE, {
                conjunction({segment.enabled, inside(segment, argument, true, true)}),
                polynomial((*coefficients)[index], op(Op::SUB, argument, segment.start)), zero()});
            function.auxiliary = true;
        }
        result.trajectories.push_back(std::move(function));
    }
    result.constraints.push_back(implies(segment.enabled, op(Op::LT, segment.start, segment.end)));
    const bool closed = *segment.derivative_domain == FlowDerivativeDomain::CLOSED_ONE_SIDED;
    const auto derivative_guard = conjunction({segment.enabled, inside(segment, point, closed, closed)});
    const auto replacements = substitution(point);
    for (std::size_t index = 0; index < segment.coordinates.size(); ++index) {
        const auto& coordinate = segment.coordinates[index];
        const auto at_point = read(index, point);
        const auto defined = instantiate(coordinate.rate.defined, replacements);
        const auto field = mkOp(Op::ITE, {coordinate.active,
            instantiate(coordinate.rate.value, replacements), zero()});
        result.constraints.push_back(implies(segment.enabled, conjunction({
            implies(negation(coordinate.initial.defined), op(Op::EQ, coordinate.initial.value, zero())),
            op(Op::EQ, coordinate.terminal.defined, coordinate.initial.defined),
            implies(negation(coordinate.terminal.defined), op(Op::EQ, coordinate.terminal.value, zero())),
            implies(coordinate.active, coordinate.initial.defined),
            op(Op::EQ, read(index, segment.start), coordinate.initial.value),
            op(Op::EQ, read(index, segment.end), coordinate.terminal.value)})));
        // Outside the modelled interval, including a disabled segment, there
        // is no independent trajectory freedom. Endpoints stay inside here.
        result.constraints.push_back(quantify(ExprKind::FORALL, point,
            implies(negation(conjunction({segment.enabled, inside(segment, point, true, true)})),
                    op(Op::EQ, at_point, zero()))));
        result.constraints.push_back(quantify(ExprKind::FORALL, point,
            implies(conjunction({segment.enabled, inside(segment, point, true, true),
                                 negation(coordinate.initial.defined)}), op(Op::EQ, at_point, zero()))));
        result.constraints.push_back(quantify(ExprKind::FORALL, point,
            implies(derivative_guard, implies(coordinate.active, defined))));
        if (coefficients) {
            const auto derivative = polynomialDerivative((*coefficients)[index], op(Op::SUB, point, segment.start));
            result.constraints.push_back(quantify(ExprKind::FORALL, point,
                implies(derivative_guard, op(Op::EQ, derivative, field))));
            continue;
        }
        // Relative closed-interval continuity includes both endpoints. Delta
        // depends on point and epsilon; witness/sample is universally scoped.
        const auto epsilon = fresh(), delta = fresh(), sample = fresh();
        const auto distance = absolute(op(Op::SUB, sample, point));
        const auto continuous = quantify(ExprKind::FORALL, epsilon,
            implies(op(Op::GT, epsilon, zero()), quantify(ExprKind::EXISTS, delta,
                conjunction({op(Op::GT, delta, zero()), quantify(ExprKind::FORALL, sample,
                    implies(conjunction({inside(segment, sample, true, true), op(Op::LT, distance, delta)}),
                            op(Op::LT, absolute(op(Op::SUB, read(index, sample), at_point)), epsilon)))}))));
        result.constraints.push_back(quantify(ExprKind::FORALL, point,
            implies(conjunction({segment.enabled, inside(segment, point, true, true)}), continuous)));
        // Multiplication by the strictly positive distance avoids introducing
        // a total SMT division at sample==point. Endpoint samples are drawn
        // only from the interval, giving the selected one-sided limits.
        const auto error = absolute(op(Op::SUB, op(Op::SUB, read(index, sample), at_point),
                                      op(Op::MUL, field, op(Op::SUB, sample, point))));
        const auto differentiable = quantify(ExprKind::FORALL, epsilon,
            implies(op(Op::GT, epsilon, zero()), quantify(ExprKind::EXISTS, delta,
                conjunction({op(Op::GT, delta, zero()), quantify(ExprKind::FORALL, sample,
                    implies(conjunction({inside(segment, sample, true, true),
                                         op(Op::GT, distance, zero()), op(Op::LT, distance, delta)}),
                            op(Op::LT, error, op(Op::MUL, epsilon, distance))))}))));
        result.constraints.push_back(quantify(ExprKind::FORALL, point,
            implies(derivative_guard, differentiable)));
    }
    for (const auto& invariant : segment.invariants) {
        result.constraints.push_back(quantify(ExprKind::FORALL, point,
            implies(conjunction({segment.enabled, invariant.guard,
                                 inside(segment, point, invariant.include_start, invariant.include_end)}),
                    conjunction({instantiate(invariant.condition.defined, replacements),
                                 instantiate(invariant.condition.value, replacements)}))));
    }
    ConstraintModel validated = context;
    validated.funs.insert(validated.funs.end(), result.trajectories.begin(), result.trajectories.end());
    std::vector<LocatedExpr> generated;
    for (const auto& constraint : result.constraints) { generated.push_back({constraint, {}}); }
    if (!typeCheckTerms(validated, generated, diagnostics)) { return std::nullopt; }
    return result;
}
} // namespace

std::optional<ContinuousEncoding> encodeContinuousSegment(
    const ConstraintModel& context, const ContinuousSegment& segment, Diagnostics& diagnostics) {
    return encode(context, segment, nullptr, diagnostics);
}

std::optional<ContinuousEncoding> encodePolynomialFlowWitness(
    const ConstraintModel& context, const ContinuousSegment& segment,
    const std::vector<std::vector<ExprPtr>>& coefficients, Diagnostics& diagnostics) {
    return encode(context, segment, &coefficients, diagnostics);
}

} // namespace SOMTParser::Uir::Hir::Planning
