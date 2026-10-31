#include "somtparser/hir/planning_trajectory.h"
#include "somtparser/hir/typecheck.h"

#include <functional>
#include <unordered_map>
#include <unordered_set>

namespace SOMTParser::Uir::Hir::Planning {
namespace {
ExprPtr binary(Op op, ExprPtr a, ExprPtr b) { return mkOp(op, {std::move(a), std::move(b)}); }
ExprPtr all(std::vector<ExprPtr> terms) {
    if (terms.empty()) { return mkBool(true); }
    if (terms.size() == 1) { return terms.front(); }
    return mkOp(Op::AND, std::move(terms));
}
ExprPtr any(std::vector<ExprPtr> terms) {
    if (terms.empty()) { return mkBool(false); }
    if (terms.size() == 1) { return terms.front(); }
    return mkOp(Op::OR, std::move(terms));
}
ExprPtr not_(ExprPtr term) { return mkOp(Op::NOT, {std::move(term)}); }
ExprPtr implies(ExprPtr a, ExprPtr b) { return binary(Op::IMPLIES, std::move(a), std::move(b)); }
ExprPtr positive(const NumericCondition& condition) { return all({condition.defined, condition.value}); }
ExprPtr negative(const NumericCondition& condition) { return all({condition.defined, not_(condition.value)}); }
bool sort(const ExprPtr& term, SortKind expected) { return term && term->sort.kind == expected; }
bool conditionSort(const NumericCondition& condition) {
    return sort(condition.value, SortKind::BOOL) && sort(condition.defined, SortKind::BOOL);
}
bool binaryModal(TrajectoryOperator operation) {
    return operation == TrajectoryOperator::SOMETIME_BEFORE
        || operation == TrajectoryOperator::SOMETIME_AFTER
        || operation == TrajectoryOperator::ALWAYS_WITHIN;
}
bool parameters(TrajectoryOperator operation, const ExprPtr& lower, const ExprPtr& upper,
                Diagnostics& diagnostics) {
    bool bound = false, window = false;
    switch (operation) {
    case TrajectoryOperator::AT_END: case TrajectoryOperator::ALWAYS:
    case TrajectoryOperator::SOMETIME: case TrajectoryOperator::AT_MOST_ONCE:
    case TrajectoryOperator::SOMETIME_BEFORE: case TrajectoryOperator::SOMETIME_AFTER: break;
    case TrajectoryOperator::WITHIN: case TrajectoryOperator::ALWAYS_WITHIN:
    case TrajectoryOperator::HOLD_AFTER: bound = true; break;
    case TrajectoryOperator::HOLD_DURING: bound = true; window = true; break;
    default:
        diagnostics.error(ErrorCode::E_TYPE, "trajectory: invalid modal operator"); return false;
    }
    if ((bound ? !sort(lower, SortKind::REAL) : bool(lower))
        || (window ? !sort(upper, SortKind::REAL) : bool(upper))) {
        diagnostics.error(ErrorCode::E_TYPE, "trajectory: wrong number or sort of Real bounds"); return false;
    }
    return true;
}
bool finish(const ConstraintModel& context, const TrajectoryEncoding& result, Diagnostics& diagnostics) {
    std::vector<LocatedExpr> terms{{result.satisfied, {}}};
    for (const auto& term : result.domain_constraints) { terms.push_back({term, {}}); }
    return typeCheckTerms(context, terms, diagnostics);
}

using Replacement = std::unordered_map<std::string, ExprPtr>;
// Only free BOUND_VAR placeholders are substituted; a nested binder shadows
// them. Insertion variables are fresh across the complete context/templates.
ExprPtr replace(const ExprPtr& expression, const Replacement& replacements) {
    std::unordered_map<const Expr*, ExprPtr> memo;
    std::function<ExprPtr(const ExprPtr&)> visit = [&](const ExprPtr& term) -> ExprPtr {
        if (!term) { return term; }
        const auto found = memo.find(term.get());
        if (found != memo.end()) { return found->second; }
        if (term->kind == ExprKind::BOUND_VAR) {
            const auto item = replacements.find(term->name);
            return item == replacements.end() ? term : item->second;
        }
        if (term->kind == ExprKind::FORALL || term->kind == ExprKind::EXISTS) {
            Replacement inner = replacements;
            for (const auto& binder : term->binders) { inner.erase(binder.name); }
            auto copy = std::make_shared<Expr>(*term);
            for (auto& argument : copy->args) { argument = replace(argument, inner); }
            memo.emplace(term.get(), copy); return copy;
        }
        if (term->args.empty()) { return term; }
        auto copy = std::make_shared<Expr>(*term);
        for (auto& argument : copy->args) { argument = visit(argument); }
        memo.emplace(term.get(), copy); return copy;
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
        for (const auto& child : term->args) { add(child); }
    }
    std::string fresh() {
        for (;;) {
            auto name = "__trajectory_bound_" + std::to_string(serial++);
            if (used.insert(name).second) { return name; }
        }
    }
    TrajectoryPoint point() {
        return {mkBoundVar(fresh(), Sort::real()), mkBoundVar(fresh(), Sort::integer())};
    }
};
ExprPtr before(const TrajectoryPoint& a, const TrajectoryPoint& b, bool inclusive) {
    return any({binary(Op::LT, a.time, b.time), all({binary(Op::EQ, a.time, b.time),
        binary(inclusive ? Op::LE : Op::LT, a.phase, b.phase)})});
}
ExprPtr quantified(bool universal, const std::vector<TrajectoryPoint>& points, ExprPtr body) {
    std::vector<Binder> binders;
    for (const auto& point : points) {
        binders.push_back({point.time->name, Sort::real()});
        binders.push_back({point.phase->name, Sort::integer()});
    }
    return universal ? mkForall(binders, std::move(body)) : mkExists(binders, std::move(body));
}
} // namespace

std::optional<TrajectoryEncoding> encodeFiniteTrajectory(
    const ConstraintModel& context, TrajectoryOperator operation,
    const std::vector<TrajectorySample>& samples, ExprPtr lower, ExprPtr upper,
    Diagnostics& diagnostics) {
    if (!parameters(operation, lower, upper, diagnostics)) { return std::nullopt; }
    if (samples.empty()) {
        diagnostics.error(ErrorCode::E_TYPE, "trajectory: requires an initial observation"); return std::nullopt;
    }
    std::vector<LocatedExpr> terms;
    if (lower) { terms.push_back({lower, {}}); }
    if (upper) { terms.push_back({upper, {}}); }
    for (const auto& sample : samples) {
        if (!sort(sample.active, SortKind::BOOL) || !sort(sample.time, SortKind::REAL)
            || !conditionSort(sample.first) || bool(sample.second) != binaryModal(operation)
            || (sample.second && !conditionSort(*sample.second))) {
            diagnostics.error(ErrorCode::E_TYPE, "trajectory: malformed sample, condition or secondary predicate");
            return std::nullopt;
        }
        for (const auto& term : {sample.active, sample.time, sample.first.value, sample.first.defined}) {
            terms.push_back({term, {}});
        }
        if (sample.second) {
            terms.push_back({sample.second->value, {}}); terms.push_back({sample.second->defined, {}});
        }
    }
    if (!typeCheckTerms(context, terms, diagnostics)) { return std::nullopt; }
    TrajectoryEncoding result;
    result.domain_constraints = {samples.front().active, binary(Op::EQ, samples.front().time, mkReal("0"))};
    std::vector<ExprPtr> yes, no, other, final_cases;
    for (std::size_t i = 0; i < samples.size(); ++i) {
        const auto& sample = samples[i];
        if (i) {
            result.domain_constraints.push_back(implies(sample.active, all({samples[i-1].active,
                binary(Op::LT, samples[i-1].time, sample.time)})));
        }
        yes.push_back(all({sample.active, positive(sample.first)}));
        no.push_back(all({sample.active, negative(sample.first)}));
        if (sample.second) { other.push_back(all({sample.active, positive(*sample.second)})); }
        auto is_last = i + 1 == samples.size() ? sample.active
            : all({sample.active, not_(samples[i+1].active)});
        final_cases.push_back(all({is_last, positive(sample.first)}));
    }
    auto final_satisfied = any(final_cases);
    std::vector<ExprPtr> clauses;
    switch (operation) {
    case TrajectoryOperator::AT_END: result.satisfied = final_satisfied; break;
    case TrajectoryOperator::ALWAYS:
        for (const auto& sample : samples) { clauses.push_back(implies(sample.active, positive(sample.first))); }
        result.satisfied = all(clauses); break;
    case TrajectoryOperator::SOMETIME: result.satisfied = any(yes); break;
    case TrajectoryOperator::WITHIN:
        for (std::size_t i = 0; i < samples.size(); ++i) {
            clauses.push_back(all({yes[i], binary(Op::LE, samples[i].time, lower)}));
        }
        result.satisfied = any(clauses); break;
    case TrajectoryOperator::AT_MOST_ONCE: {
        auto seen = mkBool(false), ended = mkBool(false);
        for (std::size_t i = 0; i < samples.size(); ++i) {
            clauses.push_back(not_(all({ended, yes[i]})));
            clauses.push_back(implies(all({seen, samples[i].active}), samples[i].first.defined));
            ended = any({ended, all({seen, no[i]})});
            seen = any({seen, yes[i]});
        }
        result.satisfied = all(clauses); break;
    }
    case TrajectoryOperator::SOMETIME_BEFORE: {
        auto previous = mkBool(false);
        for (std::size_t i = 0; i < samples.size(); ++i) {
            clauses.push_back(implies(yes[i], previous)); previous = any({previous, other[i]});
        }
        result.satisfied = all(clauses); break;
    }
    case TrajectoryOperator::SOMETIME_AFTER: {
        auto future = mkBool(false);
        for (std::size_t i = samples.size(); i-- > 0;) {
            future = any({future, other[i]}); clauses.push_back(implies(yes[i], future));
        }
        result.satisfied = all(clauses); break;
    }
    case TrajectoryOperator::ALWAYS_WITHIN:
        for (std::size_t i = 0; i < samples.size(); ++i) {
            std::vector<ExprPtr> witnesses;
            for (std::size_t j = i; j < samples.size(); ++j) {
                witnesses.push_back(all({other[j], binary(Op::LE,
                    binary(Op::SUB, samples[j].time, samples[i].time), lower)}));
            }
            clauses.push_back(implies(yes[i], any(witnesses)));
        }
        result.satisfied = all(clauses); break;
    case TrajectoryOperator::HOLD_AFTER: {
        std::vector<ExprPtr> ends_before;
        for (std::size_t i = 0; i < samples.size(); ++i) {
            clauses.push_back(all({yes[i], binary(Op::GT, samples[i].time, lower)}));
            ends_before.push_back(implies(samples[i].active, binary(Op::LE, samples[i].time, lower)));
        }
        result.satisfied = any({any(clauses), all({all(ends_before), final_satisfied})}); break;
    }
    case TrajectoryOperator::HOLD_DURING: {
        auto later_at_or_before = mkBool(false);
        std::vector<ExprPtr> reaches_after;
        for (std::size_t i = samples.size(); i-- > 0;) {
            const auto& sample = samples[i];
            auto at_or_before = all({sample.active, binary(Op::LE, sample.time, lower)});
            clauses.push_back(implies(all({sample.active, binary(Op::LE, lower, sample.time),
                binary(Op::LT, sample.time, upper)}), positive(sample.first)));
            clauses.push_back(implies(all({at_or_before, not_(later_at_or_before)}), positive(sample.first)));
            later_at_or_before = any({at_or_before, later_at_or_before});
            reaches_after.push_back(all({sample.active, binary(Op::GT, sample.time, lower)}));
        }
        result.satisfied = mkOp(Op::ITE, {any(reaches_after), all(clauses), final_satisfied}); break;
    }
    }
    if (!finish(context, result, diagnostics)) { return std::nullopt; }
    return result;
}

std::optional<TrajectoryEncoding> encodeObservedTrajectory(
    const ConstraintModel& context, const TrajectoryObservationDomain& domain,
    TrajectoryOperator operation, const NumericCondition& first,
    const std::optional<NumericCondition>& second, ExprPtr lower, ExprPtr upper,
    Diagnostics& diagnostics) {
    if (!parameters(operation, lower, upper, diagnostics)) { return std::nullopt; }
    if (domain.time_variable.empty() || domain.phase_variable.empty()
        || domain.time_variable == domain.phase_variable || !sort(domain.contains, SortKind::BOOL)
        || !sort(domain.first.time, SortKind::REAL) || !sort(domain.last.time, SortKind::REAL)
        || !sort(domain.first.phase, SortKind::INT) || !sort(domain.last.phase, SortKind::INT)
        || !conditionSort(first) || bool(second) != binaryModal(operation)
        || (second && !conditionSort(*second))) {
        diagnostics.error(ErrorCode::E_TYPE, "trajectory: malformed observation domain or predicate template");
        return std::nullopt;
    }
    // This checks every defined function body too; templates cannot conceal
    // undeclared globals or capture a placeholder through a helper definition.
    std::vector<LocatedExpr> direct{{domain.first.time, {}}, {domain.first.phase, {}},
        {domain.last.time, {}}, {domain.last.phase, {}}};
    if (lower) { direct.push_back({lower, {}}); } if (upper) { direct.push_back({upper, {}}); }
    if (!typeCheckTerms(context, direct, diagnostics)) { return std::nullopt; }
    Names names;
    names.used.insert(domain.time_variable); names.used.insert(domain.phase_variable);
    for (const auto& declaration : context.decls) {
        names.used.insert(declaration.name); names.add(declaration.lower_bound); names.add(declaration.upper_bound);
    }
    for (const auto& function : context.funs) {
        names.used.insert(function.name); names.add(function.body);
        for (const auto& binder : function.binders) { names.used.insert(binder.name); }
    }
    for (const auto& row : context.constraints) { names.add(row.formula); }
    for (const auto& row : context.objectives) { names.add(row.term); }
    for (const auto& row : direct) { names.add(row.expression); }
    names.add(domain.contains); names.add(first.value); names.add(first.defined);
    if (second) { names.add(second->value); names.add(second->defined); }
    const auto a = names.point(), b = names.point(), c = names.point();
    const auto at = [&](const ExprPtr& term, const TrajectoryPoint& point) {
        return replace(term, {{domain.time_variable, point.time}, {domain.phase_variable, point.phase}});
    };
    const auto member = [&](const TrajectoryPoint& point) { return at(domain.contains, point); };
    const auto yes = [&](const TrajectoryPoint& point) { return at(positive(first), point); };
    const auto other = [&](const TrajectoryPoint& point) { return at(positive(*second), point); };
    std::vector<ExprPtr> validation{at(domain.contains, a), at(first.value, a), at(first.defined, a)};
    if (second) { validation.push_back(at(second->value, a)); validation.push_back(at(second->defined, a)); }
    if (!typeCheckTerms(context, {{quantified(true, {a}, all(validation)), {}}}, diagnostics)) {
        return std::nullopt;
    }
    TrajectoryEncoding result;
    result.domain_constraints = {binary(Op::EQ, domain.first.time, mkReal("0")),
        before(domain.first, domain.last, true), member(domain.first), member(domain.last),
        quantified(true, {a}, implies(member(a), all({before(domain.first, a, true), before(a, domain.last, true)})))};
    auto final_satisfied = yes(domain.last);
    switch (operation) {
    case TrajectoryOperator::AT_END: result.satisfied = final_satisfied; break;
    case TrajectoryOperator::ALWAYS:
        result.satisfied = quantified(true, {a}, implies(member(a), yes(a))); break;
    case TrajectoryOperator::SOMETIME:
        result.satisfied = quantified(false, {a}, all({member(a), yes(a)})); break;
    case TrajectoryOperator::WITHIN:
        result.satisfied = quantified(false, {a}, all({member(a), binary(Op::LE, a.time, lower), yes(a)})); break;
    case TrajectoryOperator::HOLD_AFTER:
        result.satisfied = mkOp(Op::ITE, {binary(Op::GT, domain.last.time, lower),
            quantified(false, {a}, all({member(a), binary(Op::GT, a.time, lower), yes(a)})), final_satisfied}); break;
    case TrajectoryOperator::HOLD_DURING: {
        auto no_later_predecessor = not_(quantified(false, {b}, all({member(b), before(a, b, false),
            binary(Op::LE, b.time, lower)})));
        auto in_window = all({binary(Op::LE, lower, a.time), binary(Op::LT, a.time, upper)});
        auto predecessor = all({binary(Op::LE, a.time, lower), no_later_predecessor});
        result.satisfied = mkOp(Op::ITE, {binary(Op::GT, domain.last.time, lower),
            quantified(true, {a}, implies(all({member(a), any({in_window, predecessor})}), yes(a))), final_satisfied});
        break;
    }
    case TrajectoryOperator::AT_MOST_ONCE:
        result.satisfied = all({
            quantified(true, {a,b}, implies(all({member(a), member(b), before(a,b,true), yes(a)}), at(first.defined,b))),
            quantified(true, {a,b,c}, implies(all({member(a), member(b), member(c), before(a,b,true),
                before(b,c,true), yes(a), yes(c)}), yes(b)))}); break;
    case TrajectoryOperator::SOMETIME_BEFORE:
    case TrajectoryOperator::SOMETIME_AFTER:
    case TrajectoryOperator::ALWAYS_WITHIN: {
        auto ordering = operation == TrajectoryOperator::SOMETIME_BEFORE ? before(b,a,false) : before(a,b,true);
        std::vector<ExprPtr> witness{member(b), ordering, other(b)};
        if (operation == TrajectoryOperator::ALWAYS_WITHIN) {
            witness.push_back(binary(Op::LE, binary(Op::SUB,b.time,a.time),lower));
        }
        result.satisfied = quantified(true, {a}, implies(all({member(a),yes(a)}), quantified(false,{b},all(witness))));
        break;
    }
    }
    if (!finish(context, result, diagnostics)) { return std::nullopt; }
    return result;
}

std::optional<PreferenceEncoding> encodePreferences(
    const ConstraintModel& context, const std::vector<PreferenceInstance>& instances,
    Diagnostics& diagnostics, const std::vector<std::string>& declared_names) {
    std::unordered_set<std::string> identities;
    std::vector<LocatedExpr> terms;
    for (const auto& instance : instances) {
        if (instance.instance_id.empty() || !identities.insert(instance.instance_id).second
            || !sort(instance.active, SortKind::BOOL) || !sort(instance.satisfied, SortKind::BOOL)) {
            diagnostics.error(ErrorCode::E_TYPE, "preference: invalid or duplicate grounded instance identity/Bool expression");
            return std::nullopt;
        }
        terms.push_back({instance.active,{}}); terms.push_back({instance.satisfied,{}});
    }
    if (!typeCheckTerms(context, terms, diagnostics)) { return std::nullopt; }
    PreferenceEncoding result; result.anonymous_violations = mkInt(0);
    for (const auto& name : declared_names) {
        if (name.empty()) {
            diagnostics.error(ErrorCode::E_TYPE,"preference: declared names must not be empty"); return std::nullopt;
        }
        result.named_violations.emplace(name,mkInt(0));
    }
    std::map<std::string,std::vector<ExprPtr>> groups;
    for (const auto& instance : instances) {
        groups[instance.name].push_back(mkOp(Op::ITE, {all({instance.active,not_(instance.satisfied)}),mkInt(1),mkInt(0)}));
    }
    for (auto& group : groups) {
        auto total = group.second.size() == 1 ? group.second.front() : mkOp(Op::ADD,std::move(group.second));
        if (group.first.empty()) { result.anonymous_violations = total; }
        else { result.named_violations[group.first] = total; }
    }
    return result;
}

std::optional<ExprPtr> preferenceMetric(
    const ConstraintModel& context, ExprPtr base, const PreferenceEncoding& preferences,
    bool minimize, Diagnostics& diagnostics) {
    if ((!sort(base, SortKind::INT) && !sort(base, SortKind::REAL))
        || !sort(preferences.anonymous_violations, SortKind::INT)) {
        diagnostics.error(ErrorCode::E_TYPE, "preference metric: requires numeric base and Int anonymous count");
        return std::nullopt;
    }
    std::vector<LocatedExpr> terms{{base,{}},{preferences.anonymous_violations,{}}};
    for (const auto& item : preferences.named_violations) {
        if (item.first.empty() || !sort(item.second,SortKind::INT)) {
            diagnostics.error(ErrorCode::E_TYPE,"preference metric: invalid named count"); return std::nullopt;
        }
        terms.push_back({item.second,{}});
    }
    if (!typeCheckTerms(context,terms,diagnostics)) { return std::nullopt; }
    auto penalty = preferences.anonymous_violations;
    if (base->sort.kind == SortKind::REAL) { penalty = mkOp(Op::TO_REAL,{penalty}); }
    auto result = binary(minimize ? Op::ADD : Op::SUB,base,penalty);
    if (!typeCheckTerms(context,{{result,{}}},diagnostics)) { return std::nullopt; }
    return result;
}
} // namespace SOMTParser::Uir::Hir::Planning
