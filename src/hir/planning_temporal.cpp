#include "somtparser/hir/planning_temporal.h"

#include <algorithm>

namespace SOMTParser::Uir::Hir::Planning {
namespace {

ExprPtr all(std::vector<ExprPtr> expressions) {
    if (expressions.empty()) { return mkBool(true); }
    if (expressions.size() == 1) { return expressions.front(); }
    return mkOp(Op::AND, std::move(expressions));
}

ExprPtr any(std::vector<ExprPtr> expressions) {
    if (expressions.empty()) { return mkBool(false); }
    if (expressions.size() == 1) { return expressions.front(); }
    return mkOp(Op::OR, std::move(expressions));
}

ExprPtr implies(ExprPtr condition, ExprPtr conclusion) {
    return mkOp(Op::IMPLIES, {std::move(condition), std::move(conclusion)});
}

bool hasSort(const ExprPtr& expression, SortKind sort, Diagnostics& diagnostics,
             const char* role) {
    if (expression && expression->sort.kind == sort) { return true; }
    diagnostics.error(ErrorCode::E_TYPE, std::string("temporal planning: ") + role
        + (sort == SortKind::REAL ? " must have Real sort" : " must have Bool sort"));
    return false;
}

bool validateHappenings(const std::vector<TemporalHappening>& happenings,
                        Diagnostics& diagnostics) {
    for (const auto& happening : happenings) {
        if (!hasSort(happening.active, SortKind::BOOL, diagnostics, "happening activation")
            || !hasSort(happening.time, SortKind::REAL, diagnostics, "happening time")) {
            return false;
        }
    }
    return true;
}

bool validateOccurrence(const DurativeOccurrence& occurrence, Diagnostics& diagnostics) {
    return hasSort(occurrence.active, SortKind::BOOL, diagnostics, "occurrence activation")
        && hasSort(occurrence.start, SortKind::REAL, diagnostics, "start time")
        && hasSort(occurrence.end, SortKind::REAL, diagnostics, "end time");
}

bool validateSamples(const TemporalConditionSamples& samples, std::size_t size,
                     Diagnostics& diagnostics) {
    const auto check = [&](const std::vector<ExprPtr>& expressions, std::size_t expected) {
        if (!expressions.empty() && expressions.size() != expected) {
            diagnostics.error(ErrorCode::E_TYPE,
                "temporal planning: condition sample count does not match the happening grid");
            return false;
        }
        for (const auto& expression : expressions) {
            if (!hasSort(expression, SortKind::BOOL, diagnostics, "condition sample")) { return false; }
        }
        return true;
    };
    return check(samples.atStart, size) && check(samples.atEnd, size)
        && check(samples.overAll, size == 0 ? 0 : size - 1);
}

ExprPtr isEndpoint(const TemporalHappening& happening, const ExprPtr& time) {
    return all({happening.active, mkOp(Op::EQ, {happening.time, time})});
}

// State is constant on this open interval. The start endpoint's post-state
// is included, and the end endpoint's post-state is excluded.
ExprPtr spansInterval(const std::vector<TemporalHappening>& happenings,
                      const DurativeOccurrence& occurrence, std::size_t index) {
    return all({happenings[index].active, happenings[index + 1].active,
        mkOp(Op::LE, {occurrence.start, happenings[index].time}),
        mkOp(Op::LT, {happenings[index].time, occurrence.end})});
}

std::vector<ExprPtr> sampledConditions(const std::vector<TemporalHappening>& happenings,
                                      const DurativeOccurrence& occurrence,
                                      const TemporalConditionSamples& samples) {
    std::vector<ExprPtr> result;
    for (std::size_t index = 0; index < happenings.size(); ++index) {
        if (!samples.atStart.empty()) {
            result.push_back(implies(isEndpoint(happenings[index], occurrence.start), samples.atStart[index]));
        }
        if (!samples.atEnd.empty()) {
            result.push_back(implies(isEndpoint(happenings[index], occurrence.end), samples.atEnd[index]));
        }
        if (index + 1 < happenings.size() && !samples.overAll.empty()) {
            result.push_back(implies(spansInterval(happenings, occurrence, index), samples.overAll[index]));
        }
    }
    return result;
}

bool intersects(const std::set<std::string>& left, const std::set<std::string>& right) {
    auto a = left.begin();
    auto b = right.begin();
    while (a != left.end() && b != right.end()) {
        if (*a == *b) { return true; }
        if (*a < *b) { ++a; } else { ++b; }
    }
    return false;
}

bool interfere(const TemporalEndpointAccess& a, const TemporalEndpointAccess& b) {
    if (intersects(a.propositionReads, b.propositionAdds)
        || intersects(a.propositionReads, b.propositionDeletes)
        || intersects(b.propositionReads, a.propositionAdds)
        || intersects(b.propositionReads, a.propositionDeletes)
        || intersects(a.propositionAdds, b.propositionDeletes)
        || intersects(b.propositionAdds, a.propositionDeletes)
        || intersects(a.numericReads, b.numericWrites)
        || intersects(b.numericReads, a.numericWrites)) { return true; }
    for (const auto& variable : a.numericWrites) {
        if (b.numericWrites.count(variable)
            && (!a.additiveWrites.count(variable) || !b.additiveWrites.count(variable))) {
            return true;
        }
    }
    return false;
}

} // namespace

std::optional<std::vector<ExprPtr>> encodeRationalTime(
    const RationalTimeCoordinate& coordinate, const ExprPtr& active,
    Diagnostics& diagnostics) {
    if (!hasSort(coordinate.time, SortKind::REAL, diagnostics, "rational time")
        || !hasSort(active, SortKind::BOOL, diagnostics, "rational time activation")) { return std::nullopt; }
    if (!coordinate.numerator || coordinate.numerator->sort.kind != SortKind::INT
        || !coordinate.denominator || coordinate.denominator->sort.kind != SortKind::INT) {
        diagnostics.error(ErrorCode::E_TYPE, "temporal planning: rational time witnesses must have Int sort");
        return std::nullopt;
    }
    return std::vector<ExprPtr>{implies(active, all({
        mkOp(Op::GT, {coordinate.denominator, mkInt(0)}),
        mkOp(Op::EQ, {mkOp(Op::MUL, {coordinate.time, mkOp(Op::TO_REAL, {coordinate.denominator})}),
            mkOp(Op::TO_REAL, {coordinate.numerator})})}))};
}

std::optional<std::vector<ExprPtr>> encodeHappeningOrder(
    const std::vector<TemporalHappening>& happenings, Diagnostics& diagnostics) {
    if (!validateHappenings(happenings, diagnostics)) { return std::nullopt; }
    std::vector<ExprPtr> result;
    for (std::size_t i = 0; i < happenings.size(); ++i) {
        result.push_back(implies(happenings[i].active, mkOp(Op::GT, {happenings[i].time, mkReal("0")})));
        if (i != 0) {
            result.push_back(implies(happenings[i].active,
                all({happenings[i - 1].active, mkOp(Op::LT, {happenings[i - 1].time, happenings[i].time})})));
        }
    }
    return result;
}

std::optional<DurativeEncoding> encodeDurativeOccurrence(
    const std::vector<TemporalHappening>& happenings,
    const DurativeOccurrence& occurrence,
    const TemporalConditionSamples& conditions, Diagnostics& diagnostics) {
    if (!validateHappenings(happenings, diagnostics)
        || !validateOccurrence(occurrence, diagnostics)
        || !validateSamples(conditions, happenings.size(), diagnostics)) { return std::nullopt; }
    DurativeEncoding result;
    result.duration = mkOp(Op::SUB, {occurrence.end, occurrence.start});
    std::vector<ExprPtr> starts, ends;
    for (const auto& happening : happenings) {
        starts.push_back(isEndpoint(happening, occurrence.start));
        ends.push_back(isEndpoint(happening, occurrence.end));
    }
    auto required = sampledConditions(happenings, occurrence, conditions);
    required.push_back(any(std::move(starts)));
    required.push_back(any(std::move(ends)));
    required.push_back(mkOp(Op::GE, {result.duration, mkReal("0")}));
    result.constraints.push_back(implies(occurrence.active, all(std::move(required))));
    return result;
}

ExprPtr temporalEffectGuard(
    const std::vector<TemporalHappening>& happenings,
    const DurativeOccurrence& occurrence,
    const TemporalConditionSamples& conditions,
    TemporalEffectEndpoint endpoint, Diagnostics& diagnostics) {
    if (!validateHappenings(happenings, diagnostics)
        || !validateOccurrence(occurrence, diagnostics)
        || !validateSamples(conditions, happenings.size(), diagnostics)) { return nullptr; }
    if (endpoint != TemporalEffectEndpoint::START && endpoint != TemporalEffectEndpoint::END) {
        diagnostics.error(ErrorCode::E_TYPE, "temporal planning: invalid effect endpoint");
        return nullptr;
    }
    if (endpoint == TemporalEffectEndpoint::START
        && (!conditions.atEnd.empty() || !conditions.overAll.empty())) {
        diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
            "temporal planning: a start effect cannot depend on end or interval conditions");
        return nullptr;
    }
    auto conditionsAtOccurrence = sampledConditions(happenings, occurrence, conditions);
    conditionsAtOccurrence.push_back(occurrence.active);
    return all(std::move(conditionsAtOccurrence));
}

std::optional<std::vector<ExprPtr>> encodeTemporalInterference(
    const std::vector<TemporalEndpointAccess>& endpoints, Diagnostics& diagnostics) {
    for (const auto& endpoint : endpoints) {
        if (!hasSort(endpoint.active, SortKind::BOOL, diagnostics, "endpoint activation")
            || !hasSort(endpoint.time, SortKind::REAL, diagnostics, "endpoint time")) { return std::nullopt; }
        if (!std::includes(endpoint.numericWrites.begin(), endpoint.numericWrites.end(),
                           endpoint.additiveWrites.begin(), endpoint.additiveWrites.end())) {
            diagnostics.error(ErrorCode::E_TYPE,
                "temporal planning: additive writes must be a subset of numeric writes");
            return std::nullopt;
        }
    }
    std::vector<ExprPtr> result;
    for (std::size_t i = 0; i < endpoints.size(); ++i) {
        for (std::size_t j = i + 1; j < endpoints.size(); ++j) {
            if (!endpoints[i].owner_id.empty() && endpoints[i].owner_id == endpoints[j].owner_id) { continue; }
            if (!interfere(endpoints[i], endpoints[j])) { continue; }
            result.push_back(mkOp(Op::NOT, {all({endpoints[i].active, endpoints[j].active,
                mkOp(Op::EQ, {endpoints[i].time, endpoints[j].time})})}));
        }
    }
    return result;
}

} // namespace SOMTParser::Uir::Hir::Planning
