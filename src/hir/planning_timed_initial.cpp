#include "somtparser/hir/planning_timed_initial.h"

namespace SOMTParser::Uir::Hir::Planning {
namespace {
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
bool sorted(const ExprPtr& term, SortKind sort, Diagnostics& diagnostics) {
    if (term && term->sort.kind == sort) { return true; }
    diagnostics.error(ErrorCode::E_TYPE, "timed initial planning construction has a missing or ill-sorted term");
    return false;
}
bool valid(const std::vector<TemporalHappening>& happenings, Diagnostics& diagnostics) {
    for (const auto& happening : happenings) {
        if (!sorted(happening.active, SortKind::BOOL, diagnostics)
            || !sorted(happening.time, SortKind::REAL, diagnostics)) { return false; }
    }
    return true;
}
} // namespace

std::optional<TimedInitialEncoding> encodeTimedInitialLiterals(
    const std::vector<TemporalHappening>& happenings,
    const std::vector<TimedInitialLiteral>& events,
    const std::string& ownerPrefix, Diagnostics& diagnostics) {
    if (!valid(happenings, diagnostics)) { return std::nullopt; }
    for (const auto& event : events) {
        if (!sorted(event.time, SortKind::REAL, diagnostics) || event.proposition.empty()) {
            diagnostics.error(ErrorCode::E_TYPE, "timed initial literal requires a canonical basic proposition");
            return std::nullopt;
        }
    }
    TimedInitialEncoding result;
    for (std::size_t i = 0; i < events.size(); ++i) {
        const auto& event = events[i];
        result.constraints.push_back(mkOp(Op::GT, {event.time, mkReal("0")}));
        std::vector<ExprPtr> matches;
        for (const auto& happening : happenings) {
            const auto match = all({happening.active, mkOp(Op::EQ, {happening.time, event.time})});
            matches.push_back(match);
            TemporalEndpointAccess access;
            access.active = match;
            access.time = happening.time;
            access.owner_id = ownerPrefix + std::to_string(i);
            (event.value ? access.propositionAdds : access.propositionDeletes).insert(event.proposition);
            result.accesses.push_back(std::move(access));
        }
        result.constraints.push_back(any(matches));
        result.matches.push_back(std::move(matches));
    }
    return result;
}

std::optional<StableGoalMakespan> encodeStableGoalMakespan(
    const std::vector<TemporalHappening>& happenings,
    const std::vector<ExprPtr>& goals, const ExprPtr& lastActionEnd,
    Diagnostics& diagnostics) {
    if (!valid(happenings, diagnostics) || !sorted(lastActionEnd, SortKind::REAL, diagnostics)) {
        return std::nullopt;
    }
    if (goals.size() != happenings.size() + 1) {
        diagnostics.error(ErrorCode::E_TYPE, "stable-goal makespan requires one goal sample per complete state");
        return std::nullopt;
    }
    for (const auto& goal : goals) {
        if (!sorted(goal, SortKind::BOOL, diagnostics)) { return std::nullopt; }
    }
    StableGoalMakespan result;
    std::vector<ExprPtr> endpoints{mkOp(Op::EQ, {lastActionEnd, mkReal("0")})};
    for (const auto& happening : happenings) {
        endpoints.push_back(all({happening.active, mkOp(Op::EQ, {lastActionEnd, happening.time})}));
    }
    result.constraints.push_back(any(std::move(endpoints)));
    result.constraints.push_back(goals.back());
    // Reverse iteration replaces a later feasible boundary with each earlier
    // one. Inactive slots have no event boundary and never become candidates.
    ExprPtr suffix = goals.back();
    ExprPtr earliest = lastActionEnd;
    std::vector<ExprPtr> candidates;
    for (std::size_t i = happenings.size(); i-- > 0;) {
        const auto eligible = all({happenings[i].active,
            mkOp(Op::GE, {happenings[i].time, lastActionEnd}), suffix});
        candidates.push_back(eligible);
        earliest = mkOp(Op::ITE, {eligible, happenings[i].time, earliest});
        suffix = all({goals[i], suffix});
    }
    const auto initiallyDone = all({mkOp(Op::EQ, {lastActionEnd, mkReal("0")}), suffix});
    candidates.push_back(initiallyDone);
    result.constraints.push_back(any(std::move(candidates)));
    result.time = mkOp(Op::ITE, {initiallyDone, mkReal("0"), earliest});
    return result;
}

} // namespace SOMTParser::Uir::Hir::Planning
