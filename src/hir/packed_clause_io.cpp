#include "somtparser/hir/packed_clause_io.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/hir/soft_objectives.h"

#include <cstdint>
#include <limits>
#include <ostream>
#include <string>

namespace SOMTParser::Uir::Hir {
namespace {
void fail(Diagnostics& diags, const std::string& message) {
    diags.error(ErrorCode::E_INTERNAL, message);
}
bool validWeight(const std::string& bytes, std::uint64_t begin, std::uint64_t end) {
    if (begin >= end || end > bytes.size() || bytes[begin] < '1' || bytes[begin] > '9') return false;
    for (std::uint64_t i = begin + 1; i < end; ++i)
        if (bytes[i] < '0' || bytes[i] > '9') return false;
    return true;
}
}

bool validatePackedBoolClauseModel(const ConstraintModel& model, Diagnostics& diags) {
    if (!model.decls.empty() || !model.funs.empty() || !model.datatypes.empty()
        || !model.constraints.empty() || !model.objectives.empty()
        || !model.uninterpreted_sorts.empty() || model.bool_var_ranges.empty()
        || model.packed_bool_clauses.empty()) {
        fail(diags, "packed SMT-LIB writer requires a packed-only Boolean clause model");
        return false;
    }
    if (!typeCheck(model, diags)) return false;
    for (const BoolVarRange& range : model.bool_var_ranges) {
        if (range.sort.kind != SortKind::BOOL || range.prefix.empty() || range.first == 0
            || (range.count != 0
                && range.first > std::numeric_limits<std::uint64_t>::max() - (range.count - 1))) {
            fail(diags, "packed SMT-LIB writer encountered an invalid Boolean variable range");
            return false;
        }
    }
    for (const PackedBoolClauseBatch& batch : model.packed_bool_clauses) {
        if (batch.variable_range >= model.bool_var_ranges.size()
            || batch.clause_offsets.size() != batch.source_lines.size() + 1
            || batch.weight_offsets.size() != batch.source_lines.size() + 1
            || batch.clause_offsets.empty() || batch.weight_offsets.empty()
            || batch.clause_offsets.front() != 0
            || batch.clause_offsets.back() != batch.literals.size()
            || batch.weight_offsets.front() != 0
            || batch.weight_offsets.back() != batch.weight_bytes.size()) {
            fail(diags, "packed SMT-LIB writer encountered malformed clause index arrays");
            return false;
        }
        const auto& range = model.bool_var_ranges[batch.variable_range];
        for (std::size_t c = 0; c < batch.source_lines.size(); ++c) {
            const auto begin = batch.clause_offsets[c], end = batch.clause_offsets[c + 1];
            const auto wb = batch.weight_offsets[c], we = batch.weight_offsets[c + 1];
            if (begin > end || end > batch.literals.size() || wb > we
                || we > batch.weight_bytes.size()
                || (wb != we && !validWeight(batch.weight_bytes, wb, we))) {
                fail(diags, "packed SMT-LIB writer encountered invalid clause spans or soft weight");
                return false;
            }
            for (std::uint64_t i = begin; i < end; ++i) {
                const auto literal = batch.literals[i];
                if (literal == 0 || literal == std::numeric_limits<std::int64_t>::min()) {
                    fail(diags, "packed SMT-LIB writer encountered an invalid signed literal");
                    return false;
                }
                const std::uint64_t magnitude = static_cast<std::uint64_t>(literal < 0 ? -literal : literal);
                if (magnitude > range.count) {
                    fail(diags, "packed SMT-LIB writer encountered an out-of-range literal");
                    return false;
                }
            }
        }
    }
    return true;
}

bool writePackedBoolClausesSmt2(const ConstraintModel& model,
                                std::ostream& out,
                                Diagnostics& diags,
                                const std::string& gomt_soft_objective) {
    if (!validatePackedBoolClauseModel(model, diags)) return false;
    if (!gomt_soft_objective.empty()) {
        if (!isSoftGroupSymbol(gomt_soft_objective)) {
            fail(diags, "packed GOMT objective must be an SMT symbol spelling");
            return false;
        }
        const auto identity = gomt_soft_objective.front() == '|'
            ? gomt_soft_objective.substr(1, gomt_soft_objective.size() - 2) : gomt_soft_objective;
        for (const auto& range : model.bool_var_ranges) {
            if (range.contains(identity)) {
                fail(diags, "packed GOMT objective collides with a Boolean variable");
                return false;
            }
        }
    }
    for (const BoolVarRange& range : model.bool_var_ranges)
        for (std::uint64_t offset = 0; offset < range.count; ++offset)
            out << "(declare-const " << range.name(offset) << " Bool)\n";
    for (const PackedBoolClauseBatch& batch : model.packed_bool_clauses) {
        const auto& range = model.bool_var_ranges[batch.variable_range];
        for (std::size_t c = 0; c < batch.source_lines.size(); ++c) {
            const auto begin = batch.clause_offsets[c], end = batch.clause_offsets[c + 1];
            const auto wb = batch.weight_offsets[c], we = batch.weight_offsets[c + 1];
            out << (wb == we ? "(assert " : "(assert-soft ");
            // SMT-LIB does not admit a zero-argument application of `or`.
            // An empty hard clause is inconsistent; an empty soft clause
            // contributes its entire weight for every assignment.
            out << (begin == end ? "false" : "(or");
            for (std::uint64_t i = begin; i < end; ++i) {
                const std::int64_t literal = batch.literals[i];
                const std::uint64_t magnitude = static_cast<std::uint64_t>(literal < 0 ? -literal : literal);
                out << ' ';
                if (literal < 0) out << "(not ";
                out << range.prefix << (range.first + magnitude - 1);
                if (literal < 0) out << ')';
            }
            if (begin != end) out << ')';
            if (wb == we) out << ")\n";
            else {
                out << " :weight " << batch.weight_bytes.substr(wb, we - wb);
                if (!gomt_soft_objective.empty()) out << " :objective " << gomt_soft_objective;
                out << ")\n";
            }
            if (!out) { fail(diags, "packed SMT-LIB writer failed while writing output"); return false; }
        }
    }
    if (!out) { fail(diags, "packed SMT-LIB writer failed while writing output"); return false; }
    return true;
}

} // namespace SOMTParser::Uir::Hir
