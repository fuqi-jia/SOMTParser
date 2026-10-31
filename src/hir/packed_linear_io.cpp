#include "somtparser/hir/packed_linear_io.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/ir/dag.h"

#include <limits>
#include <ostream>

namespace SOMTParser::Uir::Hir {
namespace {

// Canonical finite decimals carry exact values without an exponent, a leading
// plus/zero, a trailing fractional zero, or negative zero. The MPS reader's
// exact decimal normalization produces this form before freezing the pool.
bool canonicalDecimal(const std::string& value) {
    if (value.empty()) { return false; }
    std::size_t i = value.front() == '-' ? 1 : 0;
    const std::size_t first = i;
    if (i == value.size()) { return false; }
    while (i < value.size() && value[i] >= '0' && value[i] <= '9') { ++i; }
    if (i == first || (i > first + 1 && value[first] == '0')) { return false; }
    if (i == value.size()) { return value != "-0"; }
    if (value[i++] != '.' || i == value.size() || value.back() == '0') { return false; }
    for (; i < value.size(); ++i) {
        if (value[i] < '0' || value[i] > '9') { return false; }
    }
    return true;
}

SourceLoc rowLoc(const PackedLinearRowBatch& batch, const PackedLinearRow& row) {
    SourceLoc loc;
    loc.file = batch.source_file;
    loc.line = row.source_line <= static_cast<std::uint32_t>(std::numeric_limits<int>::max())
        ? static_cast<int>(row.source_line) : 0;
    loc.column = 1;
    return loc;
}

std::string realLiteral(const std::string& value) {
    const bool negative = value.front() == '-';
    std::string magnitude = negative ? value.substr(1) : value;
    if (magnitude.find('.') == std::string::npos) { magnitude += ".0"; }
    return negative ? "(- " + magnitude + ")" : magnitude;
}

} // namespace

bool isPackedLinearBoundLiteral(const VarDecl& declaration, const ExprPtr& endpoint) {
    if ((declaration.sort.kind != SortKind::INT && declaration.sort.kind != SortKind::REAL)
        || !endpoint || !endpoint->args.empty()) { return false; }
    if (endpoint->kind == ExprKind::LIT_INT && sameSort(endpoint->sort, Sort::integer())) {
        // Empty names use the builder's machine-integer field, exactly as the
        // ordinary lowerer does. Textual integers retain arbitrary precision.
        return endpoint->name.empty()
            || (canonicalDecimal(endpoint->name) && endpoint->name.find('.') == std::string::npos);
    }
    return endpoint->kind == ExprKind::LIT_REAL && sameSort(endpoint->sort, Sort::real())
        && canonicalDecimal(endpoint->name);
}

bool writePackedLinearDeclarationsSmt2(const ConstraintModel& model,
                                       const std::vector<std::string>& column_symbols,
                                       Lower::HirToParser& lowering,
                                       std::ostream& out, Diagnostics& diags) {
    if (!model.packed_linear_rows || column_symbols.size() != model.decls.size()) {
        diags.error(ErrorCode::E_INTERNAL, "packed declaration writer has no storage or column symbol map");
        return false;
    }
    const auto& materialized = lowering.varMap();
    // Check the entire map before writing a prefix. No source spelling is
    // independently guessed by this complementary writer.
    for (std::size_t i = 0; i < model.decls.size(); ++i) {
        const auto& declaration = model.decls[i];
        const auto expected = smtSymbol(lowering.emittedSymbolName(declaration.name, diags));
        if (diags.hasErrors()) { return false; }
        if (column_symbols[i] != expected || expected.empty()) {
            diags.error(ErrorCode::E_INTERNAL, "packed declaration writer has an inconsistent column symbol", declaration.loc);
            return false;
        }
        if (materialized.find(declaration.name) == materialized.end()
            && declaration.sort.kind != SortKind::INT && declaration.sort.kind != SortKind::REAL) {
            diags.error(ErrorCode::E_INTERNAL, "packed declaration writer cannot defer a nonnumeric declaration", declaration.loc);
            return false;
        }
    }
    for (std::size_t i = 0; i < model.decls.size(); ++i) {
        const auto& declaration = model.decls[i];
        if (materialized.find(declaration.name) != materialized.end()) { continue; }
        out << "(declare-fun " << column_symbols[i] << " () "
            << (declaration.sort.kind == SortKind::INT ? "Int" : "Real") << ")\n";
        if (!out) {
            diags.error(ErrorCode::E_IO, "packed declaration writer failed while writing output", declaration.loc);
            return false;
        }
    }
    if (!out) {
        diags.error(ErrorCode::E_IO, "packed declaration writer failed while writing output");
        return false;
    }
    return true;
}

bool writePackedLinearBoundsSmt2(const ConstraintModel& model,
                                 const std::vector<std::string>& column_symbols,
                                 std::ostream& out, Diagnostics& diags) {
    if (!model.packed_linear_rows || column_symbols.size() != model.decls.size()) {
        diags.error(ErrorCode::E_INTERNAL, "packed bound writer has no storage or column symbol map");
        return false;
    }
    for (const auto& symbol : column_symbols) {
        if (symbol.empty()) {
            diags.error(ErrorCode::E_INTERNAL, "packed bound writer has an empty column symbol");
            return false;
        }
    }
    for (std::size_t i = 0; i < model.decls.size(); ++i) {
        const auto& declaration = model.decls[i];
        const auto write_bound = [&](const ExprPtr& endpoint, const char* relation) {
            if (!isPackedLinearBoundLiteral(declaration, endpoint)) { return; }
            out << "(assert (" << relation << ' ' << column_symbols[i] << ' ';
            if (endpoint->kind == ExprKind::LIT_REAL) {
                out << realLiteral(endpoint->name);
            } else {
                const auto value = endpoint->name.empty() ? std::to_string(endpoint->int_value) : endpoint->name;
                if (value.front() == '-') { out << "(- " << value.substr(1) << ')'; }
                else { out << value; }
            }
            out << "))\n";
        };
        write_bound(declaration.lower_bound, ">=");
        write_bound(declaration.upper_bound, "<=");
        if (!out) {
            diags.error(ErrorCode::E_IO, "packed bound writer failed while writing output", declaration.loc);
            return false;
        }
    }
    if (!out) {
        diags.error(ErrorCode::E_IO, "packed bound writer failed while writing output");
        return false;
    }
    return true;
}

bool validatePackedLinearRows(const ConstraintModel& model, Diagnostics& diags) {
    if (!model.packed_linear_rows) { return true; }
    const auto& data = *model.packed_linear_rows;
    for (std::size_t i = 0; i < data.numbers.size(); ++i) {
        if (!canonicalDecimal(data.numbers[i])) {
            diags.error(ErrorCode::E_TYPE, "packed linear number " + std::to_string(i)
                + " is not an exact canonical finite decimal");
            return false;
        }
    }
    for (const auto& batch : data.batches) {
        std::uint64_t previous_end = 0;
        for (const auto& row : batch.rows) {
            const SourceLoc loc = rowLoc(batch, row);
            if (row.source_line == 0 || loc.line == 0) {
                diags.error(ErrorCode::E_INTERNAL,
                    "packed linear row source line is outside SourceLoc range", loc);
                return false;
            }
            if (row.begin != previous_end || row.begin > row.end || row.end > batch.terms.size()) {
                diags.error(ErrorCode::E_INTERNAL, "packed linear row has invalid term spans", loc);
                return false;
            }
            previous_end = row.end;
            switch (row.relation) {
            case LinearRowRelation::LE: case LinearRowRelation::GE:
            case LinearRowRelation::EQ: case LinearRowRelation::RANGE: break;
            default:
                diags.error(ErrorCode::E_INTERNAL, "packed linear row has an invalid relation", loc);
                return false;
            }
            if (row.rhs >= data.numbers.size()
                || (row.relation == LinearRowRelation::RANGE && row.upper >= data.numbers.size())) {
                diags.error(ErrorCode::E_INTERNAL, "packed linear row bound is outside its number pool", loc);
                return false;
            }
            for (std::uint64_t i = row.begin; i < row.end; ++i) {
                const auto& term = batch.terms[static_cast<std::size_t>(i)];
                if (term.column >= model.decls.size() || term.coefficient >= data.numbers.size()) {
                    diags.error(ErrorCode::E_INTERNAL,
                        "packed linear term has an out-of-range column or coefficient", loc);
                    return false;
                }
                const SortKind sort = model.decls[static_cast<std::size_t>(term.column)].sort.kind;
                if (sort != SortKind::INT && sort != SortKind::REAL) {
                    diags.error(ErrorCode::E_TYPE, "packed linear term requires an Int or Real column", loc);
                    return false;
                }
            }
        }
        if (previous_end != batch.terms.size()) {
            diags.error(ErrorCode::E_INTERNAL, "packed linear row spans do not cover the term pool");
            return false;
        }
    }
    return true;
}

bool writePackedLinearRowsSmt2(const ConstraintModel& model,
                               const std::vector<std::string>& column_symbols,
                               std::ostream& out, Diagnostics& diags) {
    // Validate before writing a prefix, including direct callers outside the
    // translation pipeline. Successful output never omits malformed rows.
    if (!validatePackedLinearRows(model, diags)) { return false; }
    if (!model.packed_linear_rows || column_symbols.size() != model.decls.size()) {
        diags.error(ErrorCode::E_INTERNAL, "packed linear writer has no storage or column symbol map");
        return false;
    }
    for (const auto& symbol : column_symbols) {
        if (symbol.empty()) {
            diags.error(ErrorCode::E_INTERNAL, "packed linear writer has an empty column symbol");
            return false;
        }
    }
    const auto& data = *model.packed_linear_rows;
    std::vector<std::string> literals;
    literals.reserve(data.numbers.size());
    for (const auto& number : data.numbers) { literals.push_back(realLiteral(number)); }
    for (const auto& batch : data.batches) {
        for (const auto& row : batch.rows) {
            const auto sum = [&]() {
                std::size_t active = 0;
                for (std::uint64_t i = row.begin; i < row.end; ++i) {
                    active += data.numbers[batch.terms[static_cast<std::size_t>(i)].coefficient] != "0";
                }
                if (active == 0) { out << "0.0"; return; }
                if (active > 1) { out << "(+"; }
                for (std::uint64_t i = row.begin; i < row.end; ++i) {
                    const auto& term = batch.terms[static_cast<std::size_t>(i)];
                    const auto& coefficient = data.numbers[term.coefficient];
                    if (coefficient == "0") { continue; }
                    if (active > 1) { out << ' '; }
                    if (coefficient == "1") { out << column_symbols[term.column]; }
                    else { out << "(* " << literals[term.coefficient] << ' '
                               << column_symbols[term.column] << ')'; }
                }
                if (active > 1) { out << ')'; }
            };
            out << "(assert ";
            if (row.relation == LinearRowRelation::RANGE) {
                out << "(and (<= " << literals[row.rhs] << ' ';
                sum();
                out << ") (<= ";
                sum();
                out << ' ' << literals[row.upper] << "))";
            } else {
                out << (row.relation == LinearRowRelation::LE ? "(<= "
                    : row.relation == LinearRowRelation::GE ? "(>= " : "(= ");
                sum();
                out << ' ' << literals[row.rhs] << ')';
            }
            out << ")\n";
            if (!out) {
                diags.error(ErrorCode::E_IO, "packed linear writer failed while writing output", rowLoc(batch, row));
                return false;
            }
        }
    }
    if (!out) {
        diags.error(ErrorCode::E_IO, "packed linear writer failed while writing output");
        return false;
    }
    return true;
}

} // namespace SOMTParser::Uir::Hir
