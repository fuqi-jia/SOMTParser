#include "somtparser/hir/packed_scalar_io.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/ir/dag.h"

#include <algorithm>
#include <limits>
#include <ostream>
#include <unordered_set>

namespace SOMTParser::Uir::Hir {
namespace {
bool integerLiteral(const ExprPtr& value) {
    if (!value || value->kind != ExprKind::LIT_INT || value->sort.kind != SortKind::INT
        || !value->args.empty() || value->name.empty()) { return false; }
    const auto& text = value->name;
    const std::size_t first = text.front() == '-' ? 1 : 0;
    if (first == text.size() || (text.size() > first + 1 && text[first] == '0')) { return false; }
    return std::all_of(text.begin() + first, text.end(),
                       [](char c) { return c >= '0' && c <= '9'; });
}
void writeInteger(const ExprPtr& value, std::ostream& out) {
    if (value->name.front() == '-') { out << "(- " << value->name.substr(1) << ')'; }
    else { out << value->name; }
}
std::string canonical(const std::string& name) {
    if (name.size() >= 2 && name.front() == '|' && name.back() == '|') {
        return name.substr(1, name.size() - 2);
    }
    return name;
}
}

ScalarRangeIndex::ScalarRangeIndex(const ConstraintModel& model) : model_(model) {
    for (std::size_t i = 0; i < model.scalar_var_ranges.size(); ++i) {
        prefixes_[model.scalar_var_ranges[i].prefix].push_back(i);
    }
}

const ScalarVarRange* ScalarRangeIndex::find(const std::string& name,
                                             std::uint64_t* range_id,
                                             std::uint64_t* offset) const {
    if (name.empty() || name.back() != ']') { return nullptr; }
    const auto open = name.rfind('[');
    if (open == std::string::npos) { return nullptr; }
    const auto found = prefixes_.find(std::string_view(name.data(), open + 1));
    if (found == prefixes_.end()) { return nullptr; }
    for (const auto i : found->second) {
        const auto& range = model_.scalar_var_ranges[i];
        std::uint64_t value = 0;
        if (!range.contains(name, &value)) { continue; }
        if (range_id) { *range_id = i; }
        if (offset) { *offset = value - range.first; }
        return &range;
    }
    return nullptr;
}

bool validatePackedScalarModel(const ConstraintModel& model, Diagnostics& diagnostics) {
    if (model.scalar_var_ranges.empty() && !model.packed_function_calls) { return true; }
    bool ok = true;
    const auto fail = [&](const std::string& message, const SourceLoc& loc = SourceLoc{}) {
        diagnostics.error(ErrorCode::E_TYPE, message, loc);
        ok = false;
    };
    if (!model.bool_var_ranges.empty() || !model.packed_bool_clauses.empty() || model.packed_linear_rows) {
        fail("compact scalar HIR cannot mix packed clause or numeric-row storage");
    }
    std::unordered_map<std::string, std::vector<const ScalarVarRange*>> prior;
    for (const auto& range : model.scalar_var_ranges) {
        if (range.prefix.empty() || range.prefix.back() != '[' || range.suffix != "]"
            || range.prefix.find_first_of("|\\\n\r\t") != std::string::npos
            || range.count == 0 || range.sort.kind != SortKind::INT
            || range.count - 1 > std::numeric_limits<std::uint64_t>::max() - range.first
            || !integerLiteral(range.lower_bound) || !integerLiteral(range.upper_bound)) {
            fail("compact scalar range has an invalid indexed name, interval, sort, or integer bound", range.loc);
            continue;
        }
        for (const auto previous : prior[range.prefix]) {
            if (range.first <= previous->first + previous->count - 1
                && previous->first <= range.first + range.count - 1) {
                fail("compact scalar ranges overlap", range.loc);
            }
        }
        prior[range.prefix].push_back(&range);
    }
    if (!ok) { return false; }
    ScalarRangeIndex ranges(model);
    const auto collision = [&](const std::string& name, const SourceLoc& loc) {
        if (ranges.find(canonical(name))) {
            fail("compact scalar range collides with declaration '" + name + "'", loc);
        }
    };
    for (const auto& declaration : model.decls) { collision(declaration.name, declaration.loc); }
    for (const auto& function : model.funs) { collision(function.name, function.loc); }
    for (const auto& datatype : model.datatypes) {
        collision(datatype.name, datatype.loc);
        for (const auto& constructor : datatype.constructors) {
            collision(constructor.name, datatype.loc);
            collision("is-" + constructor.name, datatype.loc);
            for (const auto& selector : constructor.selectors) { collision(selector.name, datatype.loc); }
        }
    }
    for (const auto& sort : model.uninterpreted_sorts) { collision(sort.name, sort.loc); }
    for (const auto& objective : model.objectives) {
        if (!objective.name.empty()) { collision(objective.name, objective.loc); }
    }
    if (!model.packed_function_calls) { return ok; }
    std::unordered_map<std::string_view, const FunDecl*> functions;
    for (const auto& function : model.funs) { functions.emplace(function.name, &function); }
    for (const auto& batch : model.packed_function_calls->batches) {
        const auto found = functions.find(batch.function);
        if (found == functions.end() || found->second->result.kind != SortKind::BOOL
            || batch.arity == 0 || found->second->params.size() != batch.arity
            || batch.arguments.size() % batch.arity != 0) {
            fail("packed function calls have an undeclared/non-Boolean function or malformed arity", batch.loc);
            continue;
        }
        for (const auto& constant : batch.constants) {
            if (!integerLiteral(constant)
                && (!constant || constant->kind != ExprKind::LIT_BOOL
                    || constant->sort.kind != SortKind::BOOL || !constant->args.empty())) {
                fail("packed function-call constant is not an exact Int/Bool literal", batch.loc);
            }
        }
        for (std::size_t i = 0; i < batch.arguments.size(); ++i) {
            const auto& argument = batch.arguments[i];
            const Sort* sort = nullptr;
            if (argument.source == PackedScalarArgument::DECLARATION) {
                if (argument.offset < model.decls.size()) { sort = &model.decls[argument.offset].sort; }
            } else if (argument.source == PackedScalarArgument::CONSTANT) {
                if (argument.offset < batch.constants.size() && batch.constants[argument.offset]) {
                    sort = &batch.constants[argument.offset]->sort;
                }
            } else if (argument.source < model.scalar_var_ranges.size()) {
                const auto& range = model.scalar_var_ranges[argument.source];
                if (argument.offset < range.count) { sort = &range.sort; }
            }
            if (!sort || !sameSort(*sort, found->second->params[i % batch.arity])) {
                fail("packed function call has an out-of-range or ill-sorted argument", batch.loc);
                break;
            }
        }
    }
    return ok;
}

ConstraintModelPtr packedScalarPreamble(const ConstraintModel& model, Diagnostics& diagnostics) {
    if (!validatePackedScalarModel(model, diagnostics)) { return {}; }
    auto result = std::make_shared<ConstraintModel>(model);
    result->scalar_var_ranges.clear();
    result->packed_function_calls.reset();
    ScalarRangeIndex ranges(model);
    std::unordered_set<std::string> declared;
    for (const auto& declaration : model.decls) { declared.insert(declaration.name); }
    std::vector<ExprPtr> todo;
    for (const auto& declaration : model.decls) {
        if (declaration.lower_bound) { todo.push_back(declaration.lower_bound); }
        if (declaration.upper_bound) { todo.push_back(declaration.upper_bound); }
    }
    for (const auto& function : model.funs) { if (function.body) { todo.push_back(function.body); } }
    for (const auto& constraint : model.constraints) { todo.push_back(constraint.formula); }
    for (const auto& objective : model.objectives) { todo.push_back(objective.term); }
    std::unordered_set<const Expr*> visited;
    while (!todo.empty()) {
        const auto expression = std::move(todo.back());
        todo.pop_back();
        if (!expression || !visited.insert(expression.get()).second) { continue; }
        if (expression->kind == ExprKind::IDENT && !declared.count(expression->name)) {
            if (const auto range = ranges.find(expression->name)) {
                VarDecl declaration;
                declaration.name = expression->name;
                declaration.sort = range->sort;
                declaration.loc = range->loc;
                result->decls.push_back(std::move(declaration));
                declared.insert(expression->name);
            }
        }
        for (const auto& child : expression->args) { todo.push_back(child); }
    }
    return result;
}

bool writePackedScalarDeclarationsSmt2(const ConstraintModel& model,
                                      Lower::HirToParser& lowering,
                                      std::ostream& out, Diagnostics& diagnostics) {
    if (!validatePackedScalarModel(model, diagnostics)) { return false; }
    const auto& declared = lowering.varMap();
    for (const auto& range : model.scalar_var_ranges) {
        for (std::uint64_t offset = 0; offset < range.count; ++offset) {
            const auto name = range.name(offset);
            if (declared.find(name) == declared.end()) {
                out << "(declare-const " << smtSymbol(name) << " Int)\n";
            }
            if (!out) {
                diagnostics.error(ErrorCode::E_IO, "compact scalar declaration output failed", range.loc);
                return false;
            }
        }
    }
    return true;
}

bool writePackedScalarsSmt2(const ConstraintModel& model, Lower::HirToParser& lowering,
                            std::ostream& out, Diagnostics& diagnostics) {
    if (!validatePackedScalarModel(model, diagnostics)) { return false; }
    const auto& preamble_variables = lowering.varMap();
    const auto scalarSymbol = [&](const ScalarVarRange& range, std::uint64_t offset) {
        const auto name = range.name(offset);
        const auto found = preamble_variables.find(name);
        return found == preamble_variables.end() ? smtSymbol(name)
                                                : smtSymbol(found->second->getName());
    };
    for (const auto& range : model.scalar_var_ranges) {
        for (std::uint64_t offset = 0; offset < range.count; ++offset) {
            const std::string symbol = scalarSymbol(range, offset);
            out << "(assert (<= ";
            writeInteger(range.lower_bound, out);
            out << ' ' << symbol << ' ';
            writeInteger(range.upper_bound, out);
            out << "))\n";
            if (!out) {
                diagnostics.error(ErrorCode::E_IO, "compact scalar SMT output failed", range.loc);
                return false;
            }
        }
    }
    if (!model.packed_function_calls) { return static_cast<bool>(out); }
    for (const auto& batch : model.packed_function_calls->batches) {
        const auto function = smtSymbol(lowering.emittedSymbolName(batch.function, diagnostics));
        if (diagnostics.hasErrors()) { return false; }
        for (std::size_t start = 0; start < batch.arguments.size(); start += batch.arity) {
            out << "(assert (" << function;
            for (std::size_t slot = 0; slot < batch.arity; ++slot) {
                const auto& argument = batch.arguments[start + slot];
                out << ' ';
                if (argument.source == PackedScalarArgument::DECLARATION) {
                    const auto& declaration = model.decls[argument.offset];
                    const auto found = preamble_variables.find(declaration.name);
                    if (found == preamble_variables.end() || !found->second) {
                        diagnostics.error(ErrorCode::E_INTERNAL, "packed argument has no preamble declaration", batch.loc);
                        return false;
                    }
                    out << smtSymbol(found->second->getName());
                } else if (argument.source == PackedScalarArgument::CONSTANT) {
                    const auto& constant = batch.constants[argument.offset];
                    if (constant->kind == ExprKind::LIT_BOOL) { out << (constant->bool_value ? "true" : "false"); }
                    else { writeInteger(constant, out); }
                } else {
                    out << scalarSymbol(model.scalar_var_ranges[argument.source], argument.offset);
                }
            }
            out << "))\n";
            if (!out) {
                diagnostics.error(ErrorCode::E_IO, "packed function-call SMT output failed", batch.loc);
                return false;
            }
        }
    }
    return true;
}

} // namespace SOMTParser::Uir::Hir
