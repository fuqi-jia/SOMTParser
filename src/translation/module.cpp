#include "somtparser/translation/module.h"
#include "somtparser/hir/typecheck.h"
#include <filesystem>
#include <fstream>
#include <sstream>
#include <unordered_set>

namespace SOMTParser::Lang {
namespace H = Uir::Hir;

ModuleOutcome Language::parseModule(const SourceUnit&) {
    ModuleOutcome out;
    out.diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                          "module import is not implemented for '" + id() + "'");
    return out;
}

ModuleOutcome Language::parseModule(const SourceUnit& unit, const ParseOptions& opts) {
    if (!opts.options.empty() || opts.strict) {
        ModuleOutcome out;
        out.diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "module reader options are not supported for '" + id() + "'");
        return out;
    }
    return parseModule(unit);
}

bool readModuleSource(const SourceUnit& unit, std::string& source,
                      Uir::Diagnostics& diagnostics) {
    if (!unit.inline_source.empty()) { source = unit.inline_source; return true; }
    std::error_code ec;
    std::ifstream in(unit.main_path, std::ios::binary);
    if (!in || std::filesystem::is_directory(unit.main_path, ec)) {
        diagnostics.error(Uir::ErrorCode::E_IO, "cannot read '" + unit.main_path + "'");
        return false;
    }
    std::ostringstream text;
    text << in.rdbuf();
    if (in.bad()) {
        diagnostics.error(Uir::ErrorCode::E_IO, "failed reading '" + unit.main_path + "'");
        return false;
    }
    source = text.str();
    return true;
}

bool validateModule(const SourceModule& module, Uir::Diagnostics& diagnostics) {
    if (!H::typeCheck(module.known, diagnostics)) { return false; }
    for (const auto& system : module.systems) {
        if (system.name.empty()
            || !system.init || !system.trans || !system.invariant
            || !system.context.constraints.empty() || !system.context.objectives.empty()) {
            diagnostics.error(Uir::ErrorCode::E_INTERNAL, "invalid transition module structure");
            return false;
        }
        auto context = system.context;
        std::unordered_set<std::string> states;
        for (const auto& variable : system.variables) {
            if (variable.current == variable.next || !states.insert(variable.current).second
                || !states.insert(variable.next).second
                || (variable.role != "input" && variable.role != "output"
                    && variable.role != "local")) {
                diagnostics.error(Uir::ErrorCode::E_INTERNAL, "invalid state variable mapping");
                return false;
            }
            // typeCheck also verifies each mapped variable exists with its sort.
            H::Constraint check;
            check.formula = H::mkOp(H::Op::EQ, {
                H::mkIdent(variable.current, variable.sort),
                H::mkIdent(variable.next, variable.sort)});
            context.constraints.push_back(check);
        }
        std::vector<H::ExprPtr> relations{system.init, system.trans, system.invariant};
        relations.insert(relations.end(), system.outputs.begin(), system.outputs.end());
        relations.insert(relations.end(), system.bad.begin(), system.bad.end());
        for (const auto& relation : relations) {
            H::Constraint check; check.formula = relation;
            context.constraints.push_back(check);
        }
        if (!H::typeCheck(context, diagnostics)) { return false; }
    }
    auto context = module.known;
    for (const auto& call : module.unresolved) {
        if (call.predicate.empty()) {
            diagnostics.error(Uir::ErrorCode::E_INTERNAL, "unnamed external relation");
            return false;
        }
        for (const auto& argument : call.arguments) {
            if (!argument.array && argument.values.size() != 1) {
                diagnostics.error(Uir::ErrorCode::E_INTERNAL, "invalid external scalar argument");
                return false;
            }
            for (const auto& value : argument.values) {
                if (!value || !H::sameSort(argument.sort, value->sort)) {
                    diagnostics.error(Uir::ErrorCode::E_TYPE, "external argument sort mismatch");
                    return false;
                }
                H::Constraint check;
                check.formula = H::mkOp(H::Op::EQ, {value, value});
                context.constraints.push_back(check);
            }
        }
    }
    return H::typeCheck(context, diagnostics);
}

ModuleOutcome importModule(const SourceUnit& unit, const std::string& language,
                           const ParseOptions& opts) {
    ModuleOutcome out;
    auto& registry = LanguageRegistry::instance();
    Language* frontend = language.empty() ? registry.detect(unit) : registry.byId(language);
    if (!frontend) {
        out.diagnostics.error(Uir::ErrorCode::E_PARSE, "unknown source language for module import");
        return out;
    }
    if (!unit.data_paths.empty()) {
        out.diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "module import does not accept companion data files");
        return out;
    }
    try {
        out = frontend->parseModule(unit, opts);
        if (out.module && (!validateModule(*out.module, out.diagnostics)
                           || out.diagnostics.hasErrors())) { out.module.reset(); }
    } catch (const std::exception& e) {
        out.module.reset();
        out.diagnostics.error(Uir::ErrorCode::E_INTERNAL, std::string("module import: ") + e.what());
    }
    return out;
}
} // namespace SOMTParser::Lang
