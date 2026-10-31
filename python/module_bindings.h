#pragma once
#include <somtparser/translation/module.h>
#include "hir_bindings.h"
#include <sstream>

namespace SomtPythonModule {
namespace L = SOMTParser::Lang;
namespace H = SOMTParser::Uir::Hir;
namespace py = pybind11;

inline std::string checkedSmt(const H::ConstraintModel& model) {
    SOMTParser::TranslateOptions options;
    options.omt_dialect = SOMTParser::Lower::OmtDialect::Z3;
    const auto result = SOMTParser::translate(model, options);
    if (!result.ok()) {
        std::string error = "module relation lowering failed";
        for (const auto& d : result.diagnostics().all()) { error += ": " + d.message; }
        throw py::value_error(error);
    }
    return result.toSmt2();
}

inline py::dict expression(const H::ExprPtr& value) {
    py::dict out;
    out["sort"] = H::toString(value->sort);
    out["kind"] = static_cast<int>(value->kind);
    out["name"] = value->name;
    out["bool_value"] = value->bool_value;
    out["op"] = static_cast<int>(value->op);
    out["indices"] = value->indices;
    py::list args;
    for (const auto& child : value->args) { args.append(expression(child)); }
    out["args"] = args;
    return out;
}

void bind(py::module_& m);

} // namespace SomtPythonModule
