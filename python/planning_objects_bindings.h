#pragma once
#include "hir_bindings.h"
#include "somtparser/hir/planning_objects.h"

namespace SomtPythonPlanningObjects {
namespace py = pybind11;
namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
using SomtPythonHir::Expr;
using SOMTParser::Uir::Diagnostics;

template <class T> T checked(std::optional<T> value, const Diagnostics& diagnostics) {
    if (value) { return std::move(*value); }
    std::string message = "invalid planning object construction";
    for (const auto& diagnostic : diagnostics.all()) { message += ": " + diagnostic.message; }
    throw py::value_error(message);
}

inline std::vector<Expr> expressions(const std::vector<H::ExprPtr>& values) {
    std::vector<Expr> result;
    for (const auto& value : values) { result.push_back({value}); }
    return result;
}

inline std::vector<H::ExprPtr> nativeExpressions(const std::vector<Expr>& values) {
    std::vector<H::ExprPtr> result;
    for (const auto& value : values) { result.push_back(value.value); }
    return result;
}

inline H::Op logical(const std::string& name) {
    if (name == "and") { return H::Op::AND; }
    if (name == "or") { return H::Op::OR; }
    if (name == "not") { return H::Op::NOT; }
    if (name == "implies") { return H::Op::IMPLIES; }
    throw py::value_error("unknown object logical operator: " + name);
}

void bind(py::module_& module);

} // namespace SomtPythonPlanningObjects
