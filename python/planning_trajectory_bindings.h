#pragma once
#include "hir_bindings.h"
#include "somtparser/hir/planning_trajectory.h"

namespace SomtPythonPlanningTrajectory {
namespace py = pybind11;
namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
using SomtPythonHir::Expr;
using SOMTParser::Uir::Diagnostics;

inline std::string message(const Diagnostics& diagnostics) {
    std::string text="invalid planning trajectory construction";
    for (const auto& row:diagnostics.all()) {text+=": "+row.message;}
    return text;
}
template<class T> T checked(const std::optional<T>& result,const Diagnostics& diagnostics) {
    if (!result) {throw py::value_error(message(diagnostics));}
    return *result;
}
inline H::ExprPtr optionalExpr(const std::optional<Expr>& expression) {
    return expression?expression->value:nullptr;
}

void bind(py::module_& module);

} // namespace SomtPythonPlanningTrajectory
