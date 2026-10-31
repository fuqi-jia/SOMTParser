#pragma once
#include "hir_bindings.h"
#include "somtparser/hir/planning_continuous.h"

namespace SomtPythonPlanningContinuous {
namespace py = pybind11;
namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
using SomtPythonHir::Expr;
using SOMTParser::Uir::Diagnostics;

inline std::string message(const Diagnostics& diagnostics) {
    std::string text="invalid continuous HIR construction";
    for (const auto& diagnostic:diagnostics.all()) {text+=": "+diagnostic.message;}
    return text;
}

void bind(py::module_& module);

} // namespace SomtPythonPlanningContinuous
