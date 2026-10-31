// Register after the shared HIR and planning_temporal bindings.
#pragma once
#include "planning_temporal_bindings.h"
#include "somtparser/hir/planning_timed_initial.h"

namespace SomtPythonPlanningTimedInitial {
namespace py = pybind11;
namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
using SomtPythonHir::Expr;
using SOMTParser::Uir::Diagnostics;
using SomtPythonPlanningTemporal::checked;
using SomtPythonPlanningTemporal::expressions;

void bind(py::module_& module);

} // namespace SomtPythonPlanningTimedInitial
