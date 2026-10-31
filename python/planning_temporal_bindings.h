// Pure temporal HIR construction; callers explicitly attach returned constraints.
#pragma once
#include "hir_bindings.h"
#include "somtparser/hir/planning_temporal.h"

namespace SomtPythonPlanningTemporal {
namespace py = pybind11;
namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
using SomtPythonHir::Expr;
using SOMTParser::Uir::Diagnostics;

inline void requireSort(const Expr& expression, H::SortKind sort, const char* role) {
    if (!expression.value || expression.value->sort.kind != sort) {
        throw py::value_error(std::string("temporal planning: ") + role
            + (sort == H::SortKind::REAL ? " must have Real sort"
                : sort == H::SortKind::INT ? " must have Int sort" : " must have Bool sort"));
    }
}

inline std::string errorMessage(const Diagnostics& diagnostics) {
    std::string message = "invalid temporal planning construction";
    for (const auto& diagnostic : diagnostics.all()) { message += ": " + diagnostic.message; }
    return message;
}

template <class T> T checked(std::optional<T> value, const Diagnostics& diagnostics) {
    if (!value) { throw py::value_error(errorMessage(diagnostics)); }
    return std::move(*value);
}

inline std::vector<Expr> expressions(const std::vector<H::ExprPtr>& values) {
    std::vector<Expr> result;
    result.reserve(values.size());
    for (const auto& value : values) { result.push_back({value}); }
    return result;
}

void bind(py::module_& module);

} // namespace SomtPythonPlanningTemporal
