// Native HIR construction. Expressions remain immutable across Python calls.
#pragma once
#include <somtparser/translation/translate.h>
#include <somtparser/hir/typecheck.h>
#include <somtparser/hir/soft_objectives.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <algorithm>
#include <regex>
#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <tuple>

namespace SomtPythonHir {
namespace H = SOMTParser::Uir::Hir;
namespace py = pybind11;
struct Expr { H::ExprPtr value; };

inline std::vector<H::ExprPtr> values(const std::vector<Expr>& args) {
    std::vector<H::ExprPtr> result;
    for (const auto& arg : args) result.push_back(arg.value);
    return result;
}

void bind(py::module_& m);

} // namespace SomtPythonHir
