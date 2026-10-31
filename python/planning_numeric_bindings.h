#pragma once
#include "hir_bindings.h"
#include "somtparser/hir/planning_numeric.h"

namespace SomtPythonPlanningNumeric {
namespace py = pybind11;
namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
using SomtPythonHir::Expr;
using SOMTParser::Uir::Diagnostics;

template <class T> T checked(std::optional<T> value, const Diagnostics& diagnostics) {
    if (value) { return *value; }
    std::string message = "invalid planning numeric construction";
    for (const auto& diagnostic : diagnostics.all()) { message += ": " + diagnostic.message; }
    throw py::value_error(message);
}

inline H::Op operation(const std::string& name) {
    static const std::unordered_map<std::string,H::Op> operators = {
        {"+",H::Op::ADD},{"-",H::Op::SUB},{"neg",H::Op::NEG},{"*",H::Op::MUL},{"/",H::Op::DIV_REAL},
        {"=",H::Op::EQ},{"<",H::Op::LT},{"<=",H::Op::LE},{">",H::Op::GT},{">=",H::Op::GE},
        {"and",H::Op::AND},{"or",H::Op::OR},{"not",H::Op::NOT},{"implies",H::Op::IMPLIES}};
    const auto found = operators.find(name);
    if (found == operators.end()) { throw py::value_error("unknown planning numeric operator: " + name); }
    return found->second;
}

void bind(py::module_& module);

} // namespace SomtPythonPlanningNumeric
