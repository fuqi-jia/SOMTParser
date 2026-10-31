#include "planning_derived_bindings.h"

namespace SomtPythonPlanningDerived {

void bind(pybind11::module_& module) {
    namespace H = SOMTParser::Uir::Hir;
    namespace P = H::Planning;
    namespace py = pybind11;
    using SomtPythonHir::Expr;
    module.def("planning_derived_closure", [](H::ConstraintModel& model,
        const std::vector<Expr>& atoms,
        const std::vector<std::pair<std::size_t, Expr>>& source_rules,
        const std::string& prefix) {
        std::vector<P::DerivedRule> rules;
        for (const auto& rule : source_rules) { rules.push_back({rule.first, rule.second.value, {}}); }
        SOMTParser::Uir::Diagnostics diagnostics;
        auto result = P::buildDerivedClosure(model, SomtPythonHir::values(atoms), rules, prefix, diagnostics);
        if (!result) {
            std::string message = "invalid finite derived closure";
            for (const auto& diagnostic : diagnostics.all()) { message += "; " + diagnostic.message; }
            throw py::value_error(message);
        }
        // Validate fully before committing the delta. The rule placeholders
        // remain unconstrained until the caller binds its observation values.
        model.decls.insert(model.decls.end(), result->declarations.begin(), result->declarations.end());
        model.constraints.insert(model.constraints.end(), result->constraints.begin(), result->constraints.end());
        std::vector<Expr> values;
        for (const auto& value : result->values) { values.push_back({value}); }
        py::dict answer;
        answer["values"] = py::cast(values);
        answer["base_dependencies"] = py::cast(result->base_dependencies);
        answer["base_function_dependencies"] = py::cast(result->base_function_dependencies);
        answer["rounds"] = result->rounds;
        return answer;
    }, py::arg("model"), py::arg("atoms"), py::arg("rules"),
       py::arg("prefix") = "__derived_lfp");
}

} // namespace SomtPythonPlanningDerived
