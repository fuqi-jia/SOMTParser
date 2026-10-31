#include "planning_continuous_bindings.h"

namespace SomtPythonPlanningContinuous {

void bind(py::module_& module) {
    py::enum_<P::FlowDerivativeDomain>(module,"FlowDerivativeDomain")
        .value("INTERIOR",P::FlowDerivativeDomain::INTERIOR)
        .value("CLOSED_ONE_SIDED",P::FlowDerivativeDomain::CLOSED_ONE_SIDED);
    py::class_<P::ContinuousCoordinate>(module,"HirContinuousCoordinate")
        .def(py::init([](std::string trajectory,std::string variable,P::NumericStateCell initial,
                        P::NumericStateCell terminal,Expr active,P::NumericValue rate) {
            return P::ContinuousCoordinate{std::move(trajectory),std::move(variable),
                std::move(initial),std::move(terminal),active.value,std::move(rate)};
        }),py::arg("trajectory_name"),py::arg("variable"),py::arg("initial"),py::arg("terminal"),
           py::arg("active"),py::arg("rate"));
    py::class_<P::ContinuousInvariant>(module,"HirContinuousInvariant")
        .def(py::init([](Expr guard,P::NumericCondition condition,bool include_start,bool include_end) {
            return P::ContinuousInvariant{guard.value,std::move(condition),include_start,include_end};
        }),py::arg("guard"),py::arg("condition"),py::arg("include_start")=false,py::arg("include_end")=false);
    py::class_<P::ContinuousSegment>(module,"HirContinuousSegment")
        .def(py::init([](Expr enabled,Expr start,Expr end,std::string time_variable,
                        P::FlowDerivativeDomain derivative_domain,
                        std::vector<P::ContinuousCoordinate> coordinates,
                        std::vector<P::ContinuousInvariant> invariants) {
            P::ContinuousSegment result;
            result.enabled=enabled.value;result.start=start.value;result.end=end.value;
            result.time_variable=std::move(time_variable);result.derivative_domain=derivative_domain;
            result.coordinates=std::move(coordinates);result.invariants=std::move(invariants);
            return result;
        }),py::arg("enabled"),py::arg("start"),py::arg("end"),py::arg("time_variable"),
           py::arg("derivative_domain"),py::arg("coordinates"),
           py::arg("invariants")=std::vector<P::ContinuousInvariant>{});
    py::class_<P::ContinuousEncoding>(module,"HirContinuousEncoding")
        .def_readonly("derivative_domain",&P::ContinuousEncoding::derivative_domain)
        .def_readonly("polynomial_witness",&P::ContinuousEncoding::polynomial_witness)
        .def_readonly("requires_trajectory_source_observations",&P::ContinuousEncoding::requires_trajectory_source_observations)
        .def_property_readonly("trajectory_names",[](const P::ContinuousEncoding& encoding) {
            std::vector<std::string> names;
            for (const auto& trajectory:encoding.trajectories) {names.push_back(trajectory.name);}
            return names;
        })
        .def_property_readonly("constraints",[](const P::ContinuousEncoding& encoding) {
            std::vector<Expr> result;
            for (const auto& expression:encoding.constraints) {result.push_back({expression});}
            return result;
        })
        .def("to_model",[](const P::ContinuousEncoding& encoding,const H::ConstraintModel& context) {
            H::ConstraintModel result=context;
            result.funs.insert(result.funs.end(),encoding.trajectories.begin(),encoding.trajectories.end());
            for (const auto& expression:encoding.constraints) {H::Constraint row;row.formula=expression;result.constraints.push_back(row);}
            Diagnostics diagnostics;
            if (!H::typeCheck(result,diagnostics)) {throw py::value_error(message(diagnostics));}
            return result;
        },py::arg("context"),"Return a validated model copy with trajectories and all constraints; leave context unchanged.");
    module.def("planning_continuous_segment",[](const H::ConstraintModel& context,const P::ContinuousSegment& segment) {
        Diagnostics diagnostics;
        auto result=P::encodeContinuousSegment(context,segment,diagnostics);
        if (!result) {throw py::value_error(message(diagnostics));}
        return *result;
    },py::arg("context"),py::arg("segment"),
       "Encode a complete real trajectory relation; does not claim arbitrary ODE decidability or parse PDDL source.");
    module.def("planning_polynomial_flow_witness",[](const H::ConstraintModel& context,
        const P::ContinuousSegment& segment,const std::vector<std::vector<Expr>>& coefficients) {
        std::vector<std::vector<H::ExprPtr>> values;
        for (const auto& coordinate:coefficients) {values.push_back(SomtPythonHir::values(coordinate));}
        Diagnostics diagnostics;
        auto result=P::encodePolynomialFlowWitness(context,segment,values,diagnostics);
        if (!result) {throw py::value_error(message(diagnostics));}
        return *result;
    },py::arg("context"),py::arg("segment"),py::arg("coefficients"),
       "Check a supplied polynomial trajectory witness, with coefficients in elapsed time; no finite-degree completeness claim.");
}

} // namespace SomtPythonPlanningContinuous
