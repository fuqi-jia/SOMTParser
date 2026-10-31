#include "planning_trajectory_bindings.h"

namespace SomtPythonPlanningTrajectory {

void bind(py::module_& module) {
    py::enum_<P::TrajectoryOperator>(module,"TrajectoryOperator")
        .value("AT_END",P::TrajectoryOperator::AT_END).value("ALWAYS",P::TrajectoryOperator::ALWAYS)
        .value("SOMETIME",P::TrajectoryOperator::SOMETIME).value("WITHIN",P::TrajectoryOperator::WITHIN)
        .value("AT_MOST_ONCE",P::TrajectoryOperator::AT_MOST_ONCE)
        .value("SOMETIME_BEFORE",P::TrajectoryOperator::SOMETIME_BEFORE)
        .value("SOMETIME_AFTER",P::TrajectoryOperator::SOMETIME_AFTER)
        .value("ALWAYS_WITHIN",P::TrajectoryOperator::ALWAYS_WITHIN)
        .value("HOLD_DURING",P::TrajectoryOperator::HOLD_DURING)
        .value("HOLD_AFTER",P::TrajectoryOperator::HOLD_AFTER);
    py::class_<P::TrajectorySample>(module,"HirTrajectorySample")
        .def(py::init([](Expr active,Expr time,P::NumericCondition first,std::optional<P::NumericCondition> second) {
            return P::TrajectorySample{active.value,time.value,std::move(first),std::move(second)};
        }),py::arg("active"),py::arg("time"),py::arg("first"),py::arg("second")=std::nullopt);
    py::class_<P::TrajectoryPoint>(module,"HirTrajectoryPoint")
        .def(py::init([](Expr time,Expr phase){return P::TrajectoryPoint{time.value,phase.value};}),py::arg("time"),py::arg("phase"));
    py::class_<P::TrajectoryObservationDomain>(module,"HirTrajectoryObservationDomain")
        .def(py::init([](std::string time,std::string phase,Expr contains,P::TrajectoryPoint first,P::TrajectoryPoint last) {
            return P::TrajectoryObservationDomain{std::move(time),std::move(phase),contains.value,std::move(first),std::move(last)};
        }),py::arg("time_variable"),py::arg("phase_variable"),py::arg("contains"),py::arg("first"),py::arg("last"));
    py::class_<P::TrajectoryEncoding>(module,"HirTrajectoryEncoding")
        .def_property_readonly("satisfied",[](const P::TrajectoryEncoding& value){return Expr{value.satisfied};})
        .def_property_readonly("domain_constraints",[](const P::TrajectoryEncoding& value){
            std::vector<Expr> result;for (const auto& term:value.domain_constraints){result.push_back({term});}return result;
        })
        .def("to_model",[](const P::TrajectoryEncoding& encoding,const H::ConstraintModel& context,bool hard) {
            H::ConstraintModel result=context;
            for (const auto& term:encoding.domain_constraints) {H::Constraint row;row.formula=term;result.constraints.push_back(row);}
            if (hard) {H::Constraint row;row.formula=encoding.satisfied;result.constraints.push_back(row);}
            Diagnostics diagnostics;
            if (!H::typeCheck(result,diagnostics)) {throw py::value_error(message(diagnostics));}
            return result;
        },py::arg("context"),py::arg("hard"),"Return a validated model copy; explicitly select hard assertion or domain-only soft use.");
    module.def("planning_finite_trajectory",[](const H::ConstraintModel& context,P::TrajectoryOperator operation,
        const std::vector<P::TrajectorySample>& samples,const std::optional<Expr>& lower,const std::optional<Expr>& upper) {
        Diagnostics diagnostics;auto result=P::encodeFiniteTrajectory(context,operation,samples,optionalExpr(lower),optionalExpr(upper),diagnostics);
        return checked(result,diagnostics);
    },py::arg("context"),py::arg("operation"),py::arg("samples"),py::arg("lower")=std::nullopt,py::arg("upper")=std::nullopt);
    module.def("planning_observed_trajectory",[](const H::ConstraintModel& context,const P::TrajectoryObservationDomain& domain,
        P::TrajectoryOperator operation,const P::NumericCondition& first,const std::optional<P::NumericCondition>& second,
        const std::optional<Expr>& lower,const std::optional<Expr>& upper) {
        Diagnostics diagnostics;auto result=P::encodeObservedTrajectory(context,domain,operation,first,second,
            optionalExpr(lower),optionalExpr(upper),diagnostics);return checked(result,diagnostics);
    },py::arg("context"),py::arg("domain"),py::arg("operation"),py::arg("first"),py::arg("second")=std::nullopt,
       py::arg("lower")=std::nullopt,py::arg("upper")=std::nullopt);
    py::class_<P::PreferenceInstance>(module,"HirPreferenceInstance")
        .def(py::init([](std::string identity,std::string name,Expr active,Expr satisfied) {
            return P::PreferenceInstance{std::move(identity),std::move(name),active.value,satisfied.value};
        }),py::arg("instance_id"),py::arg("name"),py::arg("active"),py::arg("satisfied"));
    py::class_<P::PreferenceEncoding>(module,"HirPreferenceEncoding")
        .def_property_readonly("named_violations",[](const P::PreferenceEncoding& value) {
            std::map<std::string,Expr> result;for(const auto& row:value.named_violations){result.emplace(row.first,Expr{row.second});}return result;
        })
        .def_property_readonly("anonymous_violations",[](const P::PreferenceEncoding& value){return Expr{value.anonymous_violations};})
        .def("violation_count",[](const P::PreferenceEncoding& value,const std::string& name) {
            const auto found=value.named_violations.find(name);
            if(found==value.named_violations.end()){throw py::value_error("unknown named preference: "+name);}
            return Expr{found->second};
        },py::arg("name"));
    module.def("planning_preferences",[](const H::ConstraintModel& context,const std::vector<P::PreferenceInstance>& instances,
        const std::vector<std::string>& declared_names) {
        Diagnostics diagnostics;auto result=P::encodePreferences(context,instances,diagnostics,declared_names);return checked(result,diagnostics);
    },py::arg("context"),py::arg("instances"),py::arg("declared_names")=std::vector<std::string>{});
    module.def("planning_preference_metric",[](const H::ConstraintModel& context,Expr base,const P::PreferenceEncoding& preferences,bool minimize) {
        Diagnostics diagnostics;auto result=P::preferenceMetric(context,base.value,preferences,minimize,diagnostics);
        return Expr{checked(result,diagnostics)};
    },py::arg("context"),py::arg("base"),py::arg("preferences"),py::arg("minimize"));
}

} // namespace SomtPythonPlanningTrajectory
