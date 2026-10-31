#include "planning_numeric_bindings.h"

namespace SomtPythonPlanningNumeric {

void bind(py::module_& module) {
    py::class_<P::NumericStateCell>(module,"HirNumericStateCell")
        .def(py::init([](Expr value, Expr defined) {
            P::NumericStateCell cell{value.value,defined.value};
            Diagnostics diagnostics;
            checked(P::numericRead(cell,0,diagnostics),diagnostics);
            return cell;
        }),py::arg("value"),py::arg("defined"))
        .def_property_readonly("value",[](const P::NumericStateCell& cell){return Expr{cell.value};})
        .def_property_readonly("defined",[](const P::NumericStateCell& cell){return Expr{cell.defined};});
    py::class_<P::NumericValue>(module,"HirNumericValue")
        .def(py::init([](Expr value,Expr defined,const std::vector<std::size_t>& reads){
            if (!value.value || value.value->sort.kind!=H::SortKind::REAL
                || !defined.value || defined.value->sort.kind!=H::SortKind::BOOL) {
                throw py::value_error("numeric value needs a Real expression and Bool definedness");
            }
            return P::NumericValue{value.value,defined.value,reads};
        }),py::arg("value"),py::arg("defined"),py::arg("reads")=std::vector<std::size_t>{})
        .def_property_readonly("value",[](const P::NumericValue& value){return Expr{value.value};})
        .def_property_readonly("defined",[](const P::NumericValue& value){return Expr{value.defined};})
        .def_readonly("reads",&P::NumericValue::reads);
    py::class_<P::NumericCondition>(module,"HirNumericCondition")
        .def_property_readonly("value",[](const P::NumericCondition& condition){return Expr{condition.value};})
        .def_property_readonly("defined",[](const P::NumericCondition& condition){return Expr{condition.defined};})
        .def_readonly("reads",&P::NumericCondition::reads);
    py::enum_<P::NumericUpdateKind>(module,"NumericUpdateKind")
        .value("ASSIGN",P::NumericUpdateKind::ASSIGN).value("INCREASE",P::NumericUpdateKind::INCREASE)
        .value("DECREASE",P::NumericUpdateKind::DECREASE).value("SCALE_UP",P::NumericUpdateKind::SCALE_UP)
        .value("SCALE_DOWN",P::NumericUpdateKind::SCALE_DOWN);
    py::class_<P::NumericUpdate>(module,"HirNumericUpdate")
        .def(py::init([](std::size_t target,P::NumericUpdateKind kind,P::NumericValue rhs,Expr guard,std::string owner){
            return P::NumericUpdate{target,kind,std::move(rhs),guard.value,std::move(owner)};
        }),py::arg("target_index"),py::arg("kind"),py::arg("rhs"),py::arg("guard"),py::arg("owner_id"));
    module.def("planning_numeric_constant",[](const std::string& exact){
        Diagnostics diagnostics;auto value=P::numericConstant(exact,diagnostics);return checked(value,diagnostics);
    });
    module.def("planning_numeric_read",[](const P::NumericStateCell& cell,std::size_t index){
        Diagnostics diagnostics;auto value=P::numericRead(cell,index,diagnostics);return checked(value,diagnostics);
    });
    module.def("planning_numeric_arithmetic",[](const std::string& op,const std::vector<P::NumericValue>& args){
        Diagnostics diagnostics;auto value=P::numericArithmetic(operation(op),args,diagnostics);return checked(value,diagnostics);
    });
    module.def("planning_numeric_compare",[](const std::string& op,const P::NumericValue& lhs,const P::NumericValue& rhs){
        Diagnostics diagnostics;auto value=P::numericCompare(operation(op),lhs,rhs,diagnostics);return checked(value,diagnostics);
    });
    module.def("planning_numeric_predicate",[](Expr predicate){
        Diagnostics diagnostics;auto value=P::numericPredicate(predicate.value,diagnostics);return checked(value,diagnostics);
    });
    module.def("planning_numeric_logical",[](const std::string& op,const std::vector<P::NumericCondition>& args){
        Diagnostics diagnostics;auto value=P::numericLogical(operation(op),args,diagnostics);return checked(value,diagnostics);
    });
    module.def("planning_numeric_satisfied",[](const P::NumericCondition& condition){return Expr{P::numericSatisfied(condition)};});
    module.def("planning_numeric_transition",[](const H::ConstraintModel& context,
        const std::vector<P::NumericStateCell>& before,const std::vector<P::NumericStateCell>& after,
        const std::vector<P::NumericUpdate>& updates){
        Diagnostics diagnostics;auto result=P::buildNumericTransition(context,before,after,updates,diagnostics);
        auto transition=checked(result,diagnostics);std::vector<Expr> constraints;
        for (const auto& expression:transition.constraints) {constraints.push_back({expression});}
        return constraints;
    },py::arg("context"),py::arg("before"),py::arg("after"),py::arg("updates"),
       "Return exact simultaneous numeric update/frame constraints without mutating the HIR model.");
}

} // namespace SomtPythonPlanningNumeric
