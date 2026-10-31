#include "planning_objects_bindings.h"

namespace SomtPythonPlanningObjects {

void bind(py::module_& module) {
    py::class_<P::ObjectTypeDeclaration>(module, "HirObjectTypeDeclaration")
        .def(py::init([](std::string name, std::vector<std::string> parents) {
            return P::ObjectTypeDeclaration{std::move(name), std::move(parents)};
        }), py::arg("name"), py::arg("parents") = std::vector<std::string>{})
        .def_readonly("name", &P::ObjectTypeDeclaration::name)
        .def_readonly("parents", &P::ObjectTypeDeclaration::parents);
    py::class_<P::PlanningObject>(module, "HirPlanningObject")
        .def(py::init([](std::string name, std::string type) {
            return P::PlanningObject{std::move(name), std::move(type)};
        }), py::arg("name"), py::arg("type"))
        .def_readonly("name", &P::PlanningObject::name)
        .def_readonly("type", &P::PlanningObject::type);
    py::class_<P::ObjectType>(module, "HirObjectType")
        .def(py::init([](std::vector<std::string> alternatives) {
            return P::ObjectType{std::move(alternatives)};
        }), py::arg("alternatives"))
        .def_readonly("alternatives", &P::ObjectType::alternatives);
    py::class_<P::ObjectUniverse>(module, "HirObjectUniverse")
        .def(py::init([](std::vector<P::ObjectTypeDeclaration> types, std::vector<P::PlanningObject> objects) {
            P::ObjectUniverse result{std::move(types), std::move(objects)};
            Diagnostics diagnostics;
            checked(P::validateObjectUniverse(result, diagnostics)
                ? std::optional<bool>(true) : std::nullopt, diagnostics);
            return result;
        }), py::arg("types"), py::arg("objects"))
        .def_readonly("types", &P::ObjectUniverse::types)
        .def_readonly("objects", &P::ObjectUniverse::objects);
    py::class_<P::ObjectStateCell>(module, "HirObjectStateCell")
        .def(py::init([](Expr value, Expr defined, P::ObjectType type) {
            if (!value.value || value.value->sort.kind != H::SortKind::INT
                || !defined.value || defined.value->sort.kind != H::SortKind::BOOL) {
                throw py::value_error("object state needs an Int code and Bool definedness");
            }
            return P::ObjectStateCell{value.value, defined.value, std::move(type)};
        }), py::arg("value"), py::arg("defined"), py::arg("type"))
        .def_property_readonly("value", [](const P::ObjectStateCell& cell) { return Expr{cell.value}; })
        .def_property_readonly("defined", [](const P::ObjectStateCell& cell) { return Expr{cell.defined}; })
        .def_readonly("type", &P::ObjectStateCell::type);
    py::class_<P::ObjectReadAccess>(module, "HirObjectReadAccess")
        .def_readonly("cell", &P::ObjectReadAccess::cell)
        .def_property_readonly("when", [](const P::ObjectReadAccess& read) { return Expr{read.when}; });
    py::class_<P::ObjectValue>(module, "HirObjectValue")
        .def_property_readonly("value", [](const P::ObjectValue& value) { return Expr{value.value}; })
        .def_property_readonly("defined", [](const P::ObjectValue& value) { return Expr{value.defined}; })
        .def_readonly("type", &P::ObjectValue::type)
        .def_readonly("reads", &P::ObjectValue::reads)
        .def_property_readonly("constraints", [](const P::ObjectValue& value) { return expressions(value.constraints); });
    py::class_<P::ObjectCondition>(module, "HirObjectCondition")
        .def_property_readonly("value", [](const P::ObjectCondition& value) { return Expr{value.value}; })
        .def_property_readonly("defined", [](const P::ObjectCondition& value) { return Expr{value.defined}; })
        .def_readonly("reads", &P::ObjectCondition::reads)
        .def_property_readonly("constraints", [](const P::ObjectCondition& value) { return expressions(value.constraints); });
    py::enum_<P::ObjectUndefinedPolicy>(module, "ObjectUndefinedPolicy")
        .value("STRICT", P::ObjectUndefinedPolicy::STRICT)
        .value("ATOMIC_FALSE", P::ObjectUndefinedPolicy::ATOMIC_FALSE);
    py::enum_<P::ObjectAssignmentPolicy>(module, "ObjectAssignmentPolicy")
        .value("SINGLE_WRITER", P::ObjectAssignmentPolicy::SINGLE_WRITER)
        .value("AGREEING_WRITERS", P::ObjectAssignmentPolicy::AGREEING_WRITERS);
    py::class_<P::ObjectTable>(module, "HirObjectTable")
        .def(py::init([](std::vector<P::ObjectType> parameters, std::vector<std::vector<std::size_t>> rows) {
            return P::ObjectTable{std::move(parameters), std::move(rows)};
        }), py::arg("parameters"), py::arg("rows"))
        .def_readonly("parameters", &P::ObjectTable::parameters)
        .def_readonly("rows", &P::ObjectTable::rows);
    py::class_<P::ObjectDispatch>(module, "HirObjectDispatch")
        .def_property_readonly("defined", [](const P::ObjectDispatch& value) { return Expr{value.defined}; })
        .def_property_readonly("matches", [](const P::ObjectDispatch& value) { return expressions(value.matches); })
        .def_readonly("reads", &P::ObjectDispatch::reads)
        .def_property_readonly("constraints", [](const P::ObjectDispatch& value) { return expressions(value.constraints); });
    py::class_<P::ObjectNumericValue>(module, "HirObjectNumericValue")
        .def_readonly("numeric", &P::ObjectNumericValue::numeric)
        .def_readonly("object_reads", &P::ObjectNumericValue::object_reads)
        .def_readonly("numeric_reads", &P::ObjectNumericValue::numeric_reads)
        .def_property_readonly("constraints", [](const P::ObjectNumericValue& value) { return expressions(value.constraints); });
    py::class_<P::ObjectAddress>(module, "HirObjectAddress")
        .def_property_readonly("defined", [](const P::ObjectAddress& value) { return Expr{value.defined}; })
        .def_readonly("cells", &P::ObjectAddress::cells)
        .def_property_readonly("matches", [](const P::ObjectAddress& value) { return expressions(value.matches); })
        .def_readonly("reads", &P::ObjectAddress::reads)
        .def_property_readonly("constraints", [](const P::ObjectAddress& value) { return expressions(value.constraints); });
    py::class_<P::ObjectUpdate>(module, "HirObjectUpdate")
        .def(py::init([](P::ObjectAddress target, std::optional<P::ObjectValue> rhs, Expr guard) {
            return P::ObjectUpdate{std::move(target), std::move(rhs), guard.value};
        }), py::arg("target"), py::arg("rhs"), py::arg("guard"),
           "rhs=None explicitly assigns undefined; the Bool guard controls execution.");

    module.def("planning_object_carrier", [](const P::ObjectUniverse& universe, const P::ObjectType& type) {
        Diagnostics diagnostics; auto result = P::objectCarrier(universe, type, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("universe"), py::arg("type"), "Return zero-based object indices, not the one-based Int codes.");
    module.def("planning_object_subtype", [](const P::ObjectUniverse& universe, const P::ObjectType& actual,
                                             const P::ObjectType& expected) {
        Diagnostics diagnostics; auto result = P::objectSubtype(universe, actual, expected, diagnostics);
        return checked(result, diagnostics);
    }, py::arg("universe"), py::arg("actual"), py::arg("expected"));
    module.def("planning_object_constant", [](const P::ObjectUniverse& universe, const std::string& name) {
        Diagnostics diagnostics; auto result = P::objectConstant(universe, name, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("universe"), py::arg("name"));
    module.def("planning_object_read", [](const P::ObjectUniverse& universe, const P::ObjectStateCell& cell,
                                          std::size_t index) {
        Diagnostics diagnostics; auto result = P::objectRead(universe, cell, index, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("universe"), py::arg("cell"), py::arg("index"));
    module.def("planning_object_equal", [](const P::ObjectUniverse& universe, const P::ObjectValue& lhs,
                                           const P::ObjectValue& rhs, P::ObjectUndefinedPolicy policy) {
        Diagnostics diagnostics; auto result = P::objectEqual(universe, lhs, rhs, policy, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("universe"), py::arg("lhs"), py::arg("rhs"), py::arg("policy"));
    module.def("planning_object_logical", [](const std::string& op, const std::vector<P::ObjectCondition>& args) {
        Diagnostics diagnostics; auto result = P::objectLogical(logical(op), args, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("op"), py::arg("args"));
    module.def("planning_object_satisfied", [](const P::ObjectCondition& condition) {
        return Expr{P::objectSatisfied(condition)};
    }, py::arg("condition"));
    module.def("planning_object_dispatch", [](const H::ConstraintModel& context, const P::ObjectUniverse& universe,
        const P::ObjectTable& table, const std::vector<P::ObjectValue>& arguments) {
        Diagnostics diagnostics; auto result = P::objectDispatch(context, universe, table, arguments, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("context"), py::arg("universe"), py::arg("table"), py::arg("arguments"));
    module.def("planning_object_lookup", [](const H::ConstraintModel& context, const P::ObjectUniverse& universe,
        const P::ObjectTable& table, const std::vector<P::ObjectValue>& arguments,
        const std::vector<P::ObjectValue>& rowValues, const P::ObjectType& resultType) {
        Diagnostics diagnostics; auto result = P::objectLookup(context, universe, table, arguments, rowValues, resultType, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("context"), py::arg("universe"), py::arg("table"), py::arg("arguments"), py::arg("row_values"), py::arg("result_type"));
    module.def("planning_object_predicate", [](const H::ConstraintModel& context, const P::ObjectUniverse& universe,
        const P::ObjectTable& table, const std::vector<P::ObjectValue>& arguments,
        const std::vector<Expr>& rowValues, P::ObjectUndefinedPolicy policy) {
        Diagnostics diagnostics; auto result = P::objectPredicate(context, universe, table, arguments, nativeExpressions(rowValues), policy, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("context"), py::arg("universe"), py::arg("table"), py::arg("arguments"), py::arg("row_values"), py::arg("policy"));
    module.def("planning_object_numeric_lookup", [](const H::ConstraintModel& context, const P::ObjectUniverse& universe,
        const P::ObjectTable& table, const std::vector<P::ObjectValue>& arguments,
        const std::vector<P::NumericValue>& rowValues) {
        Diagnostics diagnostics; auto result = P::objectNumericLookup(context, universe, table, arguments, rowValues, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("context"), py::arg("universe"), py::arg("table"), py::arg("arguments"), py::arg("row_values"));
    module.def("planning_object_address", [](const H::ConstraintModel& context, const P::ObjectUniverse& universe,
        const P::ObjectTable& table, const std::vector<P::ObjectValue>& arguments, const std::vector<std::size_t>& rowCells) {
        Diagnostics diagnostics; auto result = P::objectAddress(context, universe, table, arguments, rowCells, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("context"), py::arg("universe"), py::arg("table"), py::arg("arguments"), py::arg("row_cells"));
    module.def("planning_object_transition", [](const H::ConstraintModel& context, const P::ObjectUniverse& universe,
        const std::vector<P::ObjectStateCell>& before, const std::vector<P::ObjectStateCell>& after,
        const std::vector<P::ObjectUpdate>& updates, P::ObjectAssignmentPolicy policy) {
        Diagnostics diagnostics; auto result = P::buildObjectTransition(context, universe, before, after, updates, policy, diagnostics);
        return expressions(checked(std::move(result), diagnostics).constraints);
    }, py::arg("context"), py::arg("universe"), py::arg("before"), py::arg("after"), py::arg("updates"), py::arg("policy"),
       "Return every update, finite-domain and frame constraint without mutating context.");
    module.def("planning_object_initial_state", [](const H::ConstraintModel& context, const P::ObjectUniverse& universe,
        const std::vector<P::ObjectStateCell>& cells, const std::vector<std::pair<std::size_t, std::size_t>>& values) {
        Diagnostics diagnostics; auto result = P::initialObjectState(context, universe, cells, values, diagnostics);
        return expressions(checked(std::move(result), diagnostics).constraints);
    }, py::arg("context"), py::arg("universe"), py::arg("cells"), py::arg("values"),
       "values contains (cell index, object index); omitted cells start undefined.");
}

} // namespace SomtPythonPlanningObjects
