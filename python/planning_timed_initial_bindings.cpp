#include "planning_timed_initial_bindings.h"

namespace SomtPythonPlanningTimedInitial {

void bind(py::module_& module) {
    py::class_<P::TimedInitialLiteral>(module, "HirTimedInitialLiteral")
        .def(py::init([](Expr time, std::string proposition, bool value) {
            P::TimedInitialLiteral event{time.value, std::move(proposition), value};
            Diagnostics diagnostics;
            auto validation = P::encodeTimedInitialLiterals({}, {event}, "validate:", diagnostics);
            checked(std::move(validation), diagnostics);
            return event;
        }), py::arg("time"), py::arg("proposition"), py::arg("value") = true)
        .def_property_readonly("time", [](const P::TimedInitialLiteral& e) { return Expr{e.time}; })
        .def_readonly("proposition", &P::TimedInitialLiteral::proposition)
        .def_readonly("value", &P::TimedInitialLiteral::value);
    py::class_<P::TimedInitialEncoding>(module, "HirTimedInitialEncoding")
        .def_property_readonly("constraints", [](const P::TimedInitialEncoding& e) { return expressions(e.constraints); })
        .def_property_readonly("matches", [](const P::TimedInitialEncoding& e) {
            std::vector<std::vector<Expr>> rows;
            for (const auto& row : e.matches) { rows.push_back(expressions(row)); }
            return rows;
        })
        .def_readonly("accesses", &P::TimedInitialEncoding::accesses);
    py::class_<P::StableGoalMakespan>(module, "HirStableGoalMakespan")
        .def_property_readonly("constraints", [](const P::StableGoalMakespan& e) { return expressions(e.constraints); })
        .def_property_readonly("time", [](const P::StableGoalMakespan& e) { return Expr{e.time}; });
    module.def("planning_timed_initial_literals", [](const std::vector<P::TemporalHappening>& happenings,
        const std::vector<P::TimedInitialLiteral>& events, const std::string& ownerPrefix) {
        Diagnostics diagnostics;
        auto result = P::encodeTimedInitialLiterals(happenings, events, ownerPrefix, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("happenings"), py::arg("events"), py::arg("owner_prefix") = "__timed_initial_",
       "Return mandatory positive-time event constraints, match guards and endpoint accesses. Attach state transitions, occupancy and interference explicitly; no model is mutated.");
    module.def("planning_stable_goal_makespan", [](const std::vector<P::TemporalHappening>& happenings,
        const std::vector<Expr>& goals, Expr lastActionEnd) {
        Diagnostics diagnostics;
        auto result = P::encodeStableGoalMakespan(happenings, SomtPythonHir::values(goals), lastActionEnd.value, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("happenings"), py::arg("goals"), py::arg("last_action_end"),
       "Return PDDL2.2 stable-goal makespan and constraints from initial/post-state goal samples on an ordered, framed trace. Future irrelevant timed events do not inflate the metric.");
}

} // namespace SomtPythonPlanningTimedInitial
