#include "planning_temporal_bindings.h"

namespace SomtPythonPlanningTemporal {

void bind(py::module_& module) {
    py::class_<P::RationalTimeCoordinate>(module, "HirRationalTimeCoordinate")
        .def(py::init([](Expr time, Expr numerator, Expr denominator) {
            requireSort(time, H::SortKind::REAL, "rational time");
            requireSort(numerator, H::SortKind::INT, "rational time numerator");
            requireSort(denominator, H::SortKind::INT, "rational time denominator");
            return P::RationalTimeCoordinate{time.value, numerator.value, denominator.value};
        }), py::arg("time"), py::arg("numerator"), py::arg("denominator"))
        .def_property_readonly("time", [](const P::RationalTimeCoordinate& value) { return Expr{value.time}; })
        .def_property_readonly("numerator", [](const P::RationalTimeCoordinate& value) { return Expr{value.numerator}; })
        .def_property_readonly("denominator", [](const P::RationalTimeCoordinate& value) { return Expr{value.denominator}; });
    py::class_<P::TemporalHappening>(module, "HirTemporalHappening")
        .def(py::init([](Expr active, Expr time) {
            requireSort(active, H::SortKind::BOOL, "happening activation");
            requireSort(time, H::SortKind::REAL, "happening time");
            return P::TemporalHappening{active.value, time.value};
        }), py::arg("active"), py::arg("time"))
        .def_property_readonly("active", [](const P::TemporalHappening& value) { return Expr{value.active}; })
        .def_property_readonly("time", [](const P::TemporalHappening& value) { return Expr{value.time}; });
    py::class_<P::DurativeOccurrence>(module, "HirDurativeOccurrence")
        .def(py::init([](Expr active, Expr start, Expr end) {
            requireSort(active, H::SortKind::BOOL, "occurrence activation");
            requireSort(start, H::SortKind::REAL, "start time");
            requireSort(end, H::SortKind::REAL, "end time");
            return P::DurativeOccurrence{active.value, start.value, end.value};
        }), py::arg("active"), py::arg("start"), py::arg("end"))
        .def_property_readonly("active", [](const P::DurativeOccurrence& value) { return Expr{value.active}; })
        .def_property_readonly("start", [](const P::DurativeOccurrence& value) { return Expr{value.start}; })
        .def_property_readonly("end", [](const P::DurativeOccurrence& value) { return Expr{value.end}; });
    py::class_<P::TemporalConditionSamples>(module, "HirTemporalConditionSamples")
        .def(py::init([](const std::vector<Expr>& atStart, const std::vector<Expr>& atEnd,
                        const std::vector<Expr>& overAll) {
            for (const auto& group : {atStart, atEnd, overAll}) {
                for (const auto& expression : group) { requireSort(expression, H::SortKind::BOOL, "condition sample"); }
            }
            return P::TemporalConditionSamples{SomtPythonHir::values(atStart),
                SomtPythonHir::values(atEnd), SomtPythonHir::values(overAll)};
        }), py::arg("at_start") = std::vector<Expr>{}, py::arg("at_end") = std::vector<Expr>{},
            py::arg("over_all") = std::vector<Expr>{})
        .def_property_readonly("at_start", [](const P::TemporalConditionSamples& value) { return expressions(value.atStart); })
        .def_property_readonly("at_end", [](const P::TemporalConditionSamples& value) { return expressions(value.atEnd); })
        .def_property_readonly("over_all", [](const P::TemporalConditionSamples& value) { return expressions(value.overAll); });
    py::class_<P::DurativeEncoding>(module, "HirDurativeEncoding")
        .def_property_readonly("constraints", [](const P::DurativeEncoding& value) { return expressions(value.constraints); })
        .def_property_readonly("duration", [](const P::DurativeEncoding& value) { return Expr{value.duration}; });
    py::enum_<P::TemporalEffectEndpoint>(module, "TemporalEffectEndpoint")
        .value("START", P::TemporalEffectEndpoint::START)
        .value("END", P::TemporalEffectEndpoint::END);
    py::class_<P::TemporalEndpointAccess>(module, "HirTemporalEndpointAccess")
        .def(py::init([](Expr active, Expr time, std::set<std::string> propositionReads,
                        std::set<std::string> propositionAdds, std::set<std::string> propositionDeletes,
                        std::set<std::string> numericReads, std::set<std::string> numericWrites,
                        std::set<std::string> additiveWrites, std::string owner) {
            P::TemporalEndpointAccess result{active.value, time.value,
                std::move(propositionReads), std::move(propositionAdds), std::move(propositionDeletes),
                std::move(numericReads), std::move(numericWrites), std::move(additiveWrites), std::move(owner)};
            Diagnostics diagnostics;
            auto validation = P::encodeTemporalInterference({result}, diagnostics);
            checked(std::move(validation), diagnostics);
            return result;
        }), py::arg("active"), py::arg("time"), py::kw_only(),
            py::arg("proposition_reads") = std::set<std::string>{},
            py::arg("proposition_adds") = std::set<std::string>{},
            py::arg("proposition_deletes") = std::set<std::string>{},
            py::arg("numeric_reads") = std::set<std::string>{},
            py::arg("numeric_writes") = std::set<std::string>{},
            py::arg("additive_writes") = std::set<std::string>{}, py::arg("owner_id") = "")
        .def_property_readonly("active", [](const P::TemporalEndpointAccess& value) { return Expr{value.active}; })
        .def_property_readonly("time", [](const P::TemporalEndpointAccess& value) { return Expr{value.time}; })
        .def_readonly("proposition_reads", &P::TemporalEndpointAccess::propositionReads)
        .def_readonly("proposition_adds", &P::TemporalEndpointAccess::propositionAdds)
        .def_readonly("proposition_deletes", &P::TemporalEndpointAccess::propositionDeletes)
        .def_readonly("numeric_reads", &P::TemporalEndpointAccess::numericReads)
        .def_readonly("numeric_writes", &P::TemporalEndpointAccess::numericWrites)
        .def_readonly("additive_writes", &P::TemporalEndpointAccess::additiveWrites)
        .def_readonly("owner_id", &P::TemporalEndpointAccess::owner_id);
    module.def("planning_temporal_rational_time", [](const P::RationalTimeCoordinate& coordinate, Expr active) {
        Diagnostics diagnostics;
        auto result = P::encodeRationalTime(coordinate, active.value, diagnostics);
        return expressions(checked(std::move(result), diagnostics));
    }, py::arg("coordinate"), py::arg("active"),
       "Return active-guarded rational-time constraints with unbounded integer witnesses and a positive denominator. Inactive coordinates remain unrestricted; no model is mutated.");
    module.def("planning_temporal_happening_order", [](const std::vector<P::TemporalHappening>& happenings) {
        Diagnostics diagnostics;
        auto result = P::encodeHappeningOrder(happenings, diagnostics);
        return expressions(checked(std::move(result), diagnostics));
    }, py::arg("happenings"), "Return active-prefix and strictly positive, increasing-time constraints; no model is mutated.");
    module.def("planning_temporal_durative_occurrence", [](const std::vector<P::TemporalHappening>& happenings,
            const P::DurativeOccurrence& occurrence, const P::TemporalConditionSamples& conditions) {
        Diagnostics diagnostics;
        auto result = P::encodeDurativeOccurrence(happenings, occurrence, conditions, diagnostics);
        return checked(std::move(result), diagnostics);
    }, py::arg("happenings"), py::arg("occurrence"), py::arg("conditions") = P::TemporalConditionSamples{},
       "Return constraints and exact end-start duration. Endpoint samples are pre-state; interval samples are post-state on open intervals. Emit happening order separately.");
    module.def("planning_temporal_effect_guard", [](const std::vector<P::TemporalHappening>& happenings,
            const P::DurativeOccurrence& occurrence, const P::TemporalConditionSamples& conditions,
            P::TemporalEffectEndpoint endpoint) {
        Diagnostics diagnostics;
        auto result = P::temporalEffectGuard(happenings, occurrence, conditions, endpoint, diagnostics);
        if (!result) { throw py::value_error(errorMessage(diagnostics)); }
        return Expr{std::move(result)};
    }, py::arg("happenings"), py::arg("occurrence"), py::arg("conditions"), py::arg("endpoint"),
       "Return a history guard, not a plan constraint. START cannot depend on future samples. Emit occurrence validity separately; sampled states must be piecewise constant.");
    module.def("planning_temporal_interference", [](const std::vector<P::TemporalEndpointAccess>& endpoints) {
        Diagnostics diagnostics;
        auto result = P::encodeTemporalInterference(endpoints, diagnostics);
        return expressions(checked(std::move(result), diagnostics));
    }, py::arg("endpoints"),
       "Return no-moving-target constraints between endpoint owners. Equal nonempty owner_id groups branches of one endpoint; empty owners remain independent. Emit state transitions separately.");
}

} // namespace SomtPythonPlanningTemporal
