#include "module_bindings.h"

namespace SomtPythonModule {

void bind(py::module_& m) {
    // Return value snapshots: mutating the Python view cannot erase a call or
    // alter the immutable imported artifact held by ModuleOutcome.
    py::class_<L::ModuleOutcome>(m, "ModuleImport")
        .def_property_readonly("ok", &L::ModuleOutcome::ok)
        .def_property_readonly("diagnostics", [](const L::ModuleOutcome& out) {
            return out.diagnostics.all();
        })
        .def_property_readonly("language", [](const L::ModuleOutcome& out) {
            return out.module ? out.module->language : std::string{};
        })
        .def("to_smt2", [](const L::ModuleOutcome& out) {
            if (!out.ok()) { throw py::value_error("module import failed"); }
            const auto exported = L::exportModule(*out.module);
            if (!exported.ok()) {
                std::string message = "module export failed";
                for (const auto& d : exported.diagnostics.all()) { message += ": " + d.message; }
                throw py::value_error(message);
            }
            return exported.smt2;
        }, "Export every relation and external call, without check-sat or exit. The first comment carries the JSON interface.")
        .def_property_readonly("systems", [](const L::ModuleOutcome& out) {
            py::list result;
            if (!out.ok()) { return result; }
            for (const auto& system : out.module->systems) {
                py::dict item;
                item["name"] = system.name;
                py::list variables;
                for (const auto& variable : system.variables) {
                    py::dict row;
                    row["current"] = variable.current; row["next"] = variable.next;
                    row["sort"] = H::toString(variable.sort); row["role"] = variable.role;
                    variables.append(row);
                }
                item["variables"] = variables;
                item["output_count"] = system.outputs.size();
                item["bad_count"] = system.bad.size();
                result.append(item);
            }
            return result;
        })
        .def_property_readonly("unresolved", [](const L::ModuleOutcome& out) {
            py::list result;
            if (!out.ok()) { return result; }
            for (const auto& call : out.module->unresolved) {
                py::dict item;
                item["predicate"] = call.predicate; item["annotations"] = call.annotations;
                item["file"] = call.loc.file; item["line"] = call.loc.line;
                py::list arguments;
                for (const auto& argument : call.arguments) {
                    py::dict row;
                    row["sort"] = H::toString(argument.sort); row["array"] = argument.array;
                    row["parameter"] = argument.parameter;
                    py::list values;
                    for (const auto& value : argument.values) { values.append(expression(value)); }
                    row["values"] = values;
                    arguments.append(row);
                }
                item["arguments"] = arguments;
                result.append(item);
            }
            return result;
        })
        .def("relation_smt2", [](const L::ModuleOutcome& out, std::size_t index,
                                 const std::string& relation) {
            if (!out.ok()) { throw py::value_error("module import failed"); }
            if (index >= out.module->systems.size()) { throw py::index_error("system index out of range"); }
            {
                const auto& system = out.module->systems[index];
                H::ExprPtr term;
                if (relation == "init") { term = system.init; }
                else if (relation == "trans") { term = system.trans; }
                else if (relation == "invariant") { term = system.invariant; }
                else { throw py::value_error("relation must be init, trans, or invariant"); }
                auto context = system.context;
                H::Constraint constraint; constraint.formula = term;
                context.constraints.push_back(constraint);
                return checkedSmt(context);
            }
        }, py::arg("system_index"), py::arg("relation"),
           "Inspect one relation as SMT; this does not express a reachability query.")
        .def("known_constraints_smt2", [](const L::ModuleOutcome& out) {
            if (!out.ok()) { throw py::value_error("module import failed"); }
            std::istringstream input(checkedSmt(out.module->known));
            std::string line;
            std::string text = "; PARTIAL MODEL: external relations are unresolved; not a solution query.\n";
            while (std::getline(input, line)) {
                if (line == "(check-sat)" || line == "(exit)") { continue; }
                text += line + "\n";
            }
            return text;
        }, "Inspect known constraints only; unresolved relations are excluded.");
    m.def("import_module", [](const std::string& path, std::string source,
                               const std::string& language, const SOMTParser::Uir::ParamMap& reader_options) {
        L::SourceUnit unit; unit.main_path = path; unit.inline_source = std::move(source);
        L::ParseOptions options; options.options = reader_options;
        return L::importModule(unit, language, options);
    }, py::arg("path") = "", py::kw_only(), py::arg("source") = "", py::arg("language") = "",
       py::arg("options") = SOMTParser::Uir::ParamMap{});
}

} // namespace SomtPythonModule
