#include "somtparser/translation/module.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/lowering/omt_emitter.h"
#include <iomanip>
#include <map>
#include <sstream>
#include <unordered_set>

namespace SOMTParser::Lang {
namespace H = Uir::Hir;
namespace {

std::string json(const std::string& value) {
    std::ostringstream out;
    out << '"';
    for (unsigned char c : value) {
        if (c == '"' || c == '\\') { out << '\\' << c; }
        else if (c < 32) {
            out << "\\u" << std::hex << std::setw(4) << std::setfill('0') << unsigned(c);
        } else { out << c; }
    }
    return out.str() + '"';
}

struct Names {
    std::unordered_set<std::string> used;
    void reserve(const std::string& name) {
        used.insert(name);
        if (name.size() >= 2 && name.front() == '|' && name.back() == '|') {
            used.insert(name.substr(1, name.size() - 2));
        }
    }
    void model(const H::ConstraintModel& model) {
        for (const auto& v : model.decls) { reserve(v.name); }
        for (const auto& f : model.funs) { reserve(f.name); }
        for (const auto& d : model.datatypes) {
            reserve(d.name);
            for (const auto& c : d.constructors) {
                reserve(c.name);
                for (const auto& s : c.selectors) { reserve(s.name); }
            }
        }
    }
    std::string fresh(const std::string& stem) {
        std::string name = "somt.module." + stem;
        while (!used.insert(name).second) { name += "_"; }
        return name;
    }
};

struct ListEncoding { H::Sort sort; std::string nil, cons; };

ModuleExport emit(const SourceModule& source) {
    ModuleExport out;
    if (!validateModule(source, out.diagnostics)) { return out; }
    Names names;
    names.model(source.known);
    for (const auto& system : source.systems) { names.model(system.context); }
    std::ostringstream metadata, definitions;
    metadata << "{\"schema\":\"somt-module-v1\",\"language\":" << json(source.language)
             << ",\"query\":false,\"systems\":[";
    std::string environment;
    for (std::size_t index = 0; index < source.systems.size(); ++index) {
        const auto& system = source.systems[index];
        std::unordered_set<std::string> state_names;
        for (const auto& variable : system.variables) {
            state_names.insert(variable.current);
            state_names.insert(variable.next);
        }
        for (const auto& declaration : system.context.decls) {
            if (state_names.count(declaration.name)
                && (declaration.lower_bound || declaration.upper_bound)) {
                out.diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "state bounds must be expressed in the module relations before export");
                return out;
            }
        }
        auto parser = newParser();
        Lower::HirToParser lower(parser);
        Uir::TranslationReport report;
        if (!lower.lower(system.context, report, out.diagnostics)) { return out; }
        std::unordered_set<std::string> bound;
        std::ostringstream parameters, parameter_json;
        bool first = true;
        for (const auto& v : system.variables) {
            for (const auto& item : {std::make_pair(v.current, "current"),
                                     std::make_pair(v.next, "next")}) {
                const auto node = lower.varMap().at(item.first);
                bound.insert(node->getName());
                const std::string name = dumpSMTLIB2(node);
                if (!first) { parameters << ' '; parameter_json << ','; }
                first = false;
                parameters << '(' << name << ' ' << node->getSort()->toString() << ')';
                parameter_json << "{\"source\":" << json(item.first) << ",\"symbol\":" << json(name)
                               << ",\"sort\":" << json(node->getSort()->toString())
                               << ",\"role\":" << json(v.role) << ",\"state\":" << json(item.second) << '}';
            }
        }
        if (index) { metadata << ','; }
        metadata << "{\"index\":" << index << ",\"name\":" << json(system.name)
                 << ",\"parameters\":[" << parameter_json.str() << "],\"relations\":{";
        std::vector<std::pair<std::string, H::ExprPtr>> relations{
            {"init", system.init}, {"trans", system.trans}, {"invariant", system.invariant}};
        for (std::size_t i = 0; i < system.outputs.size(); ++i) {
            relations.push_back({"output." + std::to_string(i), system.outputs[i]});
        }
        for (std::size_t i = 0; i < system.bad.size(); ++i) {
            relations.push_back({"bad." + std::to_string(i), system.bad[i]});
        }
        for (std::size_t i = 0; i < relations.size(); ++i) {
            const auto& relation = relations[i];
            const auto term = lower.lowerTerm(relation.second, out.diagnostics);
            if (!term) { return out; }
            const auto name = names.fresh("system." + std::to_string(index) + "." + relation.first);
            definitions << "(define-fun " << name << " (" << parameters.str() << ") "
                        << term->getSort()->toString() << ' ' << dumpSMTLIB2(term) << ")\n";
            if (i) { metadata << ','; }
            metadata << json(relation.first) << ':' << json(name);
        }
        metadata << "}}";
        // Rigid declarations are shared; state constants become local parameters.
        // Refuse inconsistent environments instead of dropping or shadowing one.
        const auto current = parser->dumpSMT2Module(bound);
        if (index == 0) { environment = current; }
        else if (environment != current) {
            out.diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "module systems have different rigid environments");
            return out;
        }
    }
    metadata << "],\"imports\":[";
    auto model = source.known;
    std::map<std::string, ListEncoding> lists;
    std::map<std::string, std::string> imports;
    std::ostringstream calls;
    for (std::size_t ci = 0; ci < source.unresolved.size(); ++ci) {
        const auto& call = source.unresolved[ci];
        std::vector<H::Sort> sorts;
        std::vector<H::ExprPtr> values;
        std::ostringstream signature;
        signature << json(call.predicate) << ':' << json(call.annotations);
        std::ostringstream arguments;
        for (std::size_t ai = 0; ai < call.arguments.size(); ++ai) {
            const auto& arg = call.arguments[ai];
            const auto sort_name = H::toString(arg.sort);
            signature << ':' << json(sort_name) << ':' << arg.array << ':' << arg.parameter;
            if (ai) { arguments << ','; }
            arguments << "{\"sort\":" << json(sort_name) << ",\"array\":" << (arg.array ? "true" : "false")
                      << ",\"parameter\":" << (arg.parameter ? "true" : "false") << '}';
            if (!arg.array) {
                sorts.push_back(arg.sort); values.push_back(arg.values.front()); continue;
            }
            auto it = lists.find(sort_name);
            if (it == lists.end()) {
                const auto name = names.fresh("list." + std::to_string(lists.size()));
                ListEncoding encoding{H::Sort::datatype(name), names.fresh("nil." + std::to_string(lists.size())),
                                      names.fresh("cons." + std::to_string(lists.size()))};
                H::DatatypeDecl dt;
                dt.name = name;
                dt.constructors = {{encoding.nil, {}}, {encoding.cons, {
                    {names.fresh("head." + std::to_string(lists.size())), arg.sort},
                    {names.fresh("tail." + std::to_string(lists.size())), encoding.sort}}}};
                model.datatypes.push_back(dt);
                it = lists.emplace(sort_name, encoding).first;
            }
            const auto& encoding = it->second;
            auto value = H::mkDtConstructor(encoding.nil, encoding.sort, {});
            for (auto vi = arg.values.rbegin(); vi != arg.values.rend(); ++vi) {
                value = H::mkDtConstructor(encoding.cons, encoding.sort, {*vi, value});
            }
            sorts.push_back(encoding.sort); values.push_back(value);
        }
        auto it = imports.find(signature.str());
        if (it == imports.end()) {
            const auto symbol = names.fresh("external." + std::to_string(imports.size()));
            model.funs.push_back({symbol, sorts, H::Sort::boolean(), call.loc});
            if (!imports.empty()) { metadata << ','; }
            metadata << "{\"symbol\":" << json(symbol) << ",\"predicate\":" << json(call.predicate)
                     << ",\"annotations\":" << json(call.annotations) << ",\"arguments\":[" << arguments.str() << "]}";
            it = imports.emplace(signature.str(), symbol).first;
        }
        H::Constraint constraint;
        constraint.formula = H::mkApply(it->second, H::Sort::boolean(), values, call.loc);
        constraint.loc = call.loc;
        model.constraints.push_back(constraint);
        if (ci) { calls << ','; }
        calls << "{\"index\":" << ci << ",\"symbol\":" << json(it->second)
              << ",\"file\":" << json(call.loc.file) << ",\"line\":" << call.loc.line << '}';
    }
    metadata << "],\"calls\":[" << calls.str() << "],\"array_encodings\":[";
    bool first_list = true;
    for (const auto& item : lists) {
        if (!first_list) { metadata << ','; }
        first_list = false;
        metadata << "{\"element_sort\":" << json(item.first) << ",\"sort\":" << json(H::toString(item.second.sort))
                 << ",\"nil\":" << json(item.second.nil) << ",\"cons\":" << json(item.second.cons) << '}';
    }
    metadata << "],\"objective_count\":" << model.objectives.size();
    if (!source.source_rewrites.empty()) {
        metadata << ",\"source_rewrites\":[";
        for (std::size_t i = 0; i < source.source_rewrites.size(); ++i) {
            const auto& rewrite = source.source_rewrites[i];
            if (i) { metadata << ','; }
            metadata << "{\"rule\":" << json(rewrite.rule)
                     << ",\"original\":" << json(rewrite.original)
                     << ",\"replacement\":" << json(rewrite.replacement)
                     << ",\"file\":" << json(rewrite.loc.file)
                     << ",\"line\":" << rewrite.loc.line << '}';
        }
        metadata << ']';
    }
    metadata << '}';
    if (!H::typeCheck(model, out.diagnostics)) { return out; }
    auto parser = newParser();
    Lower::HirToParser lower(parser);
    Uir::TranslationReport report;
    if (!lower.lower(model, report, out.diagnostics)) { return out; }
    const auto objectives = Lower::emitObjectives(model, Lower::OmtDialect::Z3, lower, out.diagnostics);
    if (out.diagnostics.hasErrors()) { return out; }
    const auto body = parser->dumpSMT2Module();
    if (source.systems.empty()) { environment = body; }
    else if (!model.decls.empty() || !model.funs.empty() || !model.datatypes.empty()
             || !model.constraints.empty() || !model.objectives.empty()) {
        // Current frontends produce either a library or an open constraint model.
        out.diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "mixed transition and constraint module export is not supported");
        return out;
    }
    out.interface_json = metadata.str();
    // JSON is single-line escaped: annotations cannot inject SMT commands.
    out.smt2 = "; SOMT module interface " + out.interface_json + "\n"
             + environment + definitions.str() + objectives;
    return out;
}
} // namespace

ModuleExport exportModule(const SourceModule& module) {
    try { return emit(module); }
    catch (const std::exception& e) {
        ModuleExport out;
        out.diagnostics.error(Uir::ErrorCode::E_INTERNAL, std::string("module export: ") + e.what());
        return out;
    }
}
} // namespace SOMTParser::Lang
