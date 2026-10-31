/* -*- Source -*-
 * OMT dialect emission. Do not include <cassert> (see hir_to_parser.cpp).
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/lowering/omt_emitter.h"
#include "somtparser/core/asserting.h"
#include "somtparser/hir/soft_objectives.h"

#include <algorithm>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <vector>

namespace SOMTParser::Lower {

using Uir::ErrorCode;
namespace H = Uir::Hir;

namespace {

/** Render an objective term as SMT-LIB text through the already-lowered node,
 *  so the emitter never re-implements printing. */
std::string termText(const H::ExprPtr& term,
                     HirToParser& lowered,
                     Uir::Diagnostics& diagnostics) {
    if (!term) {
        diagnostics.error(ErrorCode::E_INTERNAL, "objective has no term");
        return {};
    }
    if (term->kind == H::ExprKind::IDENT) {
        const auto& vars = lowered.varMap();
        const auto it = vars.find(term->name);
        if (it == vars.end()) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "objective refers to undeclared '" + term->name + "'");
            return {};
        }
        return lowered.parser()->toString(it->second);
    }
    // Numeric spellings also go through lowering: FlatZinc `+7` denotes the
    // integer 7, while raw `+7` is an SMT-LIB symbol rather than a numeral.
    // Anything else: lower it and let the engine's printer print it. A summed
    // objective -- every OPB/WBO instance with one, and every MaxSAT cost
    // function -- is the ordinary case, not an exotic one, and refusing it here
    // was this emitter re-implementing printing badly rather than not at all.
    auto node = lowered.lowerTerm(term, diagnostics);
    if (!node) { return {}; }
    std::ostringstream out;
    dumpSMTLIB2Shared(node, out);
    return out.str();
}

} // namespace

const char* omtDialectName(OmtDialect d) {
    switch (d) {
    case OmtDialect::SmtLib2025:  return "smtlib-omt-2025";
    case OmtDialect::Z3:          return "z3";
    case OmtDialect::OptiMathSAT: return "optimathsat";
    case OmtDialect::None:        return "none";
    }
    // A new dialect must fail here rather than be reported as "none", which the
    // evaluation would read as "objectives were deliberately dropped" -- turning
    // an unimplemented dialect into a silently different experiment.
    condAssert(false, "omtDialectName: unhandled OmtDialect");
    return "";   // unreachable; condAssert always throws
}

bool validateObjectives(const H::ConstraintModel& model,
                        HirToParser& lowered,
                        Uir::Diagnostics& diagnostics) {
    bool ok = true;
    // Deliberately does NOT check the combination. Renderability of a term is
    // dialect-free, which is this function's whole point (see the header), but
    // whether a *combination* can be rendered depends entirely on the dialect --
    // Z3 has three of the five; proposal and vendor support differ. Checking here would make
    // translate() refuse a model that toSmt2(Z3) could emit perfectly well.
    for (const auto& obj : model.objectives) {
        // Every objective, not just the first: a caller reading the diagnostics
        // to learn what a frontend still cannot express would otherwise see one
        // instance of a problem that affects several.
        if (termText(obj.term, lowered, diagnostics).empty()) {
            ok = false;
        }
    }
    return ok;
}

namespace {

std::string symbolIdentity(const std::string& spelling) {
    return spelling.size() >= 2 && spelling.front() == '|' && spelling.back() == '|'
        ? spelling.substr(1, spelling.size() - 2) : spelling;
}

std::string symbolText(const std::string& name, Uir::Diagnostics& diagnostics) {
    if (!name.empty() && H::isSoftGroupSymbol(name)) return name;
    if (!name.empty()) {
        for (const unsigned char ch : name) {
            if (ch == '|' || ch == '\\' || ch < 32 || ch == 127) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "objective or soft-group name cannot be represented as an SMT symbol");
                return {};
            }
        }
        return "|" + name + "|";
    }
    diagnostics.error(ErrorCode::E_INTERNAL, "empty objective symbol");
    return {};
}

} // namespace

RenderedOmt emitRenderedObjectives(const std::vector<RenderedObjective>& events,
                                   H::ObjectiveCombination combination,
                                   OmtDialect dialect,
                                   Uir::Diagnostics& diagnostics,
                                   const std::vector<std::string>& reserved_symbols) {
    using Kind = RenderedObjectiveKind;
    RenderedOmt result;
    result.query = "(check-sat)\n";
    (void)omtDialectName(dialect); // Reject invalid enum values, including empty input.
    if (dialect == OmtDialect::None || events.empty()) return result;

    std::unordered_set<std::string> groups;
    std::size_t objective_count = 0;
    bool has_soft = false, legacy_default = false, legacy_i = false;
    for (const auto& event : events) {
        if (event.kind == Kind::Soft) {
            has_soft = true;
            const auto group = symbolIdentity(event.group);
            if (groups.insert(group).second) ++objective_count;
            legacy_default |= event.already_emitted && group.empty();
            legacy_i |= event.already_emitted && group == "I";
            if (dialect == OmtDialect::Gomt && event.already_emitted) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    std::string(combination == H::ObjectiveCombination::SINGLE
                        ? "soft constraints" : "combined soft groups")
                    + " require GOMT define-maxsmt-objective and assert-soft :objective; "
                      "legacy module assert-soft :id commands cannot be reused");
                return {};
            }
        } else {
            ++objective_count;
        }
        if (event.term.empty() && !(event.kind == Kind::Soft && event.already_emitted)) {
            diagnostics.error(ErrorCode::E_INTERNAL, "rendered objective event has no term");
            return {};
        }
    }
    if (objective_count > 1 && combination == H::ObjectiveCombination::SINGLE) {
        diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                          "multiple objective costs require an explicit combination");
        return {};
    }
    if (dialect == OmtDialect::OptiMathSAT && legacy_default && legacy_i) {
        diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
            "OptiMathSAT aliases the unnamed soft group to I; legacy groups would merge");
        return {};
    }

    std::string priority, multi_kind;
    switch (combination) {
    case H::ObjectiveCombination::SINGLE: break;
    case H::ObjectiveCombination::LEXICOGRAPHIC:
        priority = "lex"; multi_kind = "OBJECTIVE_LEX"; break;
    case H::ObjectiveCombination::PARETO:
        priority = "pareto"; multi_kind = "OBJECTIVE_PARETO"; break;
    case H::ObjectiveCombination::BOX:
        priority = "box"; multi_kind = "OBJECTIVE_BOX"; break;
    case H::ObjectiveCombination::MINMAX: multi_kind = "OBJECTIVE_MINMAX"; break;
    case H::ObjectiveCombination::MAXMIN: multi_kind = "OBJECTIVE_MAXMIN"; break;
    default:
        diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT, "unknown objective combination");
        return {};
    }
    const bool extreme = combination == H::ObjectiveCombination::MINMAX
        || combination == H::ObjectiveCombination::MAXMIN;
    if (extreme && dialect == OmtDialect::Z3) {
        diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                          "minmax/maxmin has no direct z3 objective rendering");
        return {};
    }
    if (extreme && dialect == OmtDialect::OptiMathSAT) {
        // OptiMathSAT's minmax/maxmin take raw terms, not directed objectives.
        // Do not silently erase a member's opposite direction or a soft group.
        const auto required = combination == H::ObjectiveCombination::MINMAX
            ? Kind::Minimize : Kind::Maximize;
        if (has_soft || std::any_of(events.begin(), events.end(), [&](const auto& event) {
                return event.kind != required;
            })) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "OptiMathSAT minmax/maxmin requires uniformly directed arithmetic members");
            return {};
        }
    }

    // References checked 2026-10-13:
    // https://optimathsat.disi.unitn.it/pages/smt2reference.html
    // https://ceur-ws.org/Vol-4008/SMT_paper25.pdf (Fig. 1, Sections 3.1-3.3).
    // The proposal is not an adopted SMT-LIB standard.
    if (dialect == OmtDialect::Gomt) {
        result.preamble = "(set-option :enable-omt true)\n";
    } else {
        if (dialect == OmtDialect::OptiMathSAT) {
            // The solver also requires CLI -optimization=true; an SMT model
            // option is not a substitute for that executable configuration.
            result.preamble = "(set-option :produce-models true)\n";
        }
        if (!priority.empty()) result.preamble += "(set-option :opt.priority " + priority + ")\n";
    }

    std::unordered_set<std::string> used, declared;
    for (const auto& name : reserved_symbols) {
        used.insert(symbolIdentity(name));
        declared.insert(symbolIdentity(name));
    }
    // Reserve explicit group labels before generating an unnamed vendor group.
    for (const auto& event : events) {
        if (dialect == OmtDialect::OptiMathSAT && event.kind == Kind::Soft && !event.group.empty()) {
            used.insert(symbolIdentity(event.group));
        }
    }
    const auto fresh = [&](const std::string& requested) {
        std::string name = symbolIdentity(requested);
        if (name.empty()) name = "obj";
        while (!used.insert(name).second) name += "_";
        return symbolText(name, diagnostics);
    };
    std::unordered_map<std::string, std::string> group_names;
    std::ostringstream commands;
    if (extreme && dialect == OmtDialect::OptiMathSAT) {
        commands << '(' << (combination == H::ObjectiveCombination::MINMAX ? "minmax" : "maxmin");
        for (const auto& event : events) commands << ' ' << event.term;
        commands << ")\n";
        result.commands = commands.str();
        return result;
    }
    for (std::size_t index = 0; index < events.size(); ++index) {
        const auto& event = events[index];
        if (event.kind == Kind::Soft) {
            const auto identity = symbolIdentity(event.group);
            auto found = group_names.find(identity);
            const bool first = found == group_names.end();
            if (first) {
                std::string name;
                if (dialect == OmtDialect::Gomt) {
                    name = fresh(identity.empty() ? "soft" : identity);
                    result.objective_names.push_back(name);
                    commands << "(define-maxsmt-objective " << name << ")\n";
                } else if (dialect == OmtDialect::OptiMathSAT) {
                    if (identity.empty()) {
                        name = event.already_emitted ? "I" : fresh("__somt_soft_default");
                    } else if (declared.count(identity)) {
                        if (event.already_emitted) {
                            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "OptiMathSAT legacy soft-group label collides with a declared symbol");
                            return {};
                        }
                        name = fresh(identity);
                    } else {
                        // Group labels reserve each other's generated names,
                        // but are not ordinary declared symbols. Renaming every
                        // reserved group here would drift on every round trip.
                        name = symbolText(event.group, diagnostics);
                    }
                } else if (!identity.empty()) {
                    name = symbolText(event.group, diagnostics);
                }
                found = group_names.emplace(identity, name).first;
            }
            if (!event.already_emitted) {
                commands << "(assert-soft " << event.term << " :weight "
                         << (event.weight.empty() ? "1" : event.weight);
                if (dialect == OmtDialect::Gomt) commands << " :objective " << found->second;
                else if (!found->second.empty()) commands << " :id " << found->second;
                commands << ")\n";
            }
            // Unlike Z3, OptiMathSAT does not activate assert-soft groups by
            // itself. Its explicit minimize goes at the group's first event.
            if (first && dialect == OmtDialect::OptiMathSAT) {
                commands << "(minimize " << found->second << ")\n";
            }
        } else if (dialect == OmtDialect::Gomt) {
            const auto name = fresh(event.name.empty() ? "obj" + std::to_string(index) : event.name);
            result.objective_names.push_back(name);
            commands << "(define-objective " << name << ' '
                     << (event.kind == Kind::Minimize ? "OBJECTIVE_MIN" : "OBJECTIVE_MAX")
                     << ' ' << event.term << ")\n";
        } else {
            commands << '(' << (event.kind == Kind::Minimize ? "minimize" : "maximize")
                     << ' ' << event.term << ")\n";
        }
    }
    if (diagnostics.hasErrors()) return {};
    if (dialect == OmtDialect::Gomt) {
        std::string queried;
        if (!multi_kind.empty()) {
            queried = fresh("multi");
            commands << "(define-multi-objective " << queried << ' ' << multi_kind;
            for (const auto& name : result.objective_names) commands << ' ' << name;
            commands << ")\n";
        } else if (!result.objective_names.empty()) {
            queried = result.objective_names.front();
        }
        if (!queried.empty()) result.query = "(optimize-sat " + queried + ")\n";
    }
    result.commands = commands.str();
    return result;
}

std::string emitObjectives(const H::ConstraintModel& model,
                           OmtDialect dialect,
                           HirToParser& lowered,
                           Uir::Diagnostics& diagnostics,
                           std::optional<std::size_t> soft_objective_count,
                           std::vector<std::string>* objective_names,
                           std::string* preamble) {
    if (objective_names) objective_names->clear();
    if (preamble) preamble->clear();
    auto groups = H::softObjectiveGroups(model);
    const std::size_t count = soft_objective_count ? *soft_objective_count : groups.size();
    if (dialect == OmtDialect::None) {
        if (count && model.objective_combination != H::ObjectiveCombination::SINGLE) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "combined soft groups cannot be retained by the feasibility-only dialect");
        }
        return {};
    }
    if (groups.size() != count) {
        // Consuming lowering may release HIR records; recover group order from
        // the retained parser's source-indexed soft assertions when possible.
        groups.clear();
        const auto soft = lowered.parser()->getSoftAssertions();
        const auto grouped = lowered.parser()->getGroupedSoftAssertions();
        std::unordered_set<std::string> seen;
        for (std::size_t index = 0; index < soft.size(); ++index) {
            std::string group;
            for (const auto& candidate : grouped) {
                if (candidate.second.count(index)) { group = symbolIdentity(candidate.first); break; }
            }
            if (seen.insert(group).second) groups.push_back(group);
        }
        if (groups.empty() && count == 1 && !model.packed_bool_clauses.empty()) groups.push_back("");
        if (groups.size() != count) {
            if (dialect == OmtDialect::Z3) {
                // Z3 groups are already active. Identity is immaterial to this
                // marker-only priority emission; never use these names elsewhere.
                groups.clear();
                for (std::size_t i = 0; i < count; ++i) groups.push_back("__active_soft_" + std::to_string(i));
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "consumed soft-group names are unavailable for this OMT dialect");
                return {};
            }
        }
    }
    std::vector<RenderedObjective> events;
    if ((dialect == OmtDialect::Gomt || dialect == OmtDialect::OptiMathSAT) && count) {
        // These callers emit a hard-only module. Recover exact soft records
        // from the lowered parser, including after consuming HIR transforms.
        // OptiMathSAT needs fresh group labels when user declarations collide;
        // marker-only events cannot rename labels already printed in a body.
        const auto assertions = lowered.parser()->getSoftAssertions();
        const auto weights = lowered.parser()->getSoftWeights();
        const auto grouped = lowered.parser()->getGroupedSoftAssertions();
        std::unordered_set<std::string> observed_groups;
        for (std::size_t index = 0; index < assertions.size(); ++index) {
            RenderedObjective event;
            event.kind = RenderedObjectiveKind::Soft;
            std::ostringstream term;
            dumpSMTLIB2Shared(assertions[index], term);
            event.term = term.str();
            if (index < weights.size() && weights[index]) {
                event.weight = softWeightToken(weights[index]);
            }
            std::string identity;
            for (const auto& group : grouped) {
                if (group.second.count(index)) {
                    identity = symbolIdentity(group.first);
                    event.group = symbolText(group.first, diagnostics);
                    break;
                }
            }
            observed_groups.insert(identity);
            events.push_back(std::move(event));
        }
        if (observed_groups.size() != count) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "lowered soft assertion groups disagree with the cached objective count");
            return {};
        }
    } else {
        for (const auto& group : groups) {
            RenderedObjective event;
            event.kind = RenderedObjectiveKind::Soft;
            event.group = group.empty() ? "" : symbolText(group, diagnostics);
            event.already_emitted = true;
            events.push_back(std::move(event));
        }
    }
    for (const auto& objective : model.objectives) {
        RenderedObjective event;
        event.kind = objective.kind == H::ObjKind::MINIMIZE
            ? RenderedObjectiveKind::Minimize : RenderedObjectiveKind::Maximize;
        event.term = termText(objective.term, lowered, diagnostics);
        event.name = objective.name;
        if (event.term.empty()) return {};
        events.push_back(std::move(event));
    }
    std::vector<std::string> reserved;
    for (const auto& declaration : model.decls) reserved.push_back(declaration.name);
    for (const auto& function : model.funs) reserved.push_back(function.name);
    // Translation can release HIR declaration metadata after lowering. Names
    // still exist in the parser and must reserve generated objective symbols.
    if (dialect == OmtDialect::Gomt || dialect == OmtDialect::OptiMathSAT) {
        for (const auto& variable : lowered.parser()->getVariables()) reserved.push_back(variable->getName());
        for (const auto& function : lowered.parser()->getFunctions()) reserved.push_back(function->getName());
    }
    const auto rendered = emitRenderedObjectives(events, model.objective_combination,
                                                 dialect, diagnostics, reserved);
    if (diagnostics.hasErrors()) return {};
    if (objective_names) *objective_names = rendered.objective_names;
    if (preamble) *preamble = rendered.preamble;
    return (preamble ? std::string{} : rendered.preamble) + rendered.commands
        + (dialect == OmtDialect::Gomt && !rendered.objective_names.empty() ? rendered.query : "");
}

} // namespace SOMTParser::Lower
