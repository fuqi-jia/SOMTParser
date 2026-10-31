/* -*- Source -*-
 * PDDL 1.2 classical/ADL frontend.
 *
 * A source problem denotes finite object structures and arbitrary-length
 * action traces. This adapter constructs the bounded institution explicitly:
 * source trace coordinates are mapped injectively to Boolean target constants,
 * administrative one-hot/noop constraints are A_Sigma, action progression is
 * alpha, and beta removes the generated noop suffix from the decoded plan.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/pddl.h"
#include "somtparser/languages/pddl_internal.h"
#include "somtparser/languages/planning_types.h"
#include "somtparser/hir/planning_numeric.h"
#include "somtparser/hir/planning_objects.h"
#include "somtparser/hir/planning_continuous.h"
#include "somtparser/hir/planning_temporal.h"
#include "somtparser/hir/planning_timed_initial.h"
#include "somtparser/hir/planning_derived.h"
#include "somtparser/hir/planning_trajectory.h"

#include <algorithm>
#include <cctype>
#include <climits>
#include <filesystem>
#include <fstream>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
namespace P = H::Planning;
namespace S = Uir::Sem;
using Uir::ErrorCode;

constexpr char STATIC_ATOM_PREFIX[] = "__pddl_static:";

struct Sexp {
    std::string       atom;
    std::vector<Sexp> list;

    bool isAtom() const { return !atom.empty(); }
    const std::string& head() const {
        static const std::string empty;
        return list.empty() || !list[0].isAtom() ? empty : list[0].atom;
    }
};

class SexpReader {
public:
    explicit SexpReader(const std::string& source) : source_(source) {}

    bool readAll(std::vector<Sexp>& result) {
        for (;;) {
            skip();
            if (at_ == source_.size()) { return true; }
            Sexp expression;
            if (!read(expression)) { return false; }
            result.push_back(std::move(expression));
        }
    }

private:
    void skip() {
        while (at_ < source_.size()) {
            if (source_[at_] == ';') {
                while (at_ < source_.size() && source_[at_] != '\n') { ++at_; }
            } else if (std::isspace(static_cast<unsigned char>(source_[at_]))) {
                ++at_;
            } else {
                return;
            }
        }
    }

    bool read(Sexp& result) {
        skip();
        if (at_ == source_.size()) { return false; }
        if (source_[at_] == '(') {
            ++at_;
            for (;;) {
                skip();
                if (at_ == source_.size()) { return false; }
                if (source_[at_] == ')') {
                    ++at_;
                    return true;
                }
                Sexp child;
                if (!read(child)) { return false; }
                result.list.push_back(std::move(child));
            }
        }
        if (source_[at_] == ')') { return false; }
        const std::size_t begin = at_;
        while (at_ < source_.size()
               && !std::isspace(static_cast<unsigned char>(source_[at_]))
               && source_[at_] != '(' && source_[at_] != ')') {
            ++at_;
        }
        result.atom = source_.substr(begin, at_ - begin);
        std::transform(result.atom.begin(), result.atom.end(), result.atom.begin(),
                       [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
        return !result.atom.empty();
    }

    const std::string& source_;
    std::size_t        at_ = 0;
};

struct Typed {
    std::string name;
    std::string type;
};

struct Predicate {
    std::vector<Typed> params;
};

struct Action {
    std::string        name;
    std::vector<Typed> params;
    Sexp               precondition;
    Sexp               effect;
    bool               has_precondition = false;
    bool               has_effect = false;
    bool               durative = false;
    Sexp               duration;
};

struct GroundAtom {
    std::string              predicate;
    std::vector<std::string> args;
    std::string              target_base;
    std::string              source_label;
};

struct TimedInitialSource {
    H::ExprPtr time;
    Sexp literal; // The basic atom, with polarity recorded separately.
    bool value = true;
};

struct DerivedRule {
    Sexp head;
    Sexp body;
    std::vector<Typed> params;
};

struct GroundAction {
    const Action*            schema = nullptr;
    std::vector<std::string> args;
    std::string              target_base;
    std::string              source_label;
    unsigned                 earliest_step = 0;
};

using Environment = std::unordered_map<std::string, std::string>;

struct FluentUpdates {
    std::vector<H::ExprPtr> add_conditions;
    std::vector<H::ExprPtr> delete_conditions;
};

H::ExprPtr conjunction(std::vector<H::ExprPtr> terms) {
    for (const auto& term : terms) {
        if (term->kind == H::ExprKind::LIT_BOOL && !term->bool_value) { return term; }
    }
    terms.erase(std::remove_if(terms.begin(), terms.end(), [](const auto& term) {
        return term->kind == H::ExprKind::LIT_BOOL;
    }), terms.end());
    if (terms.empty()) { return H::mkBool(true); }
    if (terms.size() == 1) { return std::move(terms.front()); }
    // Finite quantifiers can have tens of thousands of instances. A left
    // fold needlessly makes every subsequent recursive HIR pass that deep.
    return H::mkOp(H::Op::AND, std::move(terms));
}

H::ExprPtr disjunction(std::vector<H::ExprPtr> terms) {
    for (const auto& term : terms) {
        if (term->kind == H::ExprKind::LIT_BOOL && term->bool_value) { return term; }
    }
    terms.erase(std::remove_if(terms.begin(), terms.end(), [](const auto& term) {
        return term->kind == H::ExprKind::LIT_BOOL;
    }), terms.end());
    if (terms.empty()) { return H::mkBool(false); }
    if (terms.size() == 1) { return std::move(terms.front()); }
    return H::mkOp(H::Op::OR, std::move(terms));
}

H::ExprPtr negation(const H::ExprPtr& term) {
    return term->kind == H::ExprKind::LIT_BOOL
        ? H::mkBool(!term->bool_value) : H::mkOp(H::Op::NOT, {term});
}

std::string hex(const std::string& value) {
    static const char digits[] = "0123456789abcdef";
    std::string result;
    result.reserve(value.size() * 2);
    for (unsigned char c : value) {
        result.push_back(digits[c >> 4]);
        result.push_back(digits[c & 15]);
    }
    return result;
}

std::string canonical(const std::string& head,
                      const std::vector<std::string>& tail) {
    std::string result = std::to_string(head.size()) + ":" + head;
    for (const std::string& item : tail) {
        result += "/" + std::to_string(item.size()) + ":" + item;
    }
    return result;
}

std::string sourceCall(const std::string& name,
                       const std::vector<std::string>& args) {
    std::string result = "(" + name;
    for (const std::string& arg : args) { result += " " + arg; }
    return result + ")";
}

class PddlParser {
public:
    PddlParser(std::string domain, std::string problem, std::string file,
               unsigned horizon)
        : domain_text_(std::move(domain)), problem_text_(std::move(problem)),
          file_(std::move(file)), horizon_(horizon) {
        types_.emplace("object", std::set<std::string>{});
    }

    /** Accept constructs the declared `:requirements` do not license.
     *  Off by default; see requireFeature for why the default is strict. */
    void setLenientRequirements(bool on) { lenient_requirements_ = on; }
    void setAllowedActions(const PddlInternal::ActionInstances* actions) { allowed_actions_ = actions; }
    void setMultipleInheritance(bool on) { multiple_inheritance_ = on; }
    void setPolicy(std::string mode, unsigned size) {
        policy_mode_ = std::move(mode); policy_size_ = size;
    }
    void setHasHorizon(bool supplied) { has_horizon_ = supplied; }
    bool usesPolicy() const {
        return !policy_mode_.empty() && requirements_.count(":non-deterministic");
    }

    H::ConstraintModelPtr parse(Uir::Diagnostics& diagnostics,
                                Uir::TranslationReport& report) {
        if (!readDomain(diagnostics) || !readProblem(diagnostics)
            || !validateDeclarations(diagnostics) || !prepareTrajectorySource(diagnostics)
            || !validateDerivedHeads(diagnostics)) {
            return nullptr;
        }
        if (usesPolicy()) {
            if (!derived_.empty()) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "derived predicates are not yet integrated with the FOND policy institution");
                return nullptr;
            }
            return buildPolicy(diagnostics, report);
        }
        if (!has_horizon_) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "a deterministic PDDL task requires plan_horizon");
            return nullptr;
        }
        return temporal_mode_ ? buildTemporal(diagnostics, report) : build(diagnostics, report);
    }

    S::ModelProjection takeModelProjection() { return std::move(projection_); }
    S::Signature takeSourceSignature() { return std::move(source_signature_); }
    std::vector<S::SymbolMapping> takeSymbolMap() { return std::move(symbol_map_); }
    std::vector<S::Sentence> takeTargetAxioms() { return std::move(target_axioms_); }

private:
    static bool isName(const std::string& name) {
        if (name.empty() || !std::isalpha(static_cast<unsigned char>(name[0]))) {
            return false;
        }
        for (unsigned char c : name) {
            if (!std::isalnum(c) && c != '-' && c != '_') { return false; }
        }
        return true;
    }

    static bool isVariable(const std::string& name) {
        return name.size() > 1 && name[0] == '?' && isName(name.substr(1));
    }

    bool readSingle(const std::string& text, const std::string& kind,
                    Sexp& result, Uir::Diagnostics& diagnostics) const {
        std::vector<Sexp> roots;
        SexpReader reader(text);
        if (!reader.readAll(roots) || roots.size() != 1 || roots[0].head() != "define") {
            diagnostics.error(ErrorCode::E_PARSE,
                              "the " + kind
                                  + " file must contain exactly one well-formed `(define ...)`");
            return false;
        }
        result = std::move(roots[0]);
        return true;
    }

    std::optional<std::string> objectTypeExpression(const Sexp& expression,
                                                     Uir::Diagnostics& diagnostics) {
        if (expression.isAtom() && isName(expression.atom)) { return expression.atom; }
        if (expression.head() != "either" || expression.list.size() < 2) {
            diagnostics.error(ErrorCode::E_PARSE, "a type must be a name or a nonempty `(either ...)`");
            return std::nullopt;
        }
        std::set<std::string> members;
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            const auto& member = expression.list[i];
            if (!member.isAtom() || !isName(member.atom)) {
                diagnostics.error(ErrorCode::E_PARSE, "`either` members must be primitive type names");
                return std::nullopt;
            }
            members.insert(member.atom);
        }
        // Parentheses cannot occur in a primitive type name, so this internal
        // key cannot collide with a source type. Normalization does not merge
        // nominal types merely because this particular problem has no objects.
        std::string key = "(either";
        for (const auto& member : members) { key += " " + member; }
        key += ")";
        union_types_.emplace(key, std::move(members));
        return key;
    }

    bool knownObjectType(const std::string& name) const {
        const auto compound = union_types_.find(name);
        if (compound == union_types_.end()) { return types_.count(name) != 0; }
        for (const auto& member : compound->second) {
            if (types_.count(member) == 0) { return false; }
        }
        return true;
    }

    bool typedList(const Sexp& expression, std::size_t from, bool variables,
                   const std::string& context, std::vector<Typed>& result,
                   Uir::Diagnostics& diagnostics, bool repeated_types = false) {
        std::vector<std::string> pending;
        std::set<std::string> names;
        for (std::size_t i = from; i < expression.list.size(); ++i) {
            const Sexp& item = expression.list[i];
            if (!item.isAtom()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  context + " expects a name or variable before a type annotation");
                return false;
            }
            if (item.atom == "-") {
                if (pending.empty() || i + 1 >= expression.list.size()) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed typed list in " + context);
                    return false;
                }
                const auto type = objectTypeExpression(expression.list[++i], diagnostics);
                if (!type) { return false; }
                if (!variables && union_types_.count(*type)) {
                    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "union-typed parameters are supported; concrete object declarations and "
                        "the primitive type hierarchy require a single nominal type");
                    return false;
                }
                for (const std::string& name : pending) {
                    result.push_back({name, *type});
                }
                pending.clear();
                continue;
            }
            const bool valid = variables ? isVariable(item.atom) : isName(item.atom);
            if (!valid) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "invalid " + std::string(variables ? "variable" : "name")
                                      + " '" + item.atom + "' in " + context);
                return false;
            }
            if (!names.insert(item.atom).second && !repeated_types) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate name '" + item.atom + "' in " + context);
                return false;
            }
            pending.push_back(item.atom);
        }
        for (const std::string& name : pending) { result.push_back({name, "object"}); }
        for (const Typed& item : result) {
            if (item.type != "object") { uses_typing_ = true; }
        }
        return true;
    }

    bool readRequirements(const Sexp& section, Uir::Diagnostics& diagnostics) {
        static const std::set<std::string> supported = {
            ":strips", ":typing", ":negative-preconditions",
            ":disjunctive-preconditions", ":equality",
            ":existential-preconditions", ":universal-preconditions",
            ":quantified-preconditions", ":conditional-effects", ":adl", ":action-costs",
            ":fluents", ":numeric-fluents", ":object-fluents",
            ":derived-predicates", ":durative-actions", ":duration-inequalities",
            ":timed-initial-literals", ":continuous-effects", ":constraints", ":preferences",
        };
        for (std::size_t i = 1; i < section.list.size(); ++i) {
            if (!section.list[i].isAtom() || section.list[i].atom.empty()
                || section.list[i].atom[0] != ':') {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed PDDL `:requirements` entry");
                return false;
            }
            const std::string& requirement = section.list[i].atom;
            if (requirement == ":non-deterministic" && policy_mode_.empty()) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    ":non-deterministic tasks require explicit fond_policy=strong "
                    "or fond_policy=strong-cyclic and policy_size=N; the two "
                    "modes have different outcome-fairness semantics");
                return false;
            }
            if (supported.count(requirement) == 0
                && !(requirement == ":non-deterministic" && !policy_mode_.empty())) {
                diagnostics.error(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "PDDL requirement '" + requirement
                        + "' is outside the deterministic finite classical/ADL "
                          "institution implemented by this frontend");
                return false;
            }
            requirements_.insert(requirement);
        }
        return true;
    }

    bool readDomain(Uir::Diagnostics& diagnostics) {
        Sexp definition;
        if (!readSingle(domain_text_, "domain", definition, diagnostics)) { return false; }
        if (definition.list.size() < 2 || definition.list[1].head() != "domain"
            || definition.list[1].list.size() != 2
            || !definition.list[1].list[1].isAtom()
            || !isName(definition.list[1].list[1].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed PDDL domain header");
            return false;
        }
        domain_name_ = definition.list[1].list[1].atom;

        std::set<std::string> singleton_sections;
        for (std::size_t i = 2; i < definition.list.size(); ++i) {
            const Sexp& section = definition.list[i];
            const std::string head = section.head();
            if (head.empty()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "a PDDL domain section has no atomic head");
                return false;
            }
            if (head != ":action" && head != ":derived" && head != ":durative-action" && !singleton_sections.insert(head).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate PDDL domain section '" + head + "'");
                return false;
            }
            if (head == ":requirements") {
                if (!readRequirements(section, diagnostics)) { return false; }
            } else if (head == ":types") {
                std::vector<Typed> declarations;
                if (!typedList(section, 1, false, "`:types`", declarations,
                               diagnostics, multiple_inheritance_)) {
                    return false;
                }
                uses_typing_ = true;
                for (const Typed& declaration : declarations) {
                    if (declaration.name == "object"
                        || (types_.count(declaration.name) && !multiple_inheritance_)) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "duplicate or reserved type '"
                                              + declaration.name + "'");
                        return false;
                    }
                    types_[declaration.name].insert(declaration.type);
                }
            } else if (head == ":constants") {
                if (!typedList(section, 1, false, "`:constants`", domain_objects_,
                               diagnostics)) {
                    return false;
                }
            } else if (head == ":predicates") {
                for (std::size_t p = 1; p < section.list.size(); ++p) {
                    const Sexp& declaration = section.list[p];
                    if (declaration.list.empty() || !declaration.list[0].isAtom()
                        || !isName(declaration.list[0].atom)) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "malformed predicate declaration");
                        return false;
                    }
                    Predicate predicate;
                    if (!typedList(declaration, 1, true, "predicate '"
                                       + declaration.list[0].atom + "'",
                                   predicate.params, diagnostics)) {
                        return false;
                    }
                    if (!predicates_.emplace(declaration.list[0].atom,
                                             std::move(predicate)).second) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "duplicate predicate '"
                                              + declaration.list[0].atom + "'");
                        return false;
                    }
                }
            } else if (head == ":durative-action") {
                if (!readDurativeAction(section, diagnostics)) { return false; }
            } else if (head == ":action") {
                if (!readAction(section, diagnostics)) { return false; }
            } else if (head == ":functions") {
                std::vector<Sexp> pending;
                const auto declareFunctions = [&](const std::string& result_type) {
                    for (const auto& declaration : pending) {
                        Predicate function;
                        const auto& name = declaration.head();
                        if (declaration.isAtom() || !isName(name)
                            || !typedList(declaration, 1, true, "function parameters", function.params, diagnostics)
                            || numeric_functions_.count(name) || object_functions_.count(name)) {
                            diagnostics.error(ErrorCode::E_PARSE, "malformed or duplicate function declaration");
                            return false;
                        }
                        if (result_type == "number") { numeric_functions_.emplace(name, std::move(function)); }
                        else {
                            object_functions_.emplace(name, std::move(function));
                            object_result_types_.emplace(name, result_type);
                            if (result_type != "object") { uses_typing_ = true; }
                        }
                    }
                    pending.clear();
                    return true;
                };
                for (std::size_t f = 1; f < section.list.size(); ++f) {
                    if (section.list[f].isAtom() && section.list[f].atom == "-") {
                        if (pending.empty() || f + 1 >= section.list.size()) {
                            diagnostics.error(ErrorCode::E_PARSE, "function return annotation needs preceding declarations and a type");
                            return false;
                        }
                        const auto type = objectTypeExpression(section.list[++f], diagnostics);
                        if (!type || !declareFunctions(*type)) { return false; }
                    } else { pending.push_back(section.list[f]); }
                }
                // The deprecated implicit numeric return remains compatible.
                if (!declareFunctions("number")) { return false; }
            } else if (head == ":task" || head == ":method") {
                diagnostics.error(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "'" + head
                        + "' declares HDDL hierarchy; translating only goal reachability "
                          "would admit plans that have no task-network decomposition");
                return false;
            } else if (head == ":derived") {
                if (section.list.size() != 3 || section.list[1].isAtom()
                    || !isName(section.list[1].head())) {
                    diagnostics.error(ErrorCode::E_PARSE, "malformed derived predicate rule");
                    return false;
                }
                derived_.push_back({section.list[1], section.list[2], {}});
                derived_predicates_.insert(section.list[1].head());
            } else if (head == ":constraints") {
                if (section.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE, ":constraints requires one formula"); return false;
                }
                // IPC5 BNF: a domain has con-GD, whereas a problem has
                // pref-con-GD. Domain constraints therefore cannot be soft.
                if (containsPreference(section.list[1])) {
                    diagnostics.error(ErrorCode::E_PARSE,
                        "domain :constraints must be hard con-GD; preferences belong in problem :constraints");
                    return false;
                }
                trajectory_constraints_.push_back(section.list[1]);
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unknown or unsupported PDDL domain section '"
                                      + head + "'");
                return false;
            }
        }
        if (requirements_.empty()) { requirements_.insert(":strips"); }
        return true;
    }

    bool readAction(const Sexp& section, Uir::Diagnostics& diagnostics) {
        if (section.list.size() < 2 || !section.list[1].isAtom()
            || !isName(section.list[1].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed PDDL action header");
            return false;
        }
        Action action;
        action.name = section.list[1].atom;
        if (action_names_.count(action.name) != 0) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "duplicate action '" + action.name + "'");
            return false;
        }
        std::set<std::string> keys;
        for (std::size_t i = 2; i < section.list.size();) {
            if (!section.list[i].isAtom() || section.list[i].atom.empty()
                || section.list[i].atom[0] != ':' || i + 1 >= section.list.size()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed body of action '" + action.name + "'");
                return false;
            }
            const std::string key = section.list[i].atom;
            const Sexp& value = section.list[i + 1];
            i += 2;
            if (!keys.insert(key).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate '" + key + "' in action '"
                                      + action.name + "'");
                return false;
            }
            if (key == ":parameters") {
                if (value.isAtom()
                    || !typedList(value, 0, true,
                                  "parameters of action '" + action.name + "'",
                                  action.params, diagnostics)) {
                    return false;
                }
            } else if (key == ":precondition") {
                action.precondition = value;
                action.has_precondition = true;
            } else if (key == ":effect") {
                action.effect = value;
                action.has_effect = true;
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unknown action field '" + key + "' in '"
                                      + action.name + "'");
                return false;
            }
        }
        action_names_.insert(action.name);
        actions_.push_back(std::move(action));
        return true;
    }

    bool readProblem(Uir::Diagnostics& diagnostics) {
        Sexp definition;
        if (!readSingle(problem_text_, "problem", definition, diagnostics)) { return false; }
        std::string{}.swap(problem_text_);
        if (definition.list.size() < 2 || definition.list[1].head() != "problem"
            || definition.list[1].list.size() != 2
            || !definition.list[1].list[1].isAtom()
            || !isName(definition.list[1].list[1].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed PDDL problem header");
            return false;
        }
        problem_name_ = definition.list[1].list[1].atom;

        std::set<std::string> seen;
        bool has_domain = false;
        for (std::size_t i = 2; i < definition.list.size(); ++i) {
            Sexp& section = definition.list[i];
            const std::string head = section.head();
            if (head.empty() || !seen.insert(head).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  head.empty() ? "a PDDL problem section has no atomic head"
                                               : "duplicate PDDL problem section '" + head + "'");
                return false;
            }
            if (head == ":domain") {
                if (section.list.size() != 2 || !section.list[1].isAtom()) {
                    diagnostics.error(ErrorCode::E_PARSE, "malformed problem `:domain`");
                    return false;
                }
                has_domain = true;
                if (section.list[1].atom != domain_name_) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "problem names domain '" + section.list[1].atom
                                          + "' but the supplied domain is '" + domain_name_ + "'");
                    return false;
                }
            } else if (head == ":requirements") {
                if (!readRequirements(section, diagnostics)) { return false; }
            } else if (head == ":objects") {
                if (!typedList(section, 1, false, "`:objects`", problem_objects_,
                               diagnostics)) {
                    return false;
                }
            } else if (head == ":init") {
                // Transfer the potentially very large fact table. Keeping a
                // second deep copy here doubles the peak parser allocation.
                init_ = std::move(section.list);
                init_.erase(init_.begin());
            } else if (head == ":goal") {
                if (section.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "PDDL `:goal` takes exactly one formula");
                    return false;
                }
                goal_ = std::move(section.list[1]);
                has_goal_ = true;
            } else if (head == ":metric") {
                if (section.list.size() != 3 || (section.list[1].atom != "minimize" && section.list[1].atom != "maximize")) {
                    diagnostics.error(ErrorCode::E_PARSE, "metric requires minimize/maximize and one numeric expression");
                    return false;
                }
                metric_ = section.list[2];
                metric_direction_ = section.list[1].atom;
                minimize_cost_ = metric_direction_ == "minimize" && metric_.head() == "total-cost" && metric_.list.size() == 1;
            } else if (head == ":constraints") {
                if (section.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE, ":constraints requires one formula"); return false;
                }
                trajectory_constraints_.push_back(section.list[1]);
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unknown or unsupported PDDL problem section '"
                                      + head + "'");
                return false;
            }
        }
        if (!has_domain) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "the problem omits its required `:domain` reference");
            return false;
        }
        if (!has_goal_) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "the problem declares no goal");
            return false;
        }
        return readTimedInitialLiterals(diagnostics);
    }

    bool readTimedInitialLiterals(Uir::Diagnostics& diagnostics) {
        std::vector<Sexp> ordinary;
        for (auto& expression : init_) {
            // A basic predicate named `at` still uses ordinary object terms.
            const bool timed = expression.head() == "at" && expression.list.size() == 3
                && !expression.list[2].isAtom();
            if (!timed) { ordinary.push_back(std::move(expression)); continue; }
            if (!requireFeature(":timed-initial-literals", "timed initial literal", diagnostics)) { return false; }
            const auto& token = expression.list[1];
            if (!decimalNumber(token) || token.atom.front() == '-'
                || token.atom.find_first_of("123456789") == std::string::npos) {
                diagnostics.error(ErrorCode::E_PARSE, "timed initial literals require a strictly positive exact decimal time");
                return false;
            }
            const auto time = P::numericConstant(token.atom.front() == '+' ? token.atom.substr(1) : token.atom, diagnostics);
            if (!time) { return false; }
            Sexp literal = expression.list[2];
            bool positive = true;
            if (literal.head() == "not") {
                if (literal.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE, "malformed negative timed initial literal");
                    return false;
                }
                positive = false;
                Sexp atom = literal.list[1];
                literal = std::move(atom);
            }
            if (literal.isAtom() || literal.list.empty() || !predicates_.count(literal.head())
                || derived_predicates_.count(literal.head())) {
                diagnostics.error(ErrorCode::E_TYPE, "timed initial literals may assign only declared basic predicates");
                return false;
            }
            timed_initial_.push_back({time->value, std::move(literal), positive});
            temporal_mode_ = true;
        }
        init_ = std::move(ordinary);
        return true;
    }

    bool validateDeclarations(Uir::Diagnostics& diagnostics) {
        continuous_mode_ = featureEnabled(":continuous-effects");
        temporal_mode_ = temporal_mode_ || featureEnabled(":durative-actions") || continuous_mode_;
        object_mode_ = !object_functions_.empty();
        numeric_mode_ = featureEnabled(":fluents") || temporal_mode_ || object_mode_;
        if (object_mode_ && !requireFeature(":object-fluents", "object-valued functions", diagnostics)) { return false; }
        if (object_mode_ && usesPolicy()) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "object fluents do not yet support the nondeterministic policy institution");
            return false;
        }
        if (object_mode_ && !numeric_functions_.empty()
            && !requireFeature(":numeric-fluents", "numeric functions combined with object functions", diagnostics)) { return false; }
        if (!numeric_mode_ && !metric_direction_.empty() && !minimize_cost_ && !featureEnabled(":preferences")) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "the action-cost fragment supports only `:metric minimize (total-cost)`; general metrics require :fluents");
            return false;
        }
        if (numeric_mode_ && usesPolicy()) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT, "general numeric states require deterministic planning");
            return false;
        }
        if (!PlanningInternal::validateTypes(types_, "PDDL", diagnostics)) { return false; }
        const auto validateTyped = [&](const std::vector<Typed>& values,
                                       const std::string& context) {
            for (const Typed& value : values) {
                if (!knownObjectType(value.type)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      context + " uses unknown type '" + value.type + "'");
                    return false;
                }
            }
            return true;
        };
        for (const auto& [name, predicate] : predicates_) {
            if (!validateTyped(predicate.params, "predicate '" + name + "'")) {
                return false;
            }
        }
        for (const Action& action : actions_) {
            if (!validateTyped(action.params, "action '" + action.name + "'")) {
                return false;
            }
        }
        for (const auto& entry : numeric_functions_) {
            const auto& name = entry.first;
            const auto& function = entry.second;
            if (!validateTyped(function.params, "numeric function '" + name + "'")) { return false; }
        }
        for (const auto& [name, function] : object_functions_) {
            if (!validateTyped(function.params, "object function '" + name + "'")
                || !knownObjectType(object_result_types_.at(name))) {
                diagnostics.error(ErrorCode::E_TYPE, "unknown object function argument or return type");
                return false;
            }
        }
        if (!numeric_mode_ && (!numeric_functions_.empty() || minimize_cost_)) {
            const auto total = numeric_functions_.find("total-cost");
            if (usesPolicy() || total == numeric_functions_.end() || !total->second.params.empty()) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "action costs require deterministic planning and a nullary (total-cost) function");
                return false;
            }
            if (!requireFeature(":action-costs", "numeric action costs", diagnostics)) { return false; }
        }
        if (!validateTyped(domain_objects_, "domain constants")
            || !validateTyped(problem_objects_, "problem objects")) {
            return false;
        }
        if (uses_typing_ && !featureEnabled(":typing")) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "typed declarations require `:typing` (or `:adl`) in "
                              "`:requirements`");
            return false;
        }

        objects_.clear();
        objects_.insert(objects_.end(), domain_objects_.begin(), domain_objects_.end());
        objects_.insert(objects_.end(), problem_objects_.begin(), problem_objects_.end());
        for (const Typed& object : objects_) {
            if (!object_types_.emplace(object.name, object.type).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate object or constant '" + object.name + "'");
                return false;
            }
        }
        return true;
    }

    bool featureEnabled(const std::string& feature) const {
        if (feature == ":durative-actions" && requirements_.count(":timed-initial-literals")) { return true; }
        if (feature == ":object-fluents") {
            return requirements_.count(":object-fluents") || requirements_.count(":fluents");
        }
        if (feature == ":fluents" || feature == ":numeric-fluents") {
            return requirements_.count(":fluents") || requirements_.count(":numeric-fluents");
        }
        if (requirements_.count(":adl") != 0) {
            static const std::set<std::string> adl = {
                ":strips", ":typing", ":negative-preconditions",
                ":disjunctive-preconditions", ":equality",
                ":existential-preconditions", ":universal-preconditions",
                ":quantified-preconditions", ":conditional-effects",
            };
            if (adl.count(feature) != 0) { return true; }
        }
        if (requirements_.count(":quantified-preconditions") != 0
            && (feature == ":existential-preconditions"
                || feature == ":universal-preconditions")) {
            return true;
        }
        return requirements_.count(feature) != 0;
    }

    /** Is @p construct licensed by the declared `:requirements`?
     *
     *  Strict by default, because a `:requirements` list is part of what a
     *  PDDL/HDDL file MEANS and not a formality: it declares which fragment of
     *  the language the author is writing in, and a planner is entitled to
     *  reject constructs outside it. Accepting them silently would make this
     *  frontend read a file no conforming planner does.
     *
     *  `lenient_requirements=1` relaxes it, because the refusal is otherwise
     *  unmeasurable: four of the eight files in HDDL's own upstream corpus --
     *  IPC test instances -- use `forall`, `not` and conditional effects
     *  without declaring the requirement that licenses them, so the corpus
     *  reports a coverage figure about its own conformance rather than about
     *  this frontend. Relaxing it is how "what would coverage be if these files
     *  were accepted" becomes a number.
     *
     *  Every relaxation is recorded (see `relaxed_features_`), and the
     *  resulting model is NOT claimed to be the one a strict planner reads. */
    bool requireFeature(const std::string& feature, const std::string& construct,
                        Uir::Diagnostics& diagnostics) {
        if (featureEnabled(feature)) { return true; }
        if (lenient_requirements_) {
            if (relaxed_features_.insert(feature).second) {
                diagnostics.warn(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    construct + " requires '" + feature
                        + "' in `:requirements` and the file does not declare it; "
                          "accepted because lenient_requirements is set");
            }
            return true;
        }
        if (missing_features_.insert(feature).second) {
            diagnostics.error(ErrorCode::E_PARSE,
                              construct + " requires '" + feature
                                  + "' (or an implying requirement) in `:requirements`");
        }
        return false;
    }

    bool isSubtype(std::string actual, const std::string& expected) const {
        if (!knownObjectType(actual) || !knownObjectType(expected)) { return false; }
        const auto actual_union = union_types_.find(actual);
        if (actual_union != union_types_.end()) {
            for (const auto& member : actual_union->second) {
                if (!isSubtype(member, expected)) { return false; }
            }
            return true;
        }
        const auto expected_union = union_types_.find(expected);
        if (expected_union != union_types_.end()) {
            for (const auto& member : expected_union->second) {
                if (isSubtype(actual, member)) { return true; }
            }
            return false;
        }
        return PlanningInternal::isSubtype(types_, actual, expected);
    }

    std::vector<std::string> objectsOfType(const std::string& type) const {
        std::vector<std::string> result;
        for (const Typed& object : objects_) {
            if (isSubtype(object.type, type)) { result.push_back(object.name); }
        }
        return result;
    }

    std::string allocateTarget(const std::string& preferred,
                               const std::string& source_identity) {
        const auto existing = target_owners_.find(preferred);
        if (existing == target_owners_.end() || existing->second == source_identity) {
            target_owners_[preferred] = source_identity;
            return preferred;
        }
        std::string candidate = preferred + "__pddl_" + hex(source_identity);
        unsigned suffix = 0;
        while (target_owners_.count(candidate) != 0
               && target_owners_[candidate] != source_identity) {
            candidate = preferred + "__pddl_" + hex(source_identity)
                      + "_" + std::to_string(++suffix);
        }
        target_owners_[candidate] = source_identity;
        return candidate;
    }

    void enumerate(const std::vector<Typed>& variables, std::size_t at,
                   Environment& environment,
                   const std::function<bool(Environment&)>& visit,
                   bool& ok) const {
        if (!ok) { return; }
        if (at == variables.size()) {
            ok = visit(environment);
            return;
        }
        const Typed& variable = variables[at];
        const auto old = environment.find(variable.name);
        const bool had_old = old != environment.end();
        const std::string old_value = had_old ? old->second : std::string{};
        for (const std::string& object : objectsOfType(variable.type)) {
            environment[variable.name] = object;
            enumerate(variables, at + 1, environment, visit, ok);
            if (!ok) { break; }
        }
        if (had_old) { environment[variable.name] = old_value; }
        else { environment.erase(variable.name); }
    }

    void groundAtoms() {
        for (const auto& [name, predicate] : predicates_) {
            std::vector<std::vector<std::string>> tuples{{}};
            for (const Typed& parameter : predicate.params) {
                std::vector<std::vector<std::string>> next;
                for (const auto& tuple : tuples) {
                    for (const std::string& object : objectsOfType(parameter.type)) {
                        auto extended = tuple;
                        extended.push_back(object);
                        next.push_back(std::move(extended));
                    }
                }
                tuples = std::move(next);
            }
            for (const auto& tuple : tuples) {
                const std::string identity = "fluent:" + canonical(name, tuple);
                std::string preferred = name;
                for (const std::string& object : tuple) { preferred += "_" + object; }
                GroundAtom atom{name, tuple, allocateTarget(preferred, identity),
                                sourceCall(name, tuple)};
                atom_targets_.emplace(canonical(name, tuple), atom.target_base);
                atoms_.push_back(std::move(atom));
            }
        }
    }

    using ReachableFacts = std::map<std::string, std::set<std::vector<std::string>>>;
    enum class PartialTruth { FALSE, UNKNOWN, TRUE };

    static void changedPredicates(const Sexp& expression, std::set<std::string>& changed) {
        const auto& head = expression.head();
        if (head.empty() || numericUpdate(head)) { return; }
        if (head == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                changedPredicates(expression.list[i], changed);
            }
        } else if (head == "when" || head == "forall") {
            changedPredicates(expression.list[2], changed);
        } else if (head == "not") { changed.insert(expression.list[1].head()); }
        else { changed.insert(head); }
    }

    // UNKNOWN includes every value a dynamic atom may take. In particular,
    // presence in the relaxed fact set never proves a mutable atom true.
    // Thus negation cannot discard an action enabled by a later delete.
    PartialTruth relaxedCondition(const Sexp& expression, const Environment& environment,
                                  const ReachableFacts& facts,
                                  const std::set<std::string>& changed) const {
        using T = PartialTruth;
        if (expression.list.empty()) { return T::TRUE; }
        const auto& head = expression.head();
        const auto negate = [](T value) {
            return value == T::UNKNOWN ? value : value == T::TRUE ? T::FALSE : T::TRUE;
        };
        if (head == "and" || head == "or") {
            const auto absorbing = head == "and" ? T::FALSE : T::TRUE;
            auto result = head == "and" ? T::TRUE : T::FALSE;
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                const auto value = relaxedCondition(expression.list[i], environment, facts, changed);
                if (value == absorbing) { return value; }
                if (value == T::UNKNOWN) { result = value; }
            }
            return result;
        }
        if (head == "not") {
            return negate(relaxedCondition(expression.list[1], environment, facts, changed));
        }
        if (head == "imply") {
            const auto left = negate(relaxedCondition(expression.list[1], environment, facts, changed));
            const auto right = relaxedCondition(expression.list[2], environment, facts, changed);
            if (left == T::TRUE || right == T::TRUE) { return T::TRUE; }
            return left == T::FALSE && right == T::FALSE ? T::FALSE : T::UNKNOWN;
        }
        // Quantifier scopes are left to the ordinary exact finite expansion.
        if (head == "forall" || head == "exists") { return T::UNKNOWN; }
        std::vector<std::string> args;
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            const auto& name = expression.list[i].atom;
            if (isVariable(name)) {
                const auto value = environment.find(name);
                if (value == environment.end()) { return T::UNKNOWN; }
                args.push_back(value->second);
            } else { args.push_back(name); }
        }
        if (numeric_mode_ && numericComparison(expression)) { return T::UNKNOWN; }
        if (head == "=") { return args[0] == args[1] ? T::TRUE : T::FALSE; }
        const auto relation = facts.find(head);
        if (relation == facts.end() || !relation->second.count(args)) { return T::FALSE; }
        return changed.count(head) ? T::UNKNOWN : T::TRUE;
    }

    static void positiveConjuncts(const Sexp& expression, std::vector<const Sexp*>& result) {
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                positiveConjuncts(expression.list[i], result);
            }
        } else if (!expression.list.empty()) {
            const auto& head = expression.head();
            if (head != "not" && head != "or" && head != "imply" && head != "="
                && head != "forall" && head != "exists" && head != "<" && head != "<="
                && head != ">" && head != ">=") { result.push_back(&expression); }
        }
    }

    bool collectEffectFacts(const Sexp& expression, Environment& environment,
                            ReachableFacts& facts, Uir::Diagnostics& diagnostics,
                            bool include_deletes = false) {
        const auto& head = expression.head();
        if (head.empty() || numericUpdate(head)) { return true; }
        if (head == "not") {
            return !include_deletes || collectEffectFacts(expression.list[1], environment,
                                                          facts, diagnostics, include_deletes);
        }
        if (head == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!collectEffectFacts(expression.list[i], environment, facts, diagnostics, include_deletes)) { return false; }
            }
            return true;
        }
        // Ignoring a conditional guard can only add possible facts. The
        // original guarded effect is still emitted in the transition relation.
        if (head == "when") { return collectEffectFacts(expression.list[2], environment, facts, diagnostics, include_deletes); }
        if (head == "forall") {
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "effect binder", variables, diagnostics)) { return false; }
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                return collectEffectFacts(expression.list[2], bound, facts, diagnostics, include_deletes);
            }, ok);
            return ok;
        }
        std::vector<std::string> args;
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            const auto value = resolveTerm(expression.list[i], environment, diagnostics);
            if (!value) { return false; }
            args.push_back(*value);
        }
        facts[head].insert(std::move(args));
        return true;
    }

    void addGroundAction(const Action& action, const std::vector<std::string>& tuple,
                         unsigned earliest_step = 0) {
        const std::string identity = "action:" + canonical(action.name, tuple);
        std::string preferred = "do_" + action.name;
        for (const std::string& object : tuple) { preferred += "_" + object; }
        ground_actions_.push_back({&action, tuple, allocateTarget(preferred, identity),
                                   sourceCall(action.name, tuple), earliest_step});
    }

    // Each layer overapproximates the facts reachable after that many source
    // actions: retain old facts, ignore deletes, and include all conditional
    // adds of every potentially applicable action. Join mandatory positive
    // preconditions against this sparse relation before enumerating free
    // parameters. Every actual bounded plan is therefore still represented.
    bool groundReachableActions(Uir::Diagnostics& diagnostics) {
        ReachableFacts facts;
        for (const auto& literal : init_) {
            if (literal.head() == "not") { continue; }
            std::vector<std::string> args;
            for (std::size_t i = 1; i < literal.list.size(); ++i) { args.push_back(literal.list[i].atom); }
            facts[literal.head()].insert(std::move(args));
        }
        std::set<std::string> changed, emitted;
        for (const auto& action : actions_) {
            if (action.has_effect) { changedPredicates(action.effect, changed); }
        }
        for (unsigned layer = 0; layer < horizon_; ++layer) {
            ReachableFacts additions;
            using Tuple = std::vector<std::string>;
            using Rows = std::vector<const Tuple*>;
            using Index = std::map<Tuple, Rows>;
            std::map<std::pair<std::string, std::vector<std::size_t>>, Index> indexes;
            const Rows empty_rows;
            // Facts stay immutable within a layer. Rebuild these indexes at
            // the next layer so newly reachable tuples cannot be missed.
            const auto candidates = [&](const Sexp& expression, const Environment& environment) -> const Rows& {
                const auto relation = facts.find(expression.head());
                if (relation == facts.end()) { return empty_rows; }
                std::vector<std::size_t> positions;
                Tuple values;
                for (std::size_t i = 1; i < expression.list.size(); ++i) {
                    const auto& term = expression.list[i].atom;
                    if (!isVariable(term)) {
                        positions.push_back(i - 1); values.push_back(term);
                    } else {
                        const auto bound = environment.find(term);
                        if (bound != environment.end()) {
                            positions.push_back(i - 1); values.push_back(bound->second);
                        }
                    }
                }
                auto inserted = indexes.try_emplace(std::make_pair(expression.head(), positions));
                auto& index = inserted.first->second;
                if (inserted.second) {
                    for (const auto& tuple : relation->second) {
                        Tuple key;
                        for (const auto position : positions) { key.push_back(tuple[position]); }
                        index[std::move(key)].push_back(&tuple);
                    }
                }
                const auto found = index.find(values);
                return found == index.end() ? empty_rows : found->second;
            };
            for (const auto& action : actions_) {
                std::vector<const Sexp*> joins;
                if (action.has_precondition) { positiveConjuncts(action.precondition, joins); }
                std::map<std::string, std::string> parameter_types;
                std::vector<std::vector<std::string>> domains;
                for (const auto& parameter : action.params) {
                    parameter_types.emplace(parameter.name, parameter.type);
                    domains.push_back(objectsOfType(parameter.type));
                }
                const auto possible = [&](const Environment& environment) {
                    return !action.has_precondition
                        || relaxedCondition(action.precondition, environment, facts, changed) != PartialTruth::FALSE;
                };
                std::function<bool(std::size_t, Environment&)> complete;
                complete = [&](std::size_t at, Environment& environment) {
                    if (!possible(environment)) { return true; }
                    if (at == action.params.size()) {
                        std::vector<std::string> tuple;
                        for (const auto& parameter : action.params) { tuple.push_back(environment.at(parameter.name)); }
                        if (!emitted.insert(canonical(action.name, tuple)).second) { return true; }
                        addGroundAction(action, tuple, layer);
                        return !action.has_effect || collectEffectFacts(action.effect, environment, additions, diagnostics);
                    }
                    const auto& name = action.params[at].name;
                    if (environment.count(name)) { return complete(at + 1, environment); }
                    for (const auto& object : domains[at]) {
                        environment[name] = object;
                        if (!complete(at + 1, environment)) { return false; }
                    }
                    environment.erase(name);
                    return true;
                };
                std::vector<bool> joined(joins.size(), false);
                std::function<bool(std::size_t, const Environment&)> join;
                join = [&](std::size_t at, const Environment& environment) {
                    if (!possible(environment)) { return true; }
                    if (at == joins.size()) {
                        auto bound = environment;
                        return complete(0, bound);
                    }
                    // Choose using the current bindings, not just the raw
                    // relation sizes. This avoids multiplying independent
                    // unary relations before visiting a connecting relation.
                    std::size_t selected = joins.size();
                    const Rows* rows = nullptr;
                    for (std::size_t i = 0; i < joins.size(); ++i) {
                        if (joined[i]) { continue; }
                        const auto& matches = candidates(*joins[i], environment);
                        if (matches.empty()) { return true; }
                        if (!rows || matches.size() < rows->size()) { selected = i; rows = &matches; }
                    }
                    const auto& expression = *joins[selected];
                    joined[selected] = true;
                    for (const auto* candidate : *rows) {
                        const auto& tuple = *candidate;
                        auto bound = environment;
                        bool matches = true;
                        for (std::size_t i = 0; i < tuple.size(); ++i) {
                            const auto& term = expression.list[i + 1].atom;
                            if (isVariable(term)) {
                                if (!isSubtype(object_types_.at(tuple[i]), parameter_types.at(term))) {
                                    matches = false; break;
                                }
                                const auto entry = bound.emplace(term, tuple[i]);
                                if (entry.first->second != tuple[i]) { matches = false; break; }
                            } else if (term != tuple[i]) { matches = false; break; }
                        }
                        if (matches && !join(at + 1, bound)) {
                            joined[selected] = false;
                            return false;
                        }
                    }
                    joined[selected] = false;
                    return true;
                };
                if (!join(0, {})) { return false; }
            }
            bool grew = false;
            for (auto& [predicate, tuples] : additions) {
                for (const auto& tuple : tuples) { grew |= facts[predicate].insert(tuple).second; }
            }
            if (!grew) { break; }
        }
        return true;
    }

    bool groundChangedAtoms(Uir::Diagnostics& diagnostics) {
        ReachableFacts changed;
        for (const auto& action : ground_actions_) {
            if (!action.schema->has_effect) { continue; }
            auto environment = actionEnvironment(action);
            if (!collectEffectFacts(action.schema->effect, environment, changed, diagnostics, true)) {
                return false;
            }
        }
        // Every add/delete target of every retained action is represented,
        // even under a false guard. All other tuples keep their initial value.
        for (const auto& [name, tuples] : changed) {
            for (const auto& tuple : tuples) {
                const auto key = canonical(name, tuple);
                std::string preferred = name;
                for (const auto& object : tuple) { preferred += "_" + object; }
                GroundAtom atom{name, tuple, allocateTarget(preferred, "fluent:" + key),
                                sourceCall(name, tuple)};
                atom_targets_.emplace(key, atom.target_base);
                atoms_.push_back(std::move(atom));
            }
        }
        return true;
    }

    void groundActions() {
        for (const Action& action : actions_) {
            if (allowed_actions_) {
                const auto found = allowed_actions_->find(action.name);
                if (found == allowed_actions_->end()) { continue; }
                for (const auto& tuple : found->second) { addGroundAction(action, tuple); }
            } else {
                Environment environment;
                bool ok = true;
                enumerate(action.params, 0, environment, [&](Environment& bound) {
                    std::vector<std::string> tuple;
                    for (const auto& parameter : action.params) { tuple.push_back(bound.at(parameter.name)); }
                    addGroundAction(action, tuple);
                    return true;
                }, ok);
            }
        }
    }

    Environment actionEnvironment(const GroundAction& action) const {
        Environment result;
        for (std::size_t i = 0; i < action.schema->params.size(); ++i) {
            result.emplace(action.schema->params[i].name, action.args[i]);
        }
        return result;
    }

    std::optional<std::string> resolveTerm(const Sexp& term,
                                           const Environment& environment,
                                           Uir::Diagnostics& diagnostics) const {
        if (!term.isAtom()) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "functional/object-valued PDDL terms are not implemented");
            return std::nullopt;
        }
        if (!term.atom.empty() && term.atom[0] == '?') {
            const auto found = environment.find(term.atom);
            if (found == environment.end()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "unbound PDDL variable '" + term.atom + "'");
                return std::nullopt;
            }
            return found->second;
        }
        if (object_types_.count(term.atom) == 0) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "unknown PDDL object or constant '" + term.atom + "'");
            return std::nullopt;
        }
        return term.atom;
    }

    std::optional<std::string> atomBase(const Sexp& expression,
                                        const Environment& environment,
                                        Uir::Diagnostics& diagnostics,
                                        bool source_key = false) const {
        if (expression.list.empty() || !expression.list[0].isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed PDDL atom");
            return std::nullopt;
        }
        const std::string& name = expression.list[0].atom;
        const auto predicate = predicates_.find(name);
        if (predicate == predicates_.end()) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "'" + name + "' is not a declared predicate");
            return std::nullopt;
        }
        if (expression.list.size() != predicate->second.params.size() + 1) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "predicate '" + name + "' expects "
                                  + std::to_string(predicate->second.params.size())
                                  + " arguments, not "
                                  + std::to_string(expression.list.size() - 1));
            return std::nullopt;
        }
        std::vector<std::string> args;
        for (std::size_t i = 0; i < predicate->second.params.size(); ++i) {
            const auto object = resolveTerm(expression.list[i + 1], environment,
                                            diagnostics);
            if (!object) { return std::nullopt; }
            const std::string& actual_type = object_types_.at(*object);
            const std::string& expected_type = predicate->second.params[i].type;
            if (!isSubtype(actual_type, expected_type)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "object '" + *object + "' of type '" + actual_type
                                      + "' is not admissible for argument "
                                      + std::to_string(i + 1) + " of predicate '" + name
                                      + "' (expected '" + expected_type + "')");
                return std::nullopt;
            }
            args.push_back(*object);
        }
        const auto key = canonical(name, args);
        if (source_key) { return key; }
        const auto target = atom_targets_.find(key);
        if (target == atom_targets_.end()) {
            if (sparse_fluents_) { return STATIC_ATOM_PREFIX + key; }
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "ground atom has no target symbol");
            return std::nullopt;
        }
        return target->second;
    }

    H::ExprPtr formula(const Sexp& expression, Environment& environment,
                       unsigned step, Uir::Diagnostics& diagnostics) {
        if (numeric_mode_) {
            auto condition = numericCondition(expression, environment, step, diagnostics);
            return condition ? P::numericSatisfied(*condition) : nullptr;
        }
        if (expression.isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "a PDDL formula must be parenthesized");
            return nullptr;
        }
        if (expression.list.empty()) { return H::mkBool(true); }
        const std::string head = expression.head();
        if (head == "and" || head == "or") {
            if (head == "or"
                && !requireFeature(":disjunctive-preconditions", "`or`",
                                   diagnostics)) {
                return nullptr;
            }
            std::vector<H::ExprPtr> terms;
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                H::ExprPtr term = formula(expression.list[i], environment, step,
                                          diagnostics);
                if (!term) { return nullptr; }
                // Static tuples and object equalities are already resolved.
                // Skip a dominated subtree only after every source schema
                // was checked; dynamic fluents never become constants here.
                if (static_conditions_validated_ && term->kind == H::ExprKind::LIT_BOOL
                    && term->bool_value == (head == "or")) { return term; }
                terms.push_back(std::move(term));
            }
            return head == "and" ? conjunction(std::move(terms))
                                 : disjunction(std::move(terms));
        }
        if (head == "not") {
            if (expression.list.size() != 2) {
                diagnostics.error(ErrorCode::E_PARSE, "`not` takes one formula");
                return nullptr;
            }
            const bool atomic = !expression.list[1].list.empty()
                             && expression.list[1].head() != "and"
                             && expression.list[1].head() != "or"
                             && expression.list[1].head() != "not"
                             && expression.list[1].head() != "imply"
                             && expression.list[1].head() != "forall"
                             && expression.list[1].head() != "exists";
            const std::string feature = atomic ? ":negative-preconditions"
                                               : ":disjunctive-preconditions";
            if (!requireFeature(feature, "`not` condition", diagnostics)) {
                return nullptr;
            }
            H::ExprPtr term = formula(expression.list[1], environment, step,
                                      diagnostics);
            return term ? negation(term) : nullptr;
        }
        if (head == "imply") {
            if (expression.list.size() != 3
                || !requireFeature(":disjunctive-preconditions", "`imply`",
                                   diagnostics)) {
                return nullptr;
            }
            H::ExprPtr lhs = formula(expression.list[1], environment, step,
                                     diagnostics);
            if (!lhs) { return nullptr; }
            if (static_conditions_validated_ && lhs->kind == H::ExprKind::LIT_BOOL
                && !lhs->bool_value) { return H::mkBool(true); }
            H::ExprPtr rhs = formula(expression.list[2], environment, step,
                                     diagnostics);
            return rhs ? disjunction({negation(lhs), rhs}) : nullptr;
        }
        if (head == "forall" || head == "exists") {
            if (expression.list.size() != 3 || expression.list[1].isAtom()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed PDDL quantifier");
                return nullptr;
            }
            const std::string feature = head == "forall"
                                            ? ":universal-preconditions"
                                            : ":existential-preconditions";
            if (!requireFeature(feature, "`" + head + "`", diagnostics)) {
                return nullptr;
            }
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "`" + head + "` binder",
                           variables, diagnostics)) {
                return nullptr;
            }
            for (const Typed& variable : variables) {
                if (!knownObjectType(variable.type)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "quantifier uses unknown type '" + variable.type + "'");
                    return nullptr;
                }
            }
            std::vector<H::ExprPtr> instances;
            bool ok = true;
            enumerate(variables, 0, environment,
                      [&](Environment& bound) {
                          H::ExprPtr instance = formula(expression.list[2], bound, step,
                                                        diagnostics);
                          if (!instance) { return false; }
                          instances.push_back(std::move(instance));
                          return true;
                      },
                      ok);
            if (!ok) { return nullptr; }
            return head == "forall" ? conjunction(std::move(instances))
                                     : disjunction(std::move(instances));
        }
        if (head == "=") {
            if (expression.list.size() != 3
                || !requireFeature(":equality", "object equality", diagnostics)) {
                return nullptr;
            }
            const auto lhs = resolveTerm(expression.list[1], environment, diagnostics);
            const auto rhs = resolveTerm(expression.list[2], environment, diagnostics);
            return lhs && rhs ? H::mkBool(*lhs == *rhs) : nullptr;
        }
        if (head == "when") {
            diagnostics.error(ErrorCode::E_PARSE,
                              "`when` is an effect form, not a condition");
            return nullptr;
        }
        const auto base = atomBase(expression, environment, diagnostics);
        if (base && base->compare(0, sizeof(STATIC_ATOM_PREFIX) - 1, STATIC_ATOM_PREFIX) == 0) {
            return H::mkBool(static_initial_.count(base->substr(sizeof(STATIC_ATOM_PREFIX) - 1)) != 0);
        }
        return base ? atomAt(*base, step) : nullptr;
    }

    static bool numericUpdate(const std::string& head) {
        return head == "assign" || head == "increase" || head == "decrease"
            || head == "scale-up" || head == "scale-down";
    }

    static bool decimalNumber(const Sexp& expression) {
        if (!expression.isAtom() || expression.atom.empty()) { return false; }
        const auto& text = expression.atom;
        std::size_t start = text.front() == '-' || text.front() == '+' ? 1 : 0;
        if (start == text.size() || !std::isdigit(static_cast<unsigned char>(text[start]))
            || !std::isdigit(static_cast<unsigned char>(text.back()))) { return false; }
        bool dot = false;
        for (std::size_t i = start; i < text.size(); ++i) {
            if (text[i] == '.' && !dot) { dot = true; }
            else if (!std::isdigit(static_cast<unsigned char>(text[i]))) { return false; }
        }
        return true;
    }

    bool numericComparison(const Sexp& expression) const {
        const auto& head = expression.head();
        if (head == "<" || head == "<=" || head == ">" || head == ">=") { return true; }
        if (head == "=" && expression.list.size() == 3
            && (expression.list[1].atom == "?duration" || expression.list[2].atom == "?duration")) { return true; }
        const auto numeric = [&](const Sexp& term) {
            if (decimalNumber(term)) { return true; }
            const auto& name = term.isAtom() ? term.atom : term.head();
            return numeric_functions_.count(name) || name == "+" || name == "-"
                || name == "*" || name == "/" || name == "total-time";
        };
        return head == "=" && expression.list.size() == 3
            && (numeric(expression.list[1]) || numeric(expression.list[2]));
    }

    bool validateNumeric(const Sexp& expression, const Environment& types,
                         Uir::Diagnostics& diagnostics) const {
        if (expression.isAtom()) {
            if ((expression.atom == "?duration" && temporal_duration_allowed_)
                || (expression.atom == "total-time" && temporal_metric_allowed_)) { return true; }
            if (decimalNumber(expression)) { return true; }
            if (object_mode_ && numeric_functions_.count(expression.atom)
                && numeric_functions_.at(expression.atom).params.empty()) { return true; }
            diagnostics.error(ErrorCode::E_TYPE, "numeric term requires an exact decimal or function application");
            return false;
        }
        const auto& head = expression.head();
        if (head == "+" || head == "-" || head == "*" || head == "/") {
            const bool metric_multi = (preference_metric_allowed_ || temporal_metric_allowed_)
                && (head == "+" || head == "*") && expression.list.size() >= 3;
            const bool arity = metric_multi || expression.list.size() == 3 || (head == "-" && expression.list.size() == 2);
            if (!arity) {
                diagnostics.error(ErrorCode::E_PARSE, "PDDL numeric arithmetic requires two operands (one for unary minus)");
                return false;
            }
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!validateNumeric(expression.list[i], types, diagnostics)) { return false; }
            }
            return true;
        }
        if (head == "is-violated") {
            if (!preference_metric_allowed_ || expression.list.size() != 2
                || !expression.list[1].isAtom() || !preference_names_.count(expression.list[1].atom)) {
                diagnostics.error(ErrorCode::E_PARSE,
                    "is-violated is a metric-only term referring to a declared named preference"); return false;
            }
            return true;
        }
        return validateApplication(expression, types, numeric_functions_, diagnostics);
    }

    P::NumericStateCell numericAt(std::size_t index, unsigned step) const {
        const std::string base = numeric_ground_.at(index).target + "@" + std::to_string(step);
        return {H::mkIdent(base, H::Sort::real()), H::mkIdent(base + "@defined", H::Sort::boolean())};
    }

    std::optional<P::NumericValue> numericExpression(const Sexp& expression,
        const Environment& environment, unsigned step, Uir::Diagnostics& diagnostics) {
        if (expression.isAtom()) {
            if (expression.atom == "?duration" && temporal_duration_) {
                return P::NumericValue{temporal_duration_, H::mkBool(true), {}};
            }
            if (expression.atom == "total-time" && temporal_metric_allowed_ && temporal_total_time_) {
                return P::NumericValue{temporal_total_time_, H::mkBool(true), {}};
            }
            if (object_mode_ && numeric_functions_.count(expression.atom)
                && numeric_functions_.at(expression.atom).params.empty()) {
                return numericExpression(functionApplication(expression), environment, step, diagnostics);
            }
            if (!decimalNumber(expression)) {
                diagnostics.error(ErrorCode::E_TYPE, "invalid exact PDDL number");
                return std::nullopt;
            }
            const auto exact = expression.atom.front() == '+' ? expression.atom.substr(1) : expression.atom;
            return P::numericConstant(exact, diagnostics);
        }
        const auto& head = expression.head();
        if (head == "+" || head == "-" || head == "*" || head == "/") {
            std::vector<P::NumericValue> args;
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                auto arg = numericExpression(expression.list[i], environment, step, diagnostics);
                if (!arg) { return std::nullopt; }
                args.push_back(*arg);
            }
            const auto op = head == "+" ? H::Op::ADD : head == "*" ? H::Op::MUL
                : head == "/" ? H::Op::DIV_REAL : args.size() == 1 ? H::Op::NEG : H::Op::SUB;
            return P::numericArithmetic(op, args, diagnostics);
        }
        if (head == "is-violated") {
            if (!preference_metric_allowed_ || expression.list.size() != 2 || !expression.list[1].isAtom()) {
                diagnostics.error(ErrorCode::E_PARSE, "is-violated is valid only in the plan metric"); return std::nullopt;
            }
            const auto count = preference_counts_.named_violations.find(expression.list[1].atom);
            if (count == preference_counts_.named_violations.end()) {
                diagnostics.error(ErrorCode::E_TYPE, "metric refers to an undeclared preference"); return std::nullopt;
            }
            return P::NumericValue{H::mkOp(H::Op::TO_REAL, {count->second}), H::mkBool(true), {}};
        }
        if (object_mode_) {
            const auto declaration = numeric_functions_.find(expression.head());
            if (declaration == numeric_functions_.end()) {
                diagnostics.error(ErrorCode::E_TYPE, "undeclared numeric function");
                return std::nullopt;
            }
            const auto arguments = objectArguments(expression, environment, step, diagnostics);
            if (!arguments) { return std::nullopt; }
            const auto& table = objectTable("numeric", expression.head(), declaration->second);
            std::vector<P::NumericValue> values;
            for (const auto& row : table.rows) {
                const auto index = numeric_indices_.at(objectRowKey(expression.head(), row));
                const auto value = P::numericRead(numericAt(index, step), index, diagnostics);
                if (!value) { return std::nullopt; }
                values.push_back(*value);
            }
            const auto value = P::objectNumericLookup(*object_context_, object_universe_, table, *arguments, values, diagnostics);
            if (!value) { return std::nullopt; }
            objectObligations(value->constraints);
            return value->numeric;
        }
        const auto key = numericKey(expression, environment, diagnostics);
        if (!key) { return std::nullopt; }
        if (!numeric_mode_) {
            if (expression.head() == "total-cost" && !cost_target_.empty()) {
                return P::NumericValue{costAt(step), H::mkBool(true), {}};
            }
            const auto value = numeric_initial_.find(*key);
            if (value == numeric_initial_.end()) {
                diagnostics.error(ErrorCode::E_TYPE, "static numeric metric term is uninitialized"); return std::nullopt;
            }
            return P::NumericValue{value->second, H::mkBool(true), {}};
        }
        const auto found = numeric_indices_.find(*key);
        if (found == numeric_indices_.end()) {
            diagnostics.error(ErrorCode::E_INTERNAL, "numeric application omitted from finite grounding");
            return std::nullopt;
        }
        return P::numericRead(numericAt(found->second, step), found->second, diagnostics);
    }

    std::optional<P::NumericCondition> numericCondition(const Sexp& expression,
        Environment& environment, unsigned step, Uir::Diagnostics& diagnostics) {
        if (expression.isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE, "a PDDL condition must be parenthesized");
            return std::nullopt;
        }
        const auto& head = expression.head();
        if (expression.list.empty()) { return P::numericPredicate(H::mkBool(true), diagnostics); }
        if (head == "and" || head == "or" || head == "not" || head == "imply") {
            std::vector<P::NumericCondition> args;
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                auto term = numericCondition(expression.list[i], environment, step, diagnostics);
                if (!term) { return std::nullopt; }
                args.push_back(*term);
            }
            return P::numericLogical(head == "and" ? H::Op::AND : head == "or" ? H::Op::OR
                : head == "not" ? H::Op::NOT : H::Op::IMPLIES, args, diagnostics);
        }
        if (head == "forall" || head == "exists") {
            std::vector<Typed> variables;
            if (expression.list.size() != 3 || !typedList(expression.list[1], 0, true,
                    "numeric condition quantifier", variables, diagnostics)) { return std::nullopt; }
            std::vector<P::NumericCondition> instances;
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                auto term = numericCondition(expression.list[2], bound, step, diagnostics);
                if (!term) { return false; }
                instances.push_back(*term);
                return true;
            }, ok);
            if (!ok) { return std::nullopt; }
            return P::numericLogical(head == "forall" ? H::Op::AND : H::Op::OR, instances, diagnostics);
        }
        if (numericComparison(expression)) {
            if (expression.list.size() != 3) {
                diagnostics.error(ErrorCode::E_PARSE, "numeric comparison requires two operands");
                return std::nullopt;
            }
            auto lhs = numericExpression(expression.list[1], environment, step, diagnostics);
            auto rhs = numericExpression(expression.list[2], environment, step, diagnostics);
            if (!lhs || !rhs) { return std::nullopt; }
            const auto op = head == "=" ? H::Op::EQ : head == "<" ? H::Op::LT
                : head == "<=" ? H::Op::LE : head == ">" ? H::Op::GT : H::Op::GE;
            return P::numericCompare(op, *lhs, *rhs, diagnostics);
        }
        if (head == "=") {
            if (expression.list.size() != 3) { return std::nullopt; }
            if (object_mode_) {
                auto lhs = objectTerm(expression.list[1], environment, step, diagnostics);
                auto rhs = objectTerm(expression.list[2], environment, step, diagnostics);
                if (!lhs || !rhs) { return std::nullopt; }
                auto result = P::objectEqual(object_universe_, *lhs, *rhs, P::ObjectUndefinedPolicy::STRICT, diagnostics);
                if (!result) { return std::nullopt; }
                objectObligations(result->constraints);
                return P::NumericCondition{result->value, result->defined, {}};
            }
            auto lhs = resolveTerm(expression.list[1], environment, diagnostics);
            auto rhs = resolveTerm(expression.list[2], environment, diagnostics);
            return lhs && rhs ? P::numericPredicate(H::mkBool(*lhs == *rhs), diagnostics) : std::nullopt;
        }
        if (object_mode_) { return objectPredicateCondition(expression, environment, step, diagnostics); }
        auto base = atomBase(expression, environment, diagnostics);
        if (!base) { return std::nullopt; }
        const bool fixed = base->compare(0, sizeof(STATIC_ATOM_PREFIX)-1, STATIC_ATOM_PREFIX) == 0;
        auto predicate = fixed ? H::mkBool(static_initial_.count(base->substr(sizeof(STATIC_ATOM_PREFIX)-1)) != 0)
            : atomAt(*base, step);
        return P::numericPredicate(predicate, diagnostics);
    }

    P::ObjectType objectApiType(const std::string& type) const {
        const auto found = union_types_.find(type);
        if (found == union_types_.end()) { return {{type}}; }
        return {std::vector<std::string>(found->second.begin(), found->second.end())};
    }

    static Sexp functionApplication(const Sexp& expression) {
        return expression.isAtom() ? Sexp{"", {expression}} : expression;
    }

    P::ObjectStateCell objectAt(std::size_t index, unsigned step) const {
        const auto& ground = object_ground_.at(index);
        const auto base = ground.target + "@" + std::to_string(step);
        return {H::mkIdent(base, H::Sort::integer()),
                H::mkIdent(base + "@defined", H::Sort::boolean()), objectApiType(ground.type)};
    }

    void objectObligations(const std::vector<H::ExprPtr>& constraints) {
        for (const auto& constraint : constraints) {
            if (object_obligation_seen_.insert(constraint.get()).second) { add(*object_context_, constraint); }
        }
    }

    const P::ObjectTable& objectTable(const std::string& category, const std::string& name,
                                     const Predicate& declaration) {
        const auto key = category + ":" + name;
        const auto prior = object_tables_.find(key);
        if (prior != object_tables_.end()) { return prior->second; }
        P::ObjectTable table;
        for (const auto& parameter : declaration.params) { table.parameters.push_back(objectApiType(parameter.type)); }
        Environment environment;
        bool ok = true;
        enumerate(declaration.params, 0, environment, [&](Environment& bound) {
            std::vector<std::size_t> row;
            for (const auto& parameter : declaration.params) { row.push_back(object_name_indices_.at(bound.at(parameter.name))); }
            table.rows.push_back(std::move(row));
            return true;
        }, ok);
        return object_tables_.emplace(key, std::move(table)).first->second;
    }

    std::string objectRowKey(const std::string& name, const std::vector<std::size_t>& row) const {
        std::vector<std::string> arguments;
        for (const auto index : row) { arguments.push_back(object_universe_.objects.at(index).name); }
        return canonical(name, arguments);
    }

    std::optional<std::vector<P::ObjectValue>> objectArguments(const Sexp& expression,
        const Environment& environment, unsigned step, Uir::Diagnostics& diagnostics) {
        std::vector<P::ObjectValue> arguments;
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            auto term = objectTerm(expression.list[i], environment, step, diagnostics);
            if (!term) { return std::nullopt; }
            arguments.push_back(std::move(*term));
        }
        return arguments;
    }

    std::optional<P::ObjectValue> objectTerm(const Sexp& expression,
        const Environment& environment, unsigned step, Uir::Diagnostics& diagnostics) {
        if (expression.isAtom()) {
            const auto name = resolveTerm(expression, environment, diagnostics);
            return name ? P::objectConstant(object_universe_, *name, diagnostics) : std::nullopt;
        }
        const auto found = object_functions_.find(expression.head());
        if (found == object_functions_.end() || expression.list.size() != found->second.params.size() + 1) {
            diagnostics.error(ErrorCode::E_TYPE, "undeclared or wrong-arity object function term");
            return std::nullopt;
        }
        const auto arguments = objectArguments(expression, environment, step, diagnostics);
        if (!arguments) { return std::nullopt; }
        const auto& table = objectTable("object", expression.head(), found->second);
        std::vector<P::ObjectValue> values;
        for (const auto& row : table.rows) {
            const auto index = object_indices_.at(objectRowKey(expression.head(), row));
            auto value = P::objectRead(object_universe_, objectAt(index, step), index, diagnostics);
            if (!value) { return std::nullopt; }
            values.push_back(std::move(*value));
        }
        auto result = P::objectLookup(*object_context_, object_universe_, table, *arguments,
            values, objectApiType(object_result_types_.at(expression.head())), diagnostics);
        if (result) { objectObligations(result->constraints); }
        return result;
    }

    std::optional<P::ObjectDispatch> objectDispatchFor(const Sexp& expression,
        const Predicate& declaration, const std::string& category,
        const Environment& environment, unsigned step, Uir::Diagnostics& diagnostics) {
        if (expression.list.size() != declaration.params.size() + 1) {
            diagnostics.error(ErrorCode::E_TYPE, "wrong-arity dynamic object application");
            return std::nullopt;
        }
        const auto arguments = objectArguments(expression, environment, step, diagnostics);
        if (!arguments) { return std::nullopt; }
        auto result = P::objectDispatch(*object_context_, object_universe_,
            objectTable(category, expression.head(), declaration), *arguments, diagnostics);
        if (result) { objectObligations(result->constraints); }
        return result;
    }

    std::optional<P::NumericCondition> objectPredicateCondition(const Sexp& expression,
        const Environment& environment, unsigned step, Uir::Diagnostics& diagnostics) {
        const auto found = predicates_.find(expression.head());
        if (found == predicates_.end()) {
            diagnostics.error(ErrorCode::E_TYPE, "undeclared predicate in object-valued condition");
            return std::nullopt;
        }
        const auto arguments = objectArguments(expression, environment, step, diagnostics);
        if (!arguments) { return std::nullopt; }
        const auto& table = objectTable("predicate", expression.head(), found->second);
        std::vector<H::ExprPtr> values;
        for (const auto& row : table.rows) { values.push_back(atomAt(atom_targets_.at(objectRowKey(expression.head(), row)), step)); }
        const auto result = P::objectPredicate(*object_context_, object_universe_, table,
            *arguments, values, P::ObjectUndefinedPolicy::STRICT, diagnostics);
        if (!result) { return std::nullopt; }
        objectObligations(result->constraints);
        return P::NumericCondition{result->value, result->defined, {}};
    }

    bool objectPredicateEffect(const Sexp& expression, const Environment& environment,
        unsigned step, H::ExprPtr guard, bool positive,
        std::map<std::string, FluentUpdates>& updates, Uir::Diagnostics& diagnostics) {
        const auto found = predicates_.find(expression.head());
        if (found == predicates_.end() || derived_predicates_.count(expression.head())) {
            diagnostics.error(ErrorCode::E_TYPE, "object-addressed effect requires a declared basic predicate");
            return false;
        }
        const auto dispatch = objectDispatchFor(expression, found->second, "predicate", environment, step, diagnostics);
        if (!dispatch) { return false; }
        pending_numeric_conditions_.push_back(H::mkOp(H::Op::IMPLIES, {guard, dispatch->defined}));
        const auto& table = objectTable("predicate", expression.head(), found->second);
        for (std::size_t i = 0; i < table.rows.size(); ++i) {
            const auto& base = atom_targets_.at(objectRowKey(expression.head(), table.rows[i]));
            auto& update = updates[base];
            auto& terms = positive ? update.add_conditions : update.delete_conditions;
            terms.push_back(conjunction({guard, dispatch->matches[i]}));
        }
        return true;
    }

    bool objectAssignment(const Sexp& expression, const Environment& environment,
        unsigned step, H::ExprPtr guard, Uir::Diagnostics& diagnostics) {
        const auto& target = expression.list[1];
        const auto& declaration = object_functions_.at(target.head());
        const auto arguments = objectArguments(target, environment, step, diagnostics);
        if (!arguments) { return false; }
        const auto& table = objectTable("object", target.head(), declaration);
        std::vector<std::size_t> cells;
        for (const auto& row : table.rows) { cells.push_back(object_indices_.at(objectRowKey(target.head(), row))); }
        auto address = P::objectAddress(*object_context_, object_universe_, table, *arguments, cells, diagnostics);
        if (!address) { return false; }
        std::optional<P::ObjectValue> rhs;
        if (!(expression.list[2].isAtom() && expression.list[2].atom == "undefined")) {
            rhs = objectTerm(expression.list[2], environment, step, diagnostics);
            if (!rhs) { return false; }
        }
        pending_objects_.push_back({std::move(*address), std::move(rhs), std::move(guard)});
        return true;
    }

    bool initializeObjects(Uir::Diagnostics& diagnostics) {
        if (!object_mode_) { return true; }
        for (const auto& [name, parents] : types_) {
            if (name != "object") { object_universe_.types.push_back({name, std::vector<std::string>(parents.begin(), parents.end())}); }
        }
        for (const auto& object : objects_) {
            object_name_indices_.emplace(object.name, object_universe_.objects.size());
            object_universe_.objects.push_back({object.name, object.type});
        }
        if (!P::validateObjectUniverse(object_universe_, diagnostics)) { return false; }
        for (const auto& [name, declaration] : object_functions_) {
            const auto& table = objectTable("object", name, declaration);
            for (const auto& row : table.rows) {
                const auto key = objectRowKey(name, row);
                std::vector<std::string> args;
                for (const auto index : row) { args.push_back(object_universe_.objects[index].name); }
                const auto target = allocateTarget("__pddl_object_" + std::to_string(object_ground_.size()), "object:" + key);
                object_indices_.emplace(key, object_ground_.size());
                object_ground_.push_back({key, target, sourceCall(name, args), object_result_types_.at(name)});
            }
        }
        std::vector<Sexp> remaining;
        std::set<std::size_t> assigned;
        for (const auto& literal : init_) {
            if (literal.head() != "=" || literal.list.size() < 2) { remaining.push_back(literal); continue; }
            const auto application = functionApplication(literal.list[1]);
            const auto declaration = object_functions_.find(application.head());
            if (declaration == object_functions_.end()) { remaining.push_back(literal); continue; }
            if (literal.list.size() != 3 || !literal.list[2].isAtom()
                || !validateApplication(application, {}, object_functions_, diagnostics)) {
                diagnostics.error(ErrorCode::E_TYPE, "object initialization requires a basic ground function and one object name");
                return false;
            }
            std::vector<std::string> arguments;
            for (std::size_t i = 1; i < application.list.size(); ++i) {
                const auto object = resolveTerm(application.list[i], {}, diagnostics);
                if (!object) { return false; }
                arguments.push_back(*object);
            }
            const auto value = resolveTerm(literal.list[2], {}, diagnostics);
            if (!value || !isSubtype(object_types_.at(*value), object_result_types_.at(application.head()))) {
                diagnostics.error(ErrorCode::E_TYPE, "object initial value has incompatible type");
                return false;
            }
            const auto index = object_indices_.at(canonical(application.head(), arguments));
            if (!assigned.insert(index).second) {
                diagnostics.error(ErrorCode::E_PARSE, "duplicate object initialization");
                return false;
            }
            object_initial_.emplace_back(index, object_name_indices_.at(*value));
        }
        init_ = std::move(remaining);
        return true;
    }

    void declareObjectState(H::ConstraintModel& model, unsigned step, bool post = false) {
        for (std::size_t index = 0; index < object_ground_.size(); ++index) {
            const auto& ground = object_ground_[index];
            const auto cell = post ? objectPostAt(index, step) : objectAt(index, step);
            const std::string state = std::string(post ? "post[" : "state[") + std::to_string(step) + "]::";
            declare(model, cell.value->name, state + "object-code::" + ground.label, H::Sort::integer());
            declare(model, cell.defined->name, state + "defined(object::" + ground.label + ")");
            S::ChoiceObservable choice;
            choice.source_name = state + "object::" + ground.label;
            // Named decoding includes undefined explicitly; it is a state value,
            // never a source term that could be tested by equality.
            const auto alternative = [&](const std::string& label, H::ExprPtr truth, std::size_t code) {
                const auto target = cell.value->name + "@object-choice" + std::to_string(code);
                declare(model, target);
                addAxiom(model, H::mkOp(H::Op::EQ, {H::mkIdent(target, H::Sort::boolean()), truth}));
                choice.alternatives.push_back({label, target});
            };
            alternative("undefined", H::mkOp(H::Op::NOT, {cell.defined}), 0);
            for (std::size_t object = 0; object < object_universe_.objects.size(); ++object) {
                if (!isSubtype(object_universe_.objects[object].type, ground.type)) { continue; }
                alternative(object_universe_.objects[object].name,
                    conjunction({cell.defined, H::mkOp(H::Op::EQ, {cell.value, H::mkInt(std::to_string(object + 1))})}), object + 1);
            }
            projection_.choices.push_back(std::move(choice));
        }
    }

    bool initializeNumeric(Uir::Diagnostics& diagnostics) {
        for (const auto& literal : init_) {
            if (literal.head() != "=") { continue; }
            if (literal.list.size() != 3 || !decimalNumber(literal.list[2])) {
                diagnostics.error(ErrorCode::E_PARSE, "numeric initialization requires one function and an exact decimal");
                return false;
            }
            const auto key = numericKey(object_mode_ ? functionApplication(literal.list[1]) : literal.list[1], {}, diagnostics);
            auto value = P::numericConstant(literal.list[2].atom.front() == '+'
                ? literal.list[2].atom.substr(1) : literal.list[2].atom, diagnostics);
            if (!key || !value) { return false; }
            if (!numeric_initial_.emplace(*key, value->value).second) {
                diagnostics.error(ErrorCode::E_PARSE, "duplicate numeric initialization");
                return false;
            }
        }
        for (const auto& entry : numeric_functions_) {
            const auto& name = entry.first;
            const auto& function = entry.second;
            Environment environment;
            bool ok = true;
            enumerate(function.params, 0, environment, [&](Environment& bound) {
                std::vector<std::string> args;
                for (const auto& parameter : function.params) { args.push_back(bound.at(parameter.name)); }
                const auto key = canonical(name, args);
                const auto target = allocateTarget("__pddl_numeric_" + std::to_string(numeric_ground_.size()), "numeric:" + key);
                numeric_indices_.emplace(key, numeric_ground_.size());
                // A Bool predicate may share a spelling with a numeric
                // function. Keep both typed source observables injective.
                const auto label = (predicates_.count(name) ? "numeric::" : "") + sourceCall(name, args);
                numeric_ground_.push_back({key, target, label});
                return true;
            }, ok);
            if (!ok) { return false; }
        }
        init_.erase(std::remove_if(init_.begin(), init_.end(),
            [](const Sexp& literal) { return literal.head() == "="; }), init_.end());
        return true;
    }

    // PDDL's action-cost fragment has one mutable accumulator. Other numeric
    // functions are a total, static table; decimals remain exact rationals.
    H::ExprPtr nonnegativeNumber(const Sexp& expression,
                                 Uir::Diagnostics& diagnostics) const {
        const auto& value = expression.atom;
        bool dot = false;
        bool valid = !value.empty() && std::isdigit(static_cast<unsigned char>(value.front()))
                     && std::isdigit(static_cast<unsigned char>(value.back()));
        for (unsigned char c : value) {
            if (c == '.' && !dot) { dot = true; }
            else if (!std::isdigit(c)) { valid = false; }
        }
        if (!expression.isAtom() || !valid) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "action costs require nonnegative decimal constants or initialized static functions");
            return nullptr;
        }
        return H::mkReal(value);
    }

    std::optional<std::string> numericKey(const Sexp& expression,
                                          const Environment& environment,
                                          Uir::Diagnostics& diagnostics) const {
        const auto function = numeric_functions_.find(expression.head());
        if (function == numeric_functions_.end()
            || expression.list.size() != function->second.params.size() + 1) {
            diagnostics.error(ErrorCode::E_TYPE, "undeclared or ill-formed numeric function application");
            return std::nullopt;
        }
        std::vector<std::string> args;
        for (std::size_t i = 0; i < function->second.params.size(); ++i) {
            const auto object = resolveTerm(expression.list[i + 1], environment, diagnostics);
            if (!object) { return std::nullopt; }
            if (!isSubtype(object_types_.at(*object), function->second.params[i].type)) {
                diagnostics.error(ErrorCode::E_TYPE, "numeric function argument has the wrong type");
                return std::nullopt;
            }
            args.push_back(*object);
        }
        return canonical(expression.head(), args);
    }

    H::ExprPtr staticCost(const Sexp& expression, const Environment& environment,
                         Uir::Diagnostics& diagnostics) const {
        if (expression.isAtom()) { return nonnegativeNumber(expression, diagnostics); }
        if (expression.head() == "total-cost") {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "total-cost may only be increased and minimized, not read as an action cost");
            return nullptr;
        }
        const auto key = numericKey(expression, environment, diagnostics);
        if (!key) { return nullptr; }
        const auto value = numeric_initial_.find(*key);
        if (value == numeric_initial_.end()) {
            diagnostics.error(ErrorCode::E_TYPE, "a numeric function application has no initial value");
            return nullptr;
        }
        return value->second;
    }

    bool initializeCosts(Uir::Diagnostics& diagnostics) {
        for (const auto& literal : init_) {
            if (literal.head() != "=") { continue; }
            if (literal.list.size() != 3) {
                diagnostics.error(ErrorCode::E_PARSE, "malformed numeric initialization");
                return false;
            }
            const auto key = numericKey(literal.list[1], {}, diagnostics);
            const auto value = nonnegativeNumber(literal.list[2], diagnostics);
            if (!key || !value) { return false; }
            if (!numeric_initial_.emplace(*key, value).second) {
                diagnostics.error(ErrorCode::E_PARSE, "duplicate numeric initialization");
                return false;
            }
        }
        for (const auto& entry : numeric_functions_) {
            const auto& name = entry.first;
            const auto& function = entry.second;
            Environment environment;
            bool ok = true;
            enumerate(function.params, 0, environment, [&](Environment& bound) {
                std::vector<std::string> args;
                for (const auto& parameter : function.params) { args.push_back(bound.at(parameter.name)); }
                if (!numeric_initial_.count(canonical(name, args))) {
                    diagnostics.error(ErrorCode::E_TYPE,
                        "numeric initialization is not total: missing " + sourceCall(name, args));
                    return false;
                }
                return true;
            }, ok);
            if (!ok) { return false; }
        }
        init_.erase(std::remove_if(init_.begin(), init_.end(),
            [](const Sexp& literal) { return literal.head() == "="; }), init_.end());
        if (!numeric_functions_.empty()) {
            cost_target_ = allocateTarget("__pddl_total_cost", "numeric:total-cost");
        }
        return true;
    }

    std::optional<std::string> schemaTermType(const Sexp& term, const Environment& types,
                                             Uir::Diagnostics& diagnostics) const {
        if (term.isAtom()) {
            if (isVariable(term.atom)) {
                const auto found = types.find(term.atom);
                if (found != types.end()) { return found->second; }
            } else {
                const auto found = object_types_.find(term.atom);
                if (found != object_types_.end()) { return found->second; }
            }
        }
        if (!term.isAtom()) {
            const auto function = object_functions_.find(term.head());
            if (function != object_functions_.end()
                && validateApplication(term, types, object_functions_, diagnostics)) {
                return object_result_types_.at(term.head());
            }
        }
        diagnostics.error(ErrorCode::E_TYPE, "unbound, undeclared or non-object term in action schema");
        return std::nullopt;
    }

    bool validateApplication(const Sexp& expression, const Environment& types,
                             const std::map<std::string, Predicate>& declarations,
                             Uir::Diagnostics& diagnostics) const {
        const auto declaration = declarations.find(expression.head());
        if (declaration == declarations.end()
            || expression.list.size() != declaration->second.params.size() + 1) {
            diagnostics.error(ErrorCode::E_TYPE,
                "undeclared or wrong-arity application '" + expression.head() + "' in action schema");
            return false;
        }
        for (std::size_t i = 0; i < declaration->second.params.size(); ++i) {
            const auto actual = schemaTermType(expression.list[i + 1], types, diagnostics);
            if (!actual) { return false; }
            if (!isSubtype(*actual, declaration->second.params[i].type)) {
                diagnostics.error(ErrorCode::E_TYPE, "incompatible argument type in action schema");
                return false;
            }
        }
        return true;
    }

    // Validate every schema before finite expansion, including unreachable
    // actions, empty object domains and horizon zero. Demand grounding must
    // never hide malformed or unsupported source constructs.
    bool validateDerivedHeads(Uir::Diagnostics& diagnostics) {
        if (!derived_.empty()
            && !requireFeature(":derived-predicates", "`:derived`", diagnostics)) { return false; }
        for (auto& rule : derived_) {
            const auto declaration = predicates_.find(rule.head.head());
            if (declaration == predicates_.end()
                || !typedList(rule.head, 1, true, "derived head", rule.params, diagnostics)
                || rule.params.size() != declaration->second.params.size()) {
                diagnostics.error(ErrorCode::E_TYPE, "undeclared or wrong-arity derived head");
                return false;
            }
            // Omitted types inherit the predicate argument type; explicit
            // annotations may narrow it (PDDL2.2 Appendix A.4).
            std::set<std::string> explicit_types;
            std::vector<std::string> pending;
            for (std::size_t i = 1; i < rule.head.list.size(); ++i) {
                if (rule.head.list[i].atom == "-") {
                    explicit_types.insert(pending.begin(), pending.end());
                    pending.clear();
                    ++i;
                } else { pending.push_back(rule.head.list[i].atom); }
            }
            if (!explicit_types.empty()
                && !requireFeature(":typing", "typed derived head", diagnostics)) { return false; }
            for (std::size_t i = 0; i < rule.params.size(); ++i) {
                auto& parameter = rule.params[i];
                const auto& expected = declaration->second.params[i].type;
                if (!explicit_types.count(parameter.name)) { parameter.type = expected; }
                if (!knownObjectType(parameter.type) || !isSubtype(parameter.type, expected)) {
                    diagnostics.error(ErrorCode::E_TYPE, "incompatible type in derived head");
                    return false;
                }
            }
        }
        return true;
    }

    bool derivedBodyVariables(const Sexp& expression, std::set<std::string> bound,
                              std::set<std::string>& free, bool positive,
                              Uir::Diagnostics& diagnostics) {
        if (expression.isAtom()) {
            if (isVariable(expression.atom) && !bound.count(expression.atom)) {
                free.insert(expression.atom);
            }
            return true;
        }
        const auto& head = expression.head();
        if ((numeric_mode_ && numericComparison(expression)) || (object_mode_ && head == "=")) {
            // Numeric/object function and predicate names occupy different source
            // syntactic contexts. validateSchema already checked this entire
            // numeric comparison; only its object-variable occurrences enter
            // the derived rule's free-variable check.
            std::function<void(const Sexp&)> variables = [&](const Sexp& term) {
                if (term.isAtom()) {
                    if (isVariable(term.atom) && !bound.count(term.atom)) { free.insert(term.atom); }
                } else {
                    for (std::size_t i = 1; i < term.list.size(); ++i) { variables(term.list[i]); }
                }
            };
            variables(expression);
            return true;
        }
        if (derived_predicates_.count(head) && !positive) {
            diagnostics.error(ErrorCode::E_TYPE, "a derived rule cannot contain a negative derived occurrence");
            return false;
        }
        if (head == "forall" || head == "exists") {
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "derived quantifier", variables, diagnostics)) {
                return false;
            }
            for (const auto& variable : variables) { bound.insert(variable.name); }
            return derivedBodyVariables(expression.list[2], std::move(bound), free, positive, diagnostics);
        }
        if (object_mode_ && predicates_.count(head)) {
            std::function<void(const Sexp&)> variables = [&](const Sexp& term) {
                if (term.isAtom()) {
                    if (isVariable(term.atom) && !bound.count(term.atom)) { free.insert(term.atom); }
                } else {
                    for (std::size_t i = 1; i < term.list.size(); ++i) { variables(term.list[i]); }
                }
            };
            for (std::size_t i = 1; i < expression.list.size(); ++i) { variables(expression.list[i]); }
            return true;
        }
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            const bool sign = head == "not" || (head == "imply" && i == 1) ? !positive : positive;
            if (!derivedBodyVariables(expression.list[i], bound, free, sign, diagnostics)) { return false; }
        }
        return true;
    }

    bool validateDerivedBodies(Uir::Diagnostics& diagnostics) {
        for (const auto& rule : derived_) {
            Environment types;
            std::set<std::string> head_variables, free;
            for (const auto& parameter : rule.params) {
                types.emplace(parameter.name, parameter.type);
                head_variables.insert(parameter.name);
            }
            // Validate before finite grounding: an empty type or false branch
            // must not conceal ill-typed syntax or a forbidden dependency.
            if (!validateSchema(rule.body, types, false, diagnostics)
                || !derivedBodyVariables(rule.body, {}, free, true, diagnostics)) { return false; }
            if (head_variables != free) {
                diagnostics.error(ErrorCode::E_TYPE, "derived body free variables must be exactly its distinct head variables");
                return false;
            }
        }
        return true;
    }

    // Insert into the joint numeric/derived/temporal Adapter. This traverses
    // source syntax independently of Boolean simplification, as required by
    // PDDL2.2's syntactic dependency graph for no-moving-targets interference.
    bool derivedSourceReads(const Sexp& expression, Environment& environment,
                            unsigned step, std::set<std::string>& reads,
                            Uir::Diagnostics& diagnostics) {
        if (expression.isAtom() || expression.list.empty()) { return true; }
        if (object_mode_) {
            // Object mode is sequential. Retain all dependency alternatives;
            // this conservative metadata is NOT used as temporal mutex guards.
            auto condition = numericCondition(expression, environment, step, diagnostics);
            if (!condition) { return false; }
            std::vector<H::ExprPtr> pending{condition->value, condition->defined};
            std::unordered_set<const H::Expr*> seen;
            while (!pending.empty()) {
                auto term = pending.back(); pending.pop_back();
                if (!seen.insert(term.get()).second) { continue; }
                if (term->kind == H::ExprKind::IDENT) { reads.insert(term->name); }
                pending.insert(pending.end(), term->args.begin(), term->args.end());
            }
            return true;
        }
        const auto& head = expression.head();
        if (head == "forall" || head == "exists") {
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "derived read quantifier", variables, diagnostics)) {
                return false;
            }
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                return derivedSourceReads(expression.list[2], bound, step, reads, diagnostics);
            }, ok);
            return ok;
        }
        if (numeric_mode_ && numericComparison(expression)) {
            const auto condition = numericCondition(expression, environment, step, diagnostics);
            if (!condition) { return false; }
            for (const auto index : condition->reads) {
                const auto cell = numericAt(index, step);
                reads.insert(cell.value->name);
                reads.insert(cell.defined->name);
            }
            return true;
        }
        if (predicates_.count(head)) {
            const auto base = atomBase(expression, environment, diagnostics);
            if (!base) { return false; }
            reads.insert(atomAt(*base, step)->name);
            return true;
        }
        if (numeric_functions_.count(head)) {
            const auto value = numericExpression(expression, environment, step, diagnostics);
            if (!value) { return false; }
            for (const auto index : value->reads) {
                const auto cell = numericAt(index, step);
                reads.insert(cell.value->name);
                reads.insert(cell.defined->name);
            }
            return true;
        }
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            if (!derivedSourceReads(expression.list[i], environment, step, reads, diagnostics)) { return false; }
        }
        return true;
    }

    bool refreshDerivedSourceReads(unsigned step, Uir::Diagnostics& diagnostics) {
        std::map<std::string, std::set<std::string>> dependencies;
        for (const auto& atom : atoms_) {
            if (derived_predicates_.count(atom.predicate)) {
                dependencies.emplace(atomAt(atom.target_base, step)->name, std::set<std::string>{});
            }
        }
        for (const auto& rule : derived_) {
            Environment environment;
            bool ok = true;
            enumerate(rule.params, 0, environment, [&](Environment& bound) {
                std::vector<std::string> arguments;
                for (const auto& parameter : rule.params) { arguments.push_back(bound.at(parameter.name)); }
                const auto& base = atom_targets_.at(canonical(rule.head.head(), arguments));
                return derivedSourceReads(rule.body, bound, step,
                    dependencies.at(atomAt(base, step)->name), diagnostics);
            }, ok);
            if (!ok) { return false; }
        }
        bool grew = true;
        while (grew) {
            grew = false;
            for (auto& entry : dependencies) {
                for (const auto& symbol : entry.second) {
                    const auto found = dependencies.find(symbol);
                    if (found == dependencies.end()) { continue; }
                    for (const auto& transitive : found->second) {
                        grew |= entry.second.insert(transitive).second;
                    }
                }
            }
        }
        for (auto& entry : dependencies) {
            for (const auto& derived : dependencies) { entry.second.erase(derived.first); }
        }
        derived_reads_[step] = std::move(dependencies);
        return true;
    }

    bool appendDerivedAt(H::ConstraintModel& model, unsigned step, Uir::Diagnostics& diagnostics) {
        if (derived_.empty()) { return true; }
        std::vector<H::ExprPtr> universe;
        std::map<std::string, std::size_t> indices;
        for (const auto& atom : atoms_) {
            if (!derived_predicates_.count(atom.predicate)) { continue; }
            indices.emplace(canonical(atom.predicate, atom.args), universe.size());
            universe.push_back(atomAt(atom.target_base, step));
        }
        std::vector<H::Planning::DerivedRule> rules;
        for (const auto& rule : derived_) {
            Environment environment;
            bool ok = true;
            enumerate(rule.params, 0, environment, [&](Environment& bound) {
                std::vector<std::string> arguments;
                for (const auto& parameter : rule.params) { arguments.push_back(bound.at(parameter.name)); }
                auto body = formula(rule.body, bound, step, diagnostics);
                if (!body) { return false; }
                rules.push_back({indices.at(canonical(rule.head.head(), arguments)), body, {}});
                return true;
            }, ok);
            if (!ok) { return false; }
        }
        auto closure = H::Planning::buildDerivedClosure(model, universe, rules,
            "__pddl_derived@" + std::to_string(step), diagnostics);
        if (!closure) { return false; }
        for (auto& declaration : closure->declarations) {
            declared_.insert(declaration.name);
            model.decls.push_back(std::move(declaration));
        }
        FlowReplacements expansions;
        for (const auto& constraint : closure->constraints) {
            addAxiom(model, constraint.formula);
            if (continuous_mode_) {
                const auto& equation = constraint.formula;
                expansions.emplace(equation->args[0]->name, equation->args[1]);
            }
        }
        for (std::size_t i = 0; i < universe.size(); ++i) {
            addAxiom(model, H::mkOp(H::Op::EQ, {universe[i], closure->values[i]}));
            derived_reads_[step][universe[i]->name] = std::move(closure->base_dependencies[i]);
            if (continuous_mode_) {
                continuous_derived_[step][universe[i]->name] = flowRewrite(closure->values[i], expansions);
            }
        }
        return refreshDerivedSourceReads(step, diagnostics);
    }

    bool validateSchema(const Sexp& expression, Environment types, bool effect,
                         Uir::Diagnostics& diagnostics) {
        if (expression.isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE, "action conditions/effects must be parenthesized");
            return false;
        }
        if (expression.list.empty()) { return true; }
        const auto& head = expression.head();
        if (effect && (derived_predicates_.count(head)
            || (head == "not" && expression.list.size() == 2
                && derived_predicates_.count(expression.list[1].head())))) {
            diagnostics.error(ErrorCode::E_TYPE, "an action effect cannot assign a derived predicate");
            return false;
        }
        if (head == "and" || (!effect && head == "or")) {
            if (head == "or" && !requireFeature(":disjunctive-preconditions", "`or`", diagnostics)) {
                return false;
            }
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!validateSchema(expression.list[i], types, effect, diagnostics)) { return false; }
            }
            return true;
        }
        if (head == "not" && expression.list.size() == 2) {
            if (effect) { return validateApplication(expression.list[1], types, predicates_, diagnostics); }
            const auto& child = expression.list[1].head();
            const bool atomic = child != "and" && child != "or" && child != "not"
                && child != "imply" && child != "forall" && child != "exists";
            return requireFeature(atomic ? ":negative-preconditions" : ":disjunctive-preconditions",
                                  "`not` condition", diagnostics)
                && validateSchema(expression.list[1], types, false, diagnostics);
        }
        if ((!effect && head == "imply") || (effect && head == "when")) {
            if (expression.list.size() != 3) {
                diagnostics.error(ErrorCode::E_PARSE, "malformed implication/conditional effect");
                return false;
            }
            return requireFeature(effect ? ":conditional-effects" : ":disjunctive-preconditions",
                                  head, diagnostics)
                && validateSchema(expression.list[1], types, false, diagnostics)
                && validateSchema(expression.list[2], types, effect, diagnostics);
        }
        if (head == "forall" || (!effect && head == "exists")) {
            if (expression.list.size() != 3 || expression.list[1].isAtom()) {
                diagnostics.error(ErrorCode::E_PARSE, "malformed quantified condition/effect");
                return false;
            }
            if (!requireFeature(effect ? ":conditional-effects" : head == "forall"
                                ? ":universal-preconditions" : ":existential-preconditions",
                                head, diagnostics)) { return false; }
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "quantifier", variables, diagnostics)) { return false; }
            for (const auto& variable : variables) {
                if (!knownObjectType(variable.type)) {
                    diagnostics.error(ErrorCode::E_TYPE, "unknown type in quantifier");
                    return false;
                }
                types[variable.name] = variable.type;
            }
            return validateSchema(expression.list[2], std::move(types), effect, diagnostics);
        }
        if (object_mode_ && effect && numericUpdate(head) && expression.list.size() == 3
            && object_functions_.count(expression.list[1].head())) {
            if (head != "assign") {
                diagnostics.error(ErrorCode::E_TYPE, "object-valued functions support assign, not numeric update operators");
                return false;
            }
            if (!validateApplication(expression.list[1], types, object_functions_, diagnostics)) { return false; }
            if (expression.list[2].isAtom() && expression.list[2].atom == "undefined") { return true; }
            const auto value_type = schemaTermType(expression.list[2], types, diagnostics);
            if (!value_type || !isSubtype(*value_type, object_result_types_.at(expression.list[1].head()))) {
                diagnostics.error(ErrorCode::E_TYPE, "object assignment RHS has incompatible nominal type");
                return false;
            }
            return true;
        }
        if (numeric_mode_ && !effect && numericComparison(expression)) {
            if (object_mode_ && !requireFeature(":numeric-fluents", "numeric comparison", diagnostics)) { return false; }
            if (expression.list.size() != 3) {
                diagnostics.error(ErrorCode::E_PARSE, "numeric comparison requires two operands");
                return false;
            }
            return validateNumeric(expression.list[1], types, diagnostics)
                && validateNumeric(expression.list[2], types, diagnostics);
        }
        if (numeric_mode_ && effect && numericUpdate(head)) {
            if (expression.list.size() != 3) {
                diagnostics.error(ErrorCode::E_PARSE, "numeric effect requires target and expression");
                return false;
            }
            return validateApplication(expression.list[1], types, numeric_functions_, diagnostics)
                && validateNumeric(expression.list[2], types, diagnostics);
        }
        if (!effect && head == "=" && expression.list.size() == 3) {
            return requireFeature(":equality", "object equality", diagnostics)
                && schemaTermType(expression.list[1], types, diagnostics)
                && schemaTermType(expression.list[2], types, diagnostics);
        }
        if (effect && head == "increase" && expression.list.size() == 3) {
            if (expression.list[1].head() != "total-cost" || expression.list[1].list.size() != 1
                || cost_target_.empty() || expression.list[2].head() == "total-cost") {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "cost effects must increase total-cost by a nonnegative static amount");
                return false;
            }
            return expression.list[2].isAtom()
                ? static_cast<bool>(nonnegativeNumber(expression.list[2], diagnostics))
                : validateApplication(expression.list[2], types, numeric_functions_, diagnostics);
        }
        return validateApplication(expression, types, predicates_, diagnostics);
    }

    // Ground fluent names are global, never quantifier-bound. Immutable HIR
    // leaves can be shared by conditions, updates and frame axioms. Separate
    // typed caches avoid conflating Boolean fluents with the Real accumulator.
    H::ExprPtr atomAt(const std::string& base, unsigned step) {
        const auto [entry, inserted] = fluent_identifiers_.try_emplace(
            base + "@" + std::to_string(step));
        if (inserted) { entry->second = H::mkIdent(entry->first, H::Sort::boolean()); }
        return entry->second;
    }

    H::ExprPtr costAt(unsigned step) {
        const auto [entry, inserted] = cost_identifiers_.try_emplace(
            cost_target_ + "@" + std::to_string(step));
        if (inserted) { entry->second = H::mkIdent(entry->first, H::Sort::real()); }
        return entry->second;
    }

    std::optional<std::string> effectBase(const Sexp& expression, const Environment& environment,
                                         Uir::Diagnostics& diagnostics) const {
        auto base = atomBase(expression, environment, diagnostics);
        if (base && base->compare(0, sizeof(STATIC_ATOM_PREFIX) - 1, STATIC_ATOM_PREFIX) == 0) {
            diagnostics.error(ErrorCode::E_INTERNAL, "effect target was omitted from mutable fluent grounding");
            return std::nullopt;
        }
        return base;
    }

    bool collectEffects(const Sexp& expression, Environment& environment,
                        unsigned step, H::ExprPtr guard,
                        std::map<std::string, FluentUpdates>& updates,
                        Uir::Diagnostics& diagnostics) {
        // Deterministic lowering has validated the complete action schema.
        // FOND uses the same collector without that gate and still traverses
        // its source, so a false guard cannot conceal malformed syntax there.
        if (static_conditions_validated_ && guard->kind == H::ExprKind::LIT_BOOL
            && !guard->bool_value) { return true; }
        if (expression.isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "a PDDL effect must be parenthesized");
            return false;
        }
        if (expression.list.empty()) { return true; }
        const std::string head = expression.head();
        if (object_mode_ && head == "assign" && expression.list.size() == 3
            && object_functions_.count(expression.list[1].head())) {
            return objectAssignment(expression, environment, step, guard, diagnostics);
        }
        if (numeric_mode_ && numericUpdate(head)) {
            if (expression.list.size() != 3) { return false; }
            if (object_mode_) {
                const auto& target = expression.list[1];
                const auto declaration = numeric_functions_.find(target.head());
                if (declaration == numeric_functions_.end()) { return false; }
                const auto dispatch = objectDispatchFor(target, declaration->second, "numeric", environment, step, diagnostics);
                const auto rhs = numericExpression(expression.list[2], environment, step, diagnostics);
                if (!dispatch || !rhs) { return false; }
                pending_numeric_conditions_.push_back(H::mkOp(H::Op::IMPLIES, {guard, dispatch->defined}));
                const auto kind = head == "assign" ? P::NumericUpdateKind::ASSIGN
                    : head == "increase" ? P::NumericUpdateKind::INCREASE
                    : head == "decrease" ? P::NumericUpdateKind::DECREASE
                    : head == "scale-up" ? P::NumericUpdateKind::SCALE_UP : P::NumericUpdateKind::SCALE_DOWN;
                const auto& table = objectTable("numeric", target.head(), declaration->second);
                for (std::size_t i = 0; i < table.rows.size(); ++i) {
                    const auto index = numeric_indices_.at(objectRowKey(target.head(), table.rows[i]));
                    pending_numeric_.push_back({index, kind, *rhs,
                        conjunction({guard, dispatch->matches[i]}), "pending"});
                }
                return true;
            }
            const auto key = numericKey(expression.list[1], environment, diagnostics);
            auto rhs = numericExpression(expression.list[2], environment, step, diagnostics);
            if (!key || !rhs) { return false; }
            const auto kind = head == "assign" ? P::NumericUpdateKind::ASSIGN
                : head == "increase" ? P::NumericUpdateKind::INCREASE
                : head == "decrease" ? P::NumericUpdateKind::DECREASE
                : head == "scale-up" ? P::NumericUpdateKind::SCALE_UP : P::NumericUpdateKind::SCALE_DOWN;
            pending_numeric_.push_back({numeric_indices_.at(*key), kind, *rhs, guard, "pending"});
            return true;
        }
        if (head == "increase") {
            if (expression.list.size() != 3 || expression.list[1].head() != "total-cost"
                || expression.list[1].list.size() != 1 || cost_target_.empty()) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "only increases of the declared nullary total-cost accumulator are supported");
                return false;
            }
            const auto amount = staticCost(expression.list[2], environment, diagnostics);
            if (!amount) { return false; }
            pending_costs_.push_back(guard->kind == H::ExprKind::LIT_BOOL
                ? (guard->bool_value ? amount : H::mkReal("0"))
                : H::mkOp(H::Op::ITE, {guard, amount, H::mkReal("0")}));
            return true;
        }
        if (head == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!collectEffects(expression.list[i], environment, step, guard,
                                    updates, diagnostics)) {
                    return false;
                }
            }
            return true;
        }
        if (head == "not") {
            if (expression.list.size() != 2) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "a delete effect is `(not (predicate ...))`");
                return false;
            }
            if (object_mode_) { return objectPredicateEffect(expression.list[1], environment, step, guard, false, updates, diagnostics); }
            const auto base = effectBase(expression.list[1], environment, diagnostics);
            if (!base) { return false; }
            updates[*base].delete_conditions.push_back(std::move(guard));
            return true;
        }
        if (head == "when") {
            if (expression.list.size() != 3
                || !requireFeature(":conditional-effects", "conditional effect",
                                   diagnostics)) {
                return false;
            }
            H::ExprPtr condition;
            if (numeric_mode_) {
                auto numeric = numericCondition(expression.list[1], environment, step, diagnostics);
                if (!numeric) { return false; }
                pending_numeric_conditions_.push_back(H::mkOp(H::Op::IMPLIES, {guard, numeric->defined}));
                condition = numeric->value;
            } else {
                condition = formula(expression.list[1], environment, step, diagnostics);
            }
            if (!condition) { return false; }
            H::ExprPtr combined = conjunction({guard, condition});
            return collectEffects(expression.list[2], environment, step,
                                  std::move(combined), updates, diagnostics);
        }
        if (head == "forall") {
            if (expression.list.size() != 3 || expression.list[1].isAtom()
                || !requireFeature(":conditional-effects",
                                   "universally quantified effect", diagnostics)) {
                return false;
            }
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "effect `forall` binder",
                           variables, diagnostics)) {
                return false;
            }
            for (const Typed& variable : variables) {
                if (!knownObjectType(variable.type)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "effect quantifier uses unknown type '"
                                          + variable.type + "'");
                    return false;
                }
            }
            bool ok = true;
            enumerate(variables, 0, environment,
                      [&](Environment& bound) {
                          return collectEffects(expression.list[2], bound, step,
                                                guard, updates, diagnostics);
                      },
                      ok);
            return ok;
        }
        if (head == "oneof") {
            diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "`oneof` is a non-deterministic effect: the source asks for a "
                "policy against environment choices, not an existential action sequence");
            return false;
        }
        if (object_mode_) { return objectPredicateEffect(expression, environment, step, guard, true, updates, diagnostics); }
        const auto base = effectBase(expression, environment, diagnostics);
        if (!base) { return false; }
        updates[*base].add_conditions.push_back(std::move(guard));
        return true;
    }

    bool initialState(std::set<std::string>& true_atoms,
                      Uir::Diagnostics& diagnostics, bool source_keys = false) {
        std::set<std::string> false_atoms;
        Environment empty;
        for (const Sexp& literal : init_) {
            bool positive = true;
            const Sexp* atom = &literal;
            if (!literal.list.empty() && literal.head() == "not") {
                if (literal.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed negative initial literal");
                    return false;
                }
                positive = false;
                atom = &literal.list[1];
            }
            if (derived_predicates_.count(atom->head())) {
                diagnostics.error(ErrorCode::E_TYPE, "initial facts cannot assign a derived predicate");
                return false;
            }
            if (!atom->list.empty() && atom->head() == "=") {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "numeric/object assignments in `:init` are outside the "
                                  "accepted Boolean fluent fragment");
                return false;
            }
            const auto base = atomBase(*atom, empty, diagnostics, source_keys);
            if (!base) { return false; }
            if (positive) {
                if (false_atoms.count(*base) != 0) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "initial state both asserts and negates '" + *base + "'");
                    return false;
                }
                true_atoms.insert(*base);
            } else {
                if (true_atoms.count(*base) != 0) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "initial state both asserts and negates '" + *base + "'");
                    return false;
                }
                false_atoms.insert(*base);
            }
        }
        return true;
    }

    void declare(H::ConstraintModel& model, const std::string& target,
                 const std::optional<std::string>& source = std::nullopt,
                 const H::Sort& sort = H::Sort::boolean()) {
        if (!declared_.insert(target).second) { return; }
        H::VarDecl declaration;
        declaration.name = target;
        declaration.sort = sort;
        declaration.auxiliary = true;
        model.decls.push_back(std::move(declaration));
        if (source) {
            source_signature_.symbols.push_back(
                {*source, S::SymbolKind::CONSTANT, {}, sort});
            symbol_map_.push_back({*source, target});
        }
    }

    static void add(H::ConstraintModel& model, const H::ExprPtr& expression) {
        H::Constraint constraint;
        constraint.formula = expression;
        model.constraints.push_back(std::move(constraint));
    }

    void addAxiom(H::ConstraintModel& model, const H::ExprPtr& expression) {
        add(model, expression);
        target_axioms_.push_back(expression);
    }

    void recordRelaxations(Uir::TranslationReport& report) {
        if (!relaxed_features_.empty()) {
            // A decision written only in a warning is a decision no downstream
            // consumer can group by (D31). The model this produces is not the
            // one a conforming planner reads, so the report has to say which
            // requirements were assumed.
            std::string names;
            for (const std::string& f : relaxed_features_) {
                if (!names.empty()) { names += " "; }
                names += f;
            }
            Uir::EncodingChoice relaxed;
            relaxed.site = file_;
            relaxed.unified_op = "requirements";
            relaxed.strategy = "lenient-requirements";
            // Exact: the relaxation changes which FILES are accepted, not what
            // an accepted file means. Every construct admitted here is one this
            // frontend already translates exactly; what is missing is the
            // declaration licensing it.
            relaxed.fidelity = Uir::Fidelity::exact();
            relaxed.rationale =
                "accepted constructs the file's `:requirements` do not declare ("
                + names
                + "); a conforming planner may reject this input, so a coverage "
                  "figure that includes it measures something different from one "
                  "that does not";
            report.addChoice(std::move(relaxed));
        }
    }

    static bool hasOneof(const Sexp& expression) {
        if (expression.head() == "oneof") { return true; }
        return std::any_of(expression.list.begin(), expression.list.end(), hasOneof);
    }

    bool effectOutcomes(const Sexp& effect, std::vector<Sexp>& result,
                        Uir::Diagnostics& diagnostics) {
        const auto head = effect.head();
        if (head == "oneof") {
            if (effect.list.size() < 2) {
                diagnostics.error(ErrorCode::E_PARSE, "oneof requires at least one outcome");
                return false;
            }
            for (std::size_t i = 1; i < effect.list.size(); ++i) {
                std::vector<Sexp> children;
                if (!effectOutcomes(effect.list[i], children, diagnostics)) { return false; }
                result.insert(result.end(), children.begin(), children.end());
                if (result.size() > 256) { break; }
            }
        } else if (head == "and") {
            result = {Sexp{"", {Sexp{"and", {}}}}};
            for (std::size_t i = 1; i < effect.list.size(); ++i) {
                std::vector<Sexp> children, product;
                if (!effectOutcomes(effect.list[i], children, diagnostics)) { return false; }
                if (result.size() * children.size() > 256) {
                    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                      "FOND effect expansion exceeds 256 outcomes per action");
                    return false;
                }
                for (const auto& prefix : result) {
                    for (const auto& child : children) {
                        Sexp combined = prefix;
                        combined.list.push_back(child);
                        product.push_back(std::move(combined));
                    }
                }
                result = std::move(product);
            }
        } else if (head == "when" && effect.list.size() == 3) {
            std::vector<Sexp> children;
            if (!effectOutcomes(effect.list[2], children, diagnostics)) { return false; }
            for (const auto& child : children) {
                result.push_back(Sexp{"", {effect.list[0], effect.list[1], child}});
            }
        } else {
            // Choices under a quantified effect are independent per grounded
            // object. Sharing one branch across the binder would be unsound.
            if (head == "forall" && hasOneof(effect)) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "oneof under forall needs independent per-object outcome expansion");
                return false;
            }
            result.push_back(effect);
        }
        if (result.size() > 256) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "FOND effect expansion exceeds 256 outcomes per action");
            return false;
        }
        return true;
    }

    H::ConstraintModelPtr buildPolicy(Uir::Diagnostics& diagnostics,
                                      Uir::TranslationReport& report) {
        groundAtoms();
        groundActions();
        const unsigned n = policy_size_;
        std::vector<std::vector<Sexp>> outcomes(ground_actions_.size());
        std::size_t outcome_count = 0;
        for (std::size_t a = 0; a < ground_actions_.size(); ++a) {
            const auto& schema = *ground_actions_[a].schema;
            if (!effectOutcomes(schema.has_effect ? schema.effect : Sexp{},
                                outcomes[a], diagnostics)) { return nullptr; }
            outcome_count += outcomes[a].size();
        }
        // Cap the actual construction, not a silently truncated outcome set.
        const std::size_t cells = std::max<std::size_t>(1, atoms_.size()) * n * n;
        if (outcome_count > 3000000 / cells) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "FOND policy relation exceeds the 3000000-cell construction budget");
            return nullptr;
        }
        auto model = std::make_shared<H::ConstraintModel>();
        const auto boolean = H::Sort::boolean();
        const auto bit = [&](const std::string& name) { return H::mkIdent(name, boolean); };
        const auto active = [&](unsigned i) { return bit("__fond_active@" + std::to_string(i)); };
        const auto rank = [&](unsigned i) {
            return H::mkIdent("__fond_rank@" + std::to_string(i), H::Sort::integer());
        };
        const auto state = [&](const GroundAtom& atom, unsigned i) {
            return atomAt(atom.target_base, i);
        };
        const auto implies = [&](H::ExprPtr a, H::ExprPtr b) {
            add(*model, H::mkOp(H::Op::IMPLIES, {a, b}));
        };
        // An injective bit-vector signature makes full-state equality one
        // equality. Define each signature once so later HIR passes do not
        // expand an entire successor vector at every possible target node.
        const auto packed = [&](const std::string& name,
                                const std::vector<H::ExprPtr>& values) {
            std::vector<H::ExprPtr> layer;
            for (const auto& value : values) {
                layer.push_back(H::mkOp(H::Op::ITE,
                    {value, H::mkBitVec("#b1", 1), H::mkBitVec("#b0", 1)}));
            }
            if (layer.empty()) { layer.push_back(H::mkBitVec("#b0", 1)); }
            while (layer.size() > 1) {
                std::vector<H::ExprPtr> next;
                for (std::size_t k = 0; k < layer.size(); k += 2) {
                    next.push_back(k + 1 == layer.size() ? layer[k]
                        : H::mkOp(H::Op::BV_CONCAT, {layer[k], layer[k + 1]}));
                }
                layer = std::move(next);
            }
            H::VarDecl declaration;
            declaration.name = name;
            declaration.sort = H::Sort::bitvec(
                static_cast<unsigned>(std::max<std::size_t>(1, values.size())));
            declaration.auxiliary = true;
            const auto identifier = H::mkIdent(name, declaration.sort);
            model->decls.push_back(std::move(declaration));
            addAxiom(*model, H::mkOp(H::Op::EQ, {identifier, layer.front()}));
            return identifier;
        };
        std::vector<H::ExprPtr> goals;
        std::vector<H::ExprPtr> packed_states;
        Environment empty;
        for (unsigned i = 0; i < n; ++i) {
            const std::string index = std::to_string(i);
            const std::string live_name = "__fond_active@" + index;
            declare(*model, live_name, "policy-active[" + index + "]");
            projection_.observables.push_back({"policy-active[" + index + "]", live_name,
                                               S::ProjectionKind::DIRECT});
            for (const auto& atom : atoms_) {
                const std::string target = atom.target_base + "@" + index;
                const std::string source = "policy-state[" + index + "]::" + atom.source_label;
                declare(*model, target, source);
                projection_.observables.push_back({source, target, S::ProjectionKind::DIRECT});
            }
            std::vector<H::ExprPtr> state_values;
            for (const auto& atom : atoms_) { state_values.push_back(state(atom, i)); }
            packed_states.push_back(packed("__fond_state_bits@" + index, state_values));
            H::VarDecl ordinal;
            ordinal.name = "__fond_rank@" + index;
            ordinal.sort = H::Sort::integer();
            ordinal.auxiliary = true;
            ordinal.lower_bound = H::mkInt(0);
            ordinal.upper_bound = H::mkInt(n - 1);
            model->decls.push_back(std::move(ordinal));
            auto goal = formula(goal_, empty, i, diagnostics);
            if (!goal) { return nullptr; }
            goals.push_back(goal);
            if (i) { addAxiom(*model, H::mkOp(H::Op::IMPLIES, {active(i), active(i - 1)})); }
            for (unsigned j = 0; j < i; ++j) {
                // Full states are distinct, so the policy cannot choose two
                // different actions after observing the same source state.
                addAxiom(*model, H::mkOp(H::Op::IMPLIES,
                    {H::mkOp(H::Op::AND, {active(i), active(j)}),
                     H::mkOp(H::Op::NOT,
                        {H::mkOp(H::Op::EQ, {packed_states[i], packed_states[j]})})}));
            }
        }
        add(*model, active(0));
        std::set<std::string> initially_true;
        if (!initialState(initially_true, diagnostics)) { return nullptr; }
        for (const auto& atom : atoms_) {
            add(*model, initially_true.count(atom.target_base) ? state(atom, 0)
                : H::mkOp(H::Op::NOT, {state(atom, 0)}));
        }
        for (unsigned i = 0; i < n; ++i) {
            const std::string index = std::to_string(i);
            const std::string stopped = "__fond_stop@" + index;
            declare(*model, stopped);
            const auto terminal = bit(stopped);
            addAxiom(*model, H::mkOp(H::Op::EQ,
                {terminal, H::mkOp(H::Op::OR, {H::mkOp(H::Op::NOT, {active(i)}), goals[i]})}));
            std::vector<H::ExprPtr> choices{terminal};
            S::ChoiceObservable projection;
            projection.source_name = "policy-action[" + index + "]";
            projection.omit_label = "__fond_terminal_or_unused";
            projection.alternatives.push_back({projection.omit_label, stopped});
            for (std::size_t a = 0; a < ground_actions_.size(); ++a) {
                const auto& action = ground_actions_[a];
                const std::string chosen = action.target_base + "@" + index;
                declare(*model, chosen, "policy-choice[" + index + "]::" + action.source_label);
                const auto selected = bit(chosen);
                choices.push_back(selected);
                projection.alternatives.push_back({action.source_label, chosen});
                Environment environment = actionEnvironment(action);
                if (action.schema->has_precondition) {
                    auto precondition = formula(action.schema->precondition, environment, i, diagnostics);
                    if (!precondition) { return nullptr; }
                    implies(selected, precondition);
                }
                std::vector<H::ExprPtr> descending;
                std::size_t outcome_index = 0;
                for (const auto& outcome : outcomes[a]) {
                    std::map<std::string, FluentUpdates> updates;
                    if (!collectEffects(outcome, environment, i, H::mkBool(true),
                                        updates, diagnostics)) { return nullptr; }
                    // Compute each successor value once. In particular an
                    // unchanged fluent is just its current value, not a fresh
                    // OR(false, AND(value, NOT(false))) for every target node.
                    std::vector<H::ExprPtr> values;
                    for (const auto& atom : atoms_) {
                        const auto found = updates.find(atom.target_base);
                        if (found == updates.end()) {
                            values.push_back(state(atom, i));
                        } else {
                            values.push_back(H::mkOp(H::Op::OR, {
                                disjunction(found->second.add_conditions),
                                H::mkOp(H::Op::AND, {state(atom, i),
                                    H::mkOp(H::Op::NOT,
                                        {disjunction(found->second.delete_conditions)})})}));
                        }
                    }
                    const auto successor = packed("__fond_next_bits@" + index + "@"
                        + std::to_string(a) + "@" + std::to_string(outcome_index++), values);
                    std::vector<H::ExprPtr> successors;
                    for (unsigned j = 0; j < n; ++j) {
                        const auto match = H::mkOp(H::Op::AND, {active(j),
                            H::mkOp(H::Op::EQ, {packed_states[j], successor})});
                        const auto decrease = H::mkOp(H::Op::AND,
                            {match, H::mkOp(H::Op::LT, {rank(j), rank(i)})});
                        successors.push_back(policy_mode_ == "strong" ? decrease : match);
                        descending.push_back(decrease);
                    }
                    // Conjoin coverage of ALL outcomes. Disjoining outcomes
                    // here would answer favorable-path existence instead.
                    implies(selected, disjunction(std::move(successors)));
                }
                implies(selected, disjunction(std::move(descending)));
            }
            addAxiom(*model, disjunction(choices));
            // A prefix records whether an earlier action was selected. This
            // exactly enforces at-most-one with linear, rather than quadratic,
            // many constraints; auxiliaries have a unique extension.
            H::ExprPtr previous = choices.front();
            for (std::size_t a = 1; a < choices.size(); ++a) {
                addAxiom(*model, H::mkOp(H::Op::NOT,
                    {H::mkOp(H::Op::AND, {previous, choices[a]})}));
                if (a + 1 < choices.size()) {
                    const std::string name = "__fond_choice_prefix@" + index
                        + "@" + std::to_string(a);
                    declare(*model, name);
                    const auto next = bit(name);
                    addAxiom(*model, H::mkOp(H::Op::EQ,
                        {next, H::mkOp(H::Op::OR, {previous, choices[a]})}));
                    previous = next;
                }
            }
            projection_.choices.push_back(std::move(projection));
        }
        Uir::EncodingChoice choice;
        choice.site = file_;
        choice.unified_op = "fond-policy-existence";
        choice.strategy = "bounded-" + policy_mode_ + "-policy";
        Uir::Fidelity::Bound bound;
        bound.kind = Uir::Fidelity::Bound::STRATEGY_SIZE;
        bound.value = n;
        bound.site = file_;
        choice.fidelity = Uir::Fidelity::underApprox(bound);
        choice.rationale = "At most " + std::to_string(n)
            + " distinct full source states, closed under every outcome of the selected "
              "applicable action. Active node 0 is the closed initial state. "
            + (policy_mode_ == "strong"
                ? "All outcome edges decrease a bounded rank; every execution reaches a goal. "
                : "At least one outcome edge decreases rank at each nongoal node. Assuming every "
                  "outcome of an infinitely repeated state/action occurs infinitely often, every "
                  "fair execution reaches a goal. This fairness is required, not inferred. ")
            + "SAT decodes to a state-feedback policy; UNSAT excludes only policies within "
              "STRATEGY_SIZE. No bound on execution length is claimed for strong-cyclic policies.";
        report.addChoice(std::move(choice));
        recordTrajectoryInterpretation(report);
        recordRelaxations(report);
        return model;
    }

    enum class TimePoint { START, END, INTERVAL, FLOW };
    struct TimedFormula {
        TimePoint point;
        Sexp formula;
        Environment environment;
    };
    struct TimedEffect {
        TimePoint point;
        Sexp effect;
        Environment environment;
        std::vector<TimedFormula> conditions;
    };

    bool readDurativeAction(const Sexp& section, Uir::Diagnostics& diagnostics) {
        if (section.list.size() < 2 || !isName(section.list[1].atom)
            || action_names_.count(section.list[1].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed or duplicate durative action");
            return false;
        }
        Action action;
        action.name = section.list[1].atom;
        action.durative = true;
        std::set<std::string> fields;
        for (std::size_t i = 2; i < section.list.size(); i += 2) {
            if (i + 1 == section.list.size() || !section.list[i].isAtom()
                || !fields.insert(section.list[i].atom).second) {
                diagnostics.error(ErrorCode::E_PARSE, "malformed or duplicate durative action field");
                return false;
            }
            const auto& key = section.list[i].atom;
            const auto& value = section.list[i + 1];
            if (key == ":parameters") {
                if (value.isAtom() || !typedList(value, 0, true, "durative parameters", action.params, diagnostics)) { return false; }
            } else if (key == ":duration") { action.duration = value; }
            else if (key == ":condition") { action.precondition = value; action.has_precondition = true; }
            else if (key == ":effect") { action.effect = value; action.has_effect = true; }
            else {
                diagnostics.error(ErrorCode::E_PARSE, "unknown durative action field '" + key + "'");
                return false;
            }
        }
        if (!fields.count(":duration")) {
            diagnostics.error(ErrorCode::E_PARSE, "a durative action requires :duration");
            return false;
        }
        temporal_mode_ = true;
        action_names_.insert(action.name);
        actions_.push_back(std::move(action));
        return true;
    }

    static std::optional<TimePoint> timePoint(const Sexp& expression) {
        if (expression.list.size() != 3) { return std::nullopt; }
        if (expression.head() == "at") {
            if (expression.list[1].atom == "start") { return TimePoint::START; }
            if (expression.list[1].atom == "end") { return TimePoint::END; }
        }
        if (expression.head() == "over" && expression.list[1].atom == "all") { return TimePoint::INTERVAL; }
        return std::nullopt;
    }

    // Validate schemas before finite grounding, including empty quantified
    // domains and actions that cannot be selected at the requested horizon.
    bool validateTimed(const Sexp& expression, Environment types, bool effect,
                       Uir::Diagnostics& diagnostics) {
        if (expression.isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE, "durative expressions must be parenthesized");
            return false;
        }
        if (expression.list.empty()) { return true; }
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!validateTimed(expression.list[i], types, effect, diagnostics)) { return false; }
            }
            return true;
        }
        if (expression.head() == "forall") {
            if (expression.list.size() != 3 || expression.list[1].isAtom()
                || !requireFeature(effect ? ":conditional-effects" : ":universal-preconditions", "durative forall", diagnostics)) { return false; }
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "durative forall", variables, diagnostics)) { return false; }
            for (const auto& variable : variables) {
                if (!knownObjectType(variable.type)) {
                    diagnostics.error(ErrorCode::E_TYPE, "unknown durative quantifier type");
                    return false;
                }
                types[variable.name] = variable.type;
            }
            return validateTimed(expression.list[2], std::move(types), effect, diagnostics);
        }
        if (effect && expression.head() == "when") {
            if (expression.list.size() != 3) {
                diagnostics.error(ErrorCode::E_PARSE, "durative when requires a condition and effect");
                return false;
            }
            const auto contains = [&](const Sexp& root, bool start) {
                std::vector<const Sexp*> pending{&root};
                while (!pending.empty()) {
                    const auto* current = pending.back(); pending.pop_back();
                    const auto point = timePoint(*current);
                    if (point) {
                        if (start ? *point == TimePoint::START : *point != TimePoint::START) { return true; }
                        // A timed node's body is an ordinary GD/effect. A
                        // predicate named at/over there is not another qualifier.
                        continue;
                    }
                    for (const auto& child : current->list) { pending.push_back(&child); }
                }
                return false;
            };
            if (containsElapsedTime(expression.list[2]) && contains(expression.list[1], false)) {
                // The BNF admits this shape, but the causal durative semantics
                // forbids deciding an earlier flow from an end/whole-interval
                // condition. VAL rejects the same combination as TemporalDAError.
                diagnostics.error(ErrorCode::E_PARSE,
                    "a continuous effect cannot depend on an at-end or over-all conditional guard: the effect would depend on future conditions");
                return false;
            }
            if (contains(expression.list[1], false) && contains(expression.list[2], true)) {
                diagnostics.error(ErrorCode::E_PARSE, "a start effect cannot depend on future or interval conditions");
                return false;
            }
            return requireFeature(":conditional-effects", "durative conditional effect", diagnostics)
                && validateTimed(expression.list[1], types, false, diagnostics)
                && validateTimed(expression.list[2], types, true, diagnostics);
        }
        if (effect && containsElapsedTime(expression)) {
            const auto rate = continuousRate(expression, diagnostics);
            if (!rate || !requireFeature(":continuous-effects", "continuous numeric effect", diagnostics)
                || !requireFeature(":fluents", "continuous numeric effect", diagnostics)
                || !validateApplication(expression.list[1], types, numeric_functions_, diagnostics)
                || !validateNumeric(*rate, types, diagnostics)) { return false; }
            continuous_mode_ = true;
            return true;
        }
        const auto point = timePoint(expression);
        if (!point || (effect && *point == TimePoint::INTERVAL)) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "durative discrete effects require at start/end; conditions require at start/end or over all");
            return false;
        }
        return validateSchema(expression.list[2], std::move(types), effect, diagnostics);
    }

    bool validateDuration(const Sexp& expression, const Environment& types,
                          Uir::Diagnostics& diagnostics, bool qualified = false) {
        // The empty duration constraint is explicitly legal in PDDL2.1.
        if (!expression.isAtom() && expression.list.empty()) { return true; }
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!validateDuration(expression.list[i], types, diagnostics)) { return false; }
            }
            return true;
        }
        if (!qualified && expression.head() == "at") {
            const auto point = timePoint(expression);
            return point && *point != TimePoint::INTERVAL
                && validateDuration(expression.list[2], types, diagnostics, true);
        }
        const auto& head = expression.head();
        if ((head != "=" && head != "<=" && head != ">=") || expression.list.size() != 3
            || expression.list[1].atom != "?duration") {
            diagnostics.error(ErrorCode::E_PARSE, "duration requires (=, <= or >= ?duration numeric-expression)");
            return false;
        }
        if (head != "=" && !requireFeature(":duration-inequalities", "duration inequality", diagnostics)) { return false; }
        std::vector<const Sexp*> pending{&expression.list[2]};
        while (!pending.empty()) {
            const auto* item = pending.back(); pending.pop_back();
            if (item->atom == "?duration") {
                diagnostics.error(ErrorCode::E_PARSE, "duration's right-hand value cannot recursively depend on ?duration");
                return false;
            }
            for (const auto& child : item->list) { pending.push_back(&child); }
        }
        return validateNumeric(expression.list[2], types, diagnostics);
    }

    bool groundTimedConditions(const Sexp& expression, Environment& environment,
                               std::vector<TimedFormula>& result, Uir::Diagnostics& diagnostics) {
        if (expression.list.empty() && !expression.isAtom()) { return true; }
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!groundTimedConditions(expression.list[i], environment, result, diagnostics)) { return false; }
            }
            return true;
        }
        if (expression.head() == "forall") {
            std::vector<Typed> variables;
            if (expression.list.size() != 3 || !typedList(expression.list[1], 0, true, "timed forall", variables, diagnostics)) { return false; }
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                return groundTimedConditions(expression.list[2], bound, result, diagnostics);
            }, ok);
            return ok;
        }
        const auto point = timePoint(expression);
        if (!point) { diagnostics.error(ErrorCode::E_PARSE, "missing temporal condition qualifier"); return false; }
        result.push_back({*point, expression.list[2], environment});
        return true;
    }

    bool groundTimedEffects(const Sexp& expression, Environment& environment,
        std::vector<TimedFormula> conditions, std::vector<TimedEffect>& result,
        Uir::Diagnostics& diagnostics) {
        if (expression.list.empty() && !expression.isAtom()) { return true; }
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!groundTimedEffects(expression.list[i], environment, conditions, result, diagnostics)) { return false; }
            }
            return true;
        }
        if (expression.head() == "forall") {
            std::vector<Typed> variables;
            if (expression.list.size() != 3 || !typedList(expression.list[1], 0, true, "timed effect forall", variables, diagnostics)) { return false; }
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                return groundTimedEffects(expression.list[2], bound, conditions, result, diagnostics);
            }, ok);
            return ok;
        }
        if (expression.head() == "when") {
            if (expression.list.size() != 3 || !groundTimedConditions(expression.list[1], environment, conditions, diagnostics)) { return false; }
            return groundTimedEffects(expression.list[2], environment, std::move(conditions), result, diagnostics);
        }
        if (containsElapsedTime(expression)) {
            if (std::any_of(conditions.begin(), conditions.end(), [](const auto& item) {
                    return item.point != TimePoint::START;
                }) || !continuousRate(expression, diagnostics)) { return false; }
            result.push_back({TimePoint::FLOW, expression, environment, std::move(conditions)});
            return true;
        }
        const auto point = timePoint(expression);
        if (!point || *point == TimePoint::INTERVAL) {
            diagnostics.error(ErrorCode::E_PARSE, "missing temporal effect endpoint"); return false;
        }
        if (*point == TimePoint::START && std::any_of(conditions.begin(), conditions.end(), [](const auto& condition) {
                return condition.point != TimePoint::START;
            })) {
            diagnostics.error(ErrorCode::E_PARSE, "a start effect cannot depend on future or interval conditions");
            return false;
        }
        result.push_back({*point, expression.list[2], environment, std::move(conditions)});
        return true;
    }

    // Object codes are exclusive, non-additive scalar resources in the shared
    // endpoint mutex API. The tag cannot collide with canonical source calls.
    static std::string objectResource(const std::string& key) { return "object:" + key; }

    P::ObjectStateCell objectPostAt(std::size_t index, unsigned step) const {
        const auto& ground = object_ground_.at(index);
        const auto base = ground.target + "@post" + std::to_string(step);
        return {H::mkIdent(base, H::Sort::integer()),
                H::mkIdent(base + "@defined", H::Sort::boolean()), objectApiType(ground.type)};
    }

    void objectReadAccess(const std::vector<P::ObjectReadAccess>& reads,
                          const P::TemporalEndpointAccess& endpoint) {
        for (const auto& read : reads) {
            P::TemporalEndpointAccess access;
            access.active = conjunction({endpoint.active, read.when});
            access.time = endpoint.time; access.owner_id = endpoint.owner_id;
            access.numericReads.insert(objectResource(object_ground_.at(read.cell).key));
            temporal_object_accesses_->push_back(std::move(access));
        }
    }

    bool objectTemporalNumericReads(const Sexp& expression, const Environment& environment,
        unsigned step, const P::TemporalEndpointAccess& endpoint, Uir::Diagnostics& diagnostics) {
        if (expression.isAtom() && (decimalNumber(expression) || expression.atom == "?duration"
            || expression.atom == "total-time")) { return true; }
        const auto application = functionApplication(expression);
        const auto& head = application.head();
        if (head == "+" || head == "-" || head == "*" || head == "/") {
            for (std::size_t i = 1; i < application.list.size(); ++i) {
                if (!objectTemporalNumericReads(application.list[i], environment, step, endpoint, diagnostics)) { return false; }
            }
            return true;
        }
        const auto declaration = numeric_functions_.find(head);
        if (declaration == numeric_functions_.end()) {
            diagnostics.error(ErrorCode::E_TYPE, "unknown numeric fluent in temporal object dependency"); return false;
        }
        const auto dispatch = objectDispatchFor(application, declaration->second, "numeric", environment, step, diagnostics);
        if (!dispatch) { return false; }
        objectReadAccess(dispatch->reads, endpoint);
        const auto& table = objectTable("numeric", head, declaration->second);
        for (std::size_t i = 0; i < table.rows.size(); ++i) {
            P::TemporalEndpointAccess access;
            access.active = conjunction({endpoint.active, dispatch->matches[i]});
            access.time = endpoint.time; access.owner_id = endpoint.owner_id;
            access.numericReads.insert(objectRowKey(head, table.rows[i]));
            temporal_object_accesses_->push_back(std::move(access));
        }
        return true;
    }

    bool prepareObjectDerivedBodies(Uir::Diagnostics& diagnostics) {
        for (const auto& rule : derived_) {
            Environment environment; bool ok = true;
            enumerate(rule.params, 0, environment, [&](Environment& bound) {
                std::vector<std::string> arguments;
                for (const auto& parameter : rule.params) { arguments.push_back(bound.at(parameter.name)); }
                object_derived_bodies_[canonical(rule.head.head(), arguments)].emplace_back(rule.body, bound);
                return true;
            }, ok);
            if (!ok) { diagnostics.error(ErrorCode::E_TYPE, "failed finite derived dependency grounding"); return false; }
        }
        return true;
    }

    bool objectTemporalReads(const Sexp& expression, Environment environment, unsigned step,
        const P::TemporalEndpointAccess& endpoint, Uir::Diagnostics& diagnostics,
        std::set<std::string> path = {}) {
        if (expression.list.empty()) { return !expression.isAtom(); }
        const auto& head = expression.head();
        if (head == "forall" || head == "exists") {
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "object temporal read quantifier", variables, diagnostics)) { return false; }
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                return objectTemporalReads(expression.list[2], bound, step, endpoint, diagnostics, path);
            }, ok);
            return ok;
        }
        if (head == "and" || head == "or" || head == "not" || head == "imply") {
            // Read every source branch, including a currently false disjunct.
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!objectTemporalReads(expression.list[i], environment, step, endpoint, diagnostics, path)) { return false; }
            }
            return true;
        }
        if (numericComparison(expression)) {
            return objectTemporalNumericReads(expression.list[1], environment, step, endpoint, diagnostics)
                && objectTemporalNumericReads(expression.list[2], environment, step, endpoint, diagnostics);
        }
        if (head == "=") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                const auto value = objectTerm(expression.list[i], environment, step, diagnostics);
                if (!value) { return false; } objectReadAccess(value->reads, endpoint);
            }
            return true;
        }
        const auto declaration = predicates_.find(head);
        if (declaration == predicates_.end()) { diagnostics.error(ErrorCode::E_TYPE, "unknown temporal object predicate"); return false; }
        const auto dispatch = objectDispatchFor(expression, declaration->second, "predicate", environment, step, diagnostics);
        if (!dispatch) { return false; }
        objectReadAccess(dispatch->reads, endpoint);
        const auto& table = objectTable("predicate", head, declaration->second);
        for (std::size_t i = 0; i < table.rows.size(); ++i) {
            const auto key = objectRowKey(head, table.rows[i]);
            P::TemporalEndpointAccess access;
            access.active = conjunction({endpoint.active, dispatch->matches[i]});
            access.time = endpoint.time; access.owner_id = endpoint.owner_id;
            if (!derived_predicates_.count(head)) {
                access.propositionReads.insert(key);
                temporal_object_accesses_->push_back(std::move(access));
            } else if (!path.count(key)) {
                auto next = path; next.insert(key);
                const auto found = object_derived_bodies_.find(key);
                if (found == object_derived_bodies_.end()) { continue; }
                // The selected finite dependency graph is fixed by this old
                // state. Any path to a basic read has a simple path with the
                // same endpoint, so cycle elimination is exact reachability,
                // not a user-chosen recursion/depth cutoff.
                for (const auto& body : found->second) {
                    if (!objectTemporalReads(body.first, body.second, step, access, diagnostics, next)) { return false; }
                }
            }
        }
        return true;
    }

    bool objectTemporalEffect(const Sexp& expression, const Environment& environment,
        unsigned step, const H::ExprPtr& guard, const std::string& owner, const H::ExprPtr& time,
        H::ConstraintModel& model, std::map<std::string, FluentUpdates>& updates,
        std::vector<P::NumericUpdate>& numeric, Uir::Diagnostics& diagnostics) {
        const auto& head = expression.head();
        P::TemporalEndpointAccess endpoint;
        endpoint.active = guard; endpoint.time = time; endpoint.owner_id = owner;
        if (head == "assign" && object_functions_.count(expression.list[1].head())) {
            if (!objectAssignment(expression, environment, step, guard, diagnostics)) { return false; }
            auto update = std::move(pending_objects_.back()); pending_objects_.pop_back();
            objectReadAccess(update.target.reads, endpoint);
            if (update.rhs) { objectReadAccess(update.rhs->reads, endpoint); }
            for (std::size_t i = 0; i < update.target.cells.size(); ++i) {
                auto access = endpoint;
                access.active = conjunction({guard, update.target.matches[i]});
                access.numericWrites.insert(objectResource(object_ground_.at(update.target.cells[i]).key));
                temporal_object_accesses_->push_back(std::move(access));
            }
            temporal_object_updates_.at(step).push_back(std::move(update));
            return true;
        }
        if (numericUpdate(head)) {
            const auto& target = expression.list[1];
            const auto declaration = numeric_functions_.find(target.head());
            if (declaration == numeric_functions_.end()) { return false; }
            const auto dispatch = objectDispatchFor(target, declaration->second, "numeric", environment, step, diagnostics);
            const auto rhs = numericExpression(expression.list[2], environment, step, diagnostics);
            if (!dispatch || !rhs) { return false; }
            add(model, H::mkOp(H::Op::IMPLIES, {guard, dispatch->defined}));
            objectReadAccess(dispatch->reads, endpoint);
            if (!objectTemporalNumericReads(expression.list[2], environment, step, endpoint, diagnostics)) { return false; }
            const auto kind = head == "assign" ? P::NumericUpdateKind::ASSIGN
                : head == "increase" ? P::NumericUpdateKind::INCREASE
                : head == "decrease" ? P::NumericUpdateKind::DECREASE
                : head == "scale-up" ? P::NumericUpdateKind::SCALE_UP : P::NumericUpdateKind::SCALE_DOWN;
            const auto& table = objectTable("numeric", target.head(), declaration->second);
            for (std::size_t i = 0; i < table.rows.size(); ++i) {
                const auto key = objectRowKey(target.head(), table.rows[i]);
                const auto applies = conjunction({guard, dispatch->matches[i]});
                numeric.push_back({numeric_indices_.at(key), kind, *rhs, applies, owner});
                auto access = endpoint; access.active = applies;
                access.numericWrites.insert(key);
                if (head == "increase" || head == "decrease") { access.additiveWrites.insert(key); }
                temporal_object_accesses_->push_back(std::move(access));
            }
            return true;
        }
        const auto& atom = head == "not" ? expression.list[1] : expression;
        const auto declaration = predicates_.find(atom.head());
        if (declaration == predicates_.end() || derived_predicates_.count(atom.head())) { return false; }
        const auto dispatch = objectDispatchFor(atom, declaration->second, "predicate", environment, step, diagnostics);
        if (!dispatch) { return false; }
        add(model, H::mkOp(H::Op::IMPLIES, {guard, dispatch->defined}));
        objectReadAccess(dispatch->reads, endpoint);
        const auto& table = objectTable("predicate", atom.head(), declaration->second);
        for (std::size_t i = 0; i < table.rows.size(); ++i) {
            const auto key = objectRowKey(atom.head(), table.rows[i]);
            const auto applies = conjunction({guard, dispatch->matches[i]});
            auto& update = updates[atom_targets_.at(key)];
            (head == "not" ? update.delete_conditions : update.add_conditions).push_back(applies);
            auto access = endpoint; access.active = applies;
            (head == "not" ? access.propositionDeletes : access.propositionAdds).insert(key);
            temporal_object_accesses_->push_back(std::move(access));
        }
        return true;
    }

    // Canonical ground fluent identities make interference independent of
    // spelling collisions and time-indexed target names. Read all syntactic
    // disjuncts, including branches that happen to be false in this state.
    bool temporalReads(const Sexp& expression, Environment environment, unsigned step,
                        P::TemporalEndpointAccess& access, Uir::Diagnostics& diagnostics) {
        if (object_mode_) { return objectTemporalReads(expression, std::move(environment), step, access, diagnostics); }
        const auto& head = expression.head();
        if (expression.list.empty()) { return !expression.isAtom(); }
        if (head == "forall" || head == "exists") {
            std::vector<Typed> variables;
            if (expression.list.size() != 3 || !typedList(expression.list[1], 0, true, "temporal read quantifier", variables, diagnostics)) { return false; }
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                return temporalReads(expression.list[2], bound, step, access, diagnostics);
            }, ok);
            return ok;
        }
        if (head == "and" || head == "or" || head == "not" || head == "imply") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!temporalReads(expression.list[i], environment, step, access, diagnostics)) { return false; }
            }
            return true;
        }
        if (numericComparison(expression)) {
            auto condition = numericCondition(expression, environment, step, diagnostics);
            if (!condition) { return false; }
            for (const auto index : condition->reads) { access.numericReads.insert(numeric_ground_.at(index).key); }
            return true;
        }
        if (head == "=") { return true; }
        auto key = atomBase(expression, environment, diagnostics, true);
        if (!key) { return false; }
        if (derived_predicates_.count(head)) {
            const auto base = atomBase(expression, environment, diagnostics);
            if (!base) { return false; }
            const auto state = derived_reads_.find(step);
            if (state == derived_reads_.end()) { diagnostics.error(ErrorCode::E_INTERNAL, "missing derived dependency closure"); return false; }
            const auto found = state->second.find(*base + "@" + std::to_string(step));
            if (found == state->second.end()) { diagnostics.error(ErrorCode::E_INTERNAL, "missing ground derived dependency closure"); return false; }
            for (const auto& symbol : found->second) {
                const auto mapped = temporal_dependency_keys_.find(symbol);
                if (mapped == temporal_dependency_keys_.end()) { diagnostics.error(ErrorCode::E_INTERNAL, "unmapped derived basic dependency"); return false; }
                (mapped->second.first ? access.numericReads : access.propositionReads).insert(mapped->second.second);
            }
        } else { access.propositionReads.insert(*key); }
        return true;
    }

    H::ExprPtr temporalMatch(const P::TemporalHappening& happening, const H::ExprPtr& time) {
        return conjunction({happening.active, H::mkOp(H::Op::EQ, {happening.time, time})});
    }

    std::optional<P::TemporalConditionSamples> temporalSamples(
        const std::vector<TimedFormula>& conditions, unsigned count, Uir::Diagnostics& diagnostics,
        bool definedOnly = false) {
        P::TemporalConditionSamples result;
        std::vector<std::vector<H::ExprPtr>> starts(count), ends(count), intervals(count == 0 ? 0 : count - 1);
        for (const auto& condition : conditions) {
            if (continuous_mode_ && condition.point == TimePoint::INTERVAL) { continue; }
            const unsigned size = condition.point == TimePoint::INTERVAL ? (count == 0 ? 0 : count - 1) : count;
            auto& destination = condition.point == TimePoint::START ? starts
                : condition.point == TimePoint::END ? ends : intervals;
            for (unsigned i = 0; i < size; ++i) {
                auto environment = condition.environment;
                auto term = numericCondition(condition.formula, environment,
                    condition.point == TimePoint::INTERVAL ? i + 1 : i, diagnostics);
                if (!term) { return std::nullopt; }
                destination[i].push_back(definedOnly ? term->defined : P::numericSatisfied(*term));
            }
        }
        const auto finish = [](auto& input, auto& output) {
            if (std::none_of(input.begin(), input.end(), [](const auto& x) { return !x.empty(); })) { return; }
            for (auto& terms : input) { output.push_back(conjunction(std::move(terms))); }
        };
        finish(starts, result.atStart); finish(ends, result.atEnd); finish(intervals, result.overAll);
        return result;
    }

    void groundDurationConditions(const Sexp& expression, const Environment& environment,
        std::vector<TimedFormula>& result, TimePoint point = TimePoint::START) {
        if (!expression.isAtom() && expression.list.empty()) { return; }
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                groundDurationConditions(expression.list[i], environment, result, point);
            }
        } else if (const auto at = timePoint(expression)) {
            groundDurationConditions(expression.list[2], environment, result, *at);
        } else { result.push_back({point, expression, environment}); }
    }

    // At endpoint j, all stored guards use only states up to j. In particular
    // a conditional end effect remembers its own start-state guard; it does
    // not re-evaluate that guard in the end state or a different occurrence.
    H::ExprPtr temporalHistoryGuard(const std::vector<TimedFormula>& conditions,
        const std::vector<P::TemporalHappening>& happenings,
        const P::DurativeOccurrence& occurrence, unsigned endpoint,
        H::ConstraintModel& model, Uir::Diagnostics& diagnostics) {
        std::vector<H::ExprPtr> terms;
        bool hasFlow = false;
        for (const auto& condition : conditions) {
            if (continuous_mode_ && condition.point == TimePoint::INTERVAL) {
                const auto history = continuousHistory(condition, happenings, occurrence, endpoint, diagnostics);
                if (!history) { return nullptr; }
                terms.push_back(history); hasFlow = true; continue;
            }
            for (unsigned i = 0; i <= endpoint; ++i) {
                if (condition.point == TimePoint::INTERVAL && i == endpoint) { continue; }
                auto environment = condition.environment;
                auto value = numericCondition(condition.formula, environment,
                    condition.point == TimePoint::INTERVAL ? i + 1 : i, diagnostics);
                if (!value) { return nullptr; }
                auto applies = condition.point == TimePoint::INTERVAL
                    ? conjunction({happenings[i].active, happenings[i + 1].active,
                        H::mkOp(H::Op::LE, {occurrence.start, happenings[i].time}),
                        H::mkOp(H::Op::LT, {happenings[i].time, occurrence.end})})
                    : temporalMatch(happenings[i], condition.point == TimePoint::START ? occurrence.start : occurrence.end);
                terms.push_back(H::mkOp(H::Op::IMPLIES, {applies, P::numericSatisfied(*value)}));
            }
        }
        auto result = conjunction(std::move(terms));
        if (hasFlow) {
            // Defer the defining formula until every trajectory is declared.
            // Earlier numeric transition builders type-check their full context.
            const auto name = "__pddl_flow_history_" + std::to_string(continuous_history_serial_++);
            declare(model, name);
            const auto identifier = H::mkIdent(name, H::Sort::boolean());
            continuous_history_constraints_.push_back(H::mkOp(H::Op::EQ, {identifier, result}));
            return identifier;
        }
        return result;
    }

    bool temporalEndpointEffects(const Sexp& expression, Environment environment,
        unsigned step, const H::ExprPtr& selected, const H::ExprPtr& guard,
        const std::string& owner, const H::ExprPtr& time,
        H::ConstraintModel& model, std::map<std::string, FluentUpdates>& updates,
        std::vector<P::NumericUpdate>& numeric, std::vector<P::TemporalEndpointAccess>& accesses,
        Uir::Diagnostics& diagnostics) {
        const auto& head = expression.head();
        if (expression.list.empty()) { return !expression.isAtom(); }
        if (head == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!temporalEndpointEffects(expression.list[i], environment, step, selected, guard,
                    owner, time, model, updates, numeric, accesses, diagnostics)) { return false; }
            }
            return true;
        }
        if (head == "forall") {
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "endpoint effect forall", variables, diagnostics)) { return false; }
            bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                return temporalEndpointEffects(expression.list[2], bound, step, selected, guard,
                    owner, time, model, updates, numeric, accesses, diagnostics);
            }, ok);
            return ok;
        }
        if (head == "when") {
            auto condition = numericCondition(expression.list[1], environment, step, diagnostics);
            if (!condition) { return false; }
            add(model, H::mkOp(H::Op::IMPLIES, {guard, condition->defined}));
            P::TemporalEndpointAccess reads;
            reads.active = selected; reads.time = time; reads.owner_id = owner;
            if (!temporalReads(expression.list[1], environment, step, reads, diagnostics)) { return false; }
            accesses.push_back(std::move(reads));
            return temporalEndpointEffects(expression.list[2], environment, step, selected,
                conjunction({guard, P::numericSatisfied(*condition)}), owner, time,
                model, updates, numeric, accesses, diagnostics);
        }
        if (object_mode_) {
            return objectTemporalEffect(expression, environment, step, guard, owner, time,
                model, updates, numeric, diagnostics);
        }
        P::TemporalEndpointAccess access;
        access.active = guard; access.time = time; access.owner_id = owner;
        if (numericUpdate(head)) {
            auto key = numericKey(expression.list[1], environment, diagnostics);
            auto rhs = numericExpression(expression.list[2], environment, step, diagnostics);
            if (!key || !rhs) { return false; }
            const auto kind = head == "assign" ? P::NumericUpdateKind::ASSIGN
                : head == "increase" ? P::NumericUpdateKind::INCREASE
                : head == "decrease" ? P::NumericUpdateKind::DECREASE
                : head == "scale-up" ? P::NumericUpdateKind::SCALE_UP : P::NumericUpdateKind::SCALE_DOWN;
            numeric.push_back({numeric_indices_.at(*key), kind, *rhs, guard, owner});
            access.numericWrites.insert(*key);
            if (head == "increase" || head == "decrease") { access.additiveWrites.insert(*key); }
            for (const auto index : rhs->reads) { access.numericReads.insert(numeric_ground_.at(index).key); }
        } else {
            const auto& atom = head == "not" ? expression.list[1] : expression;
            auto base = effectBase(atom, environment, diagnostics);
            auto key = atomBase(atom, environment, diagnostics, true);
            if (!base || !key) { return false; }
            if (head == "not") {
                updates[*base].delete_conditions.push_back(guard);
                access.propositionDeletes.insert(*key);
            } else {
                updates[*base].add_conditions.push_back(guard);
                access.propositionAdds.insert(*key);
            }
        }
        accesses.push_back(std::move(access));
        return true;
    }

    struct ContinuousEffectInstance {
        P::DurativeOccurrence occurrence;
        Sexp effect;
        Environment environment;
        std::vector<TimedFormula> conditions;
    };
    struct ContinuousConditionInstance {
        P::DurativeOccurrence occurrence;
        TimedFormula condition;
        bool defined_only = false;
    };
    using FlowReplacements = std::unordered_map<std::string, H::ExprPtr>;

    static bool containsElapsedTime(const Sexp& source) {
        if (source.atom == "#t") { return true; }
        for (const auto& child : source.list) { if (containsElapsedTime(child)) { return true; } }
        return false;
    }

    std::optional<Sexp> continuousRate(const Sexp& effect, Uir::Diagnostics& diagnostics) {
        if ((effect.head() != "increase" && effect.head() != "decrease") || effect.list.size() != 3) {
            diagnostics.error(ErrorCode::E_PARSE, "continuous effects require increase/decrease of a numeric fluent");
            return std::nullopt;
        }
        const auto& expression = effect.list[2];
        Sexp rate;
        if (expression.atom == "#t") { rate.atom = "1"; }
        else if (expression.head() == "*" && expression.list.size() == 3
            && (expression.list[1].atom == "#t" || expression.list[2].atom == "#t")) {
            rate = expression.list[expression.list[1].atom == "#t" ? 2 : 1];
        } else {
            diagnostics.error(ErrorCode::E_PARSE, "continuous rate must be #t, (* #t f-exp), or (* f-exp #t)");
            return std::nullopt;
        }
        std::vector<const Sexp*> pending{&rate};
        while (!pending.empty()) {
            const auto* item = pending.back(); pending.pop_back();
            if (item->atom == "#t" || item->atom == "?duration" || item->atom == "total-time") {
                diagnostics.error(ErrorCode::E_PARSE, "continuous f-exp rate must be free of #t, ?duration and total-time");
                return std::nullopt;
            }
            for (const auto& child : item->list) { pending.push_back(&child); }
        }
        return rate;
    }

    // Expand acyclic generated LFP definitions and substitute state templates.
    // Placeholders are distinct from source variables; inner binders still
    // shadow names explicitly. A cache preserves sharing of each expression.
    static H::ExprPtr flowRewrite(const H::ExprPtr& expression, const FlowReplacements& replacements) {
        std::unordered_map<const H::Expr*, H::ExprPtr> cache;
        std::function<H::ExprPtr(const H::ExprPtr&)> visit = [&](const H::ExprPtr& term) -> H::ExprPtr {
            if (!term) { return term; }
            const auto prior = cache.find(term.get());
            if (prior != cache.end()) { return prior->second; }
            if (term->kind == H::ExprKind::IDENT || term->kind == H::ExprKind::BOUND_VAR) {
                const auto found = replacements.find(term->name);
                if (found != replacements.end()) {
                    const auto result = visit(found->second); cache.emplace(term.get(), result); return result;
                }
            }
            if (term->args.empty()) { return term; }
            auto result = std::make_shared<H::Expr>(*term);
            if (term->kind == H::ExprKind::FORALL || term->kind == H::ExprKind::EXISTS) {
                auto inner = replacements;
                for (const auto& binder : term->binders) { inner.erase(binder.name); }
                for (auto& argument : result->args) { argument = flowRewrite(argument, inner); }
            } else { for (auto& argument : result->args) { argument = visit(argument); } }
            cache.emplace(term.get(), result); return result;
        };
        return visit(expression);
    }

    P::NumericStateCell numericPostAt(std::size_t index, unsigned step) const {
        const auto name = numeric_ground_.at(index).target + "@post" + std::to_string(step);
        return {H::mkIdent(name, H::Sort::real()), H::mkIdent(name + "@defined", H::Sort::boolean())};
    }
    static std::string flowTimeName(unsigned step) { return "__pddl_flow_time_" + std::to_string(step); }
    static std::string flowVariableName(unsigned step, std::size_t index) {
        return "__pddl_flow_value_" + std::to_string(step) + "_" + std::to_string(index);
    }
    static std::string flowFunctionName(unsigned step, std::size_t index) {
        return "__pddl_flow_" + std::to_string(step) + "_" + std::to_string(index);
    }

    FlowReplacements flowStateSubstitution(unsigned step, const H::ExprPtr& time = nullptr,
                                           bool post_endpoint = false) {
        FlowReplacements result;
        const auto derived = continuous_derived_.find(step + 1);
        if (derived != continuous_derived_.end()) { result = derived->second; }
        for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
            const auto original = numericAt(index, step + 1);
            const auto initial = numericPostAt(index, step);
            result[original.value->name] = post_endpoint ? initial.value
                : time ? H::mkApply(flowFunctionName(step, index), H::Sort::real(), {time})
                       : H::mkBoundVar(flowVariableName(step, index), H::Sort::real());
            result[original.defined->name] = initial.defined;
        }
        for (std::size_t index = 0; index < object_ground_.size(); ++index) {
            const auto original = objectAt(index, step + 1), post = objectPostAt(index, step);
            result[original.value->name] = post.value;
            result[original.defined->name] = post.defined;
        }
        return result;
    }

    std::optional<P::NumericCondition> flowCondition(const TimedFormula& condition, unsigned step,
        Uir::Diagnostics& diagnostics, const H::ExprPtr& time = nullptr, bool post_endpoint = false) {
        auto environment = condition.environment;
        auto source = numericCondition(condition.formula, environment, step + 1, diagnostics);
        if (!source) { return std::nullopt; }
        const auto substitution = flowStateSubstitution(step, time, post_endpoint);
        source->value = flowRewrite(source->value, substitution);
        source->defined = flowRewrite(source->defined, substitution);
        return source;
    }

    static H::ExprPtr flowCovers(const P::DurativeOccurrence& occurrence,
        const P::TemporalHappening& left, const P::TemporalHappening& right) {
        return conjunction({occurrence.active, left.active, right.active,
            H::mkOp(H::Op::LE, {occurrence.start, left.time}),
            H::mkOp(H::Op::LE, {right.time, occurrence.end})});
    }

    H::ExprPtr continuousHistory(const TimedFormula& condition,
        const std::vector<P::TemporalHappening>& happenings, const P::DurativeOccurrence& occurrence,
        unsigned endpoint, Uir::Diagnostics& diagnostics) {
        std::vector<H::ExprPtr> terms;
        for (unsigned step = 0; step < endpoint; ++step) {
            const auto time = H::mkBoundVar(flowTimeName(step), H::Sort::real());
            const auto value = flowCondition(condition, step, diagnostics, time);
            if (!value) { return nullptr; }
            terms.push_back(H::mkOp(H::Op::IMPLIES, {flowCovers(occurrence, happenings[step], happenings[step + 1]),
                H::mkForall({{time->name, H::Sort::real()}}, H::mkOp(H::Op::IMPLIES, {
                    conjunction({H::mkOp(H::Op::LT, {happenings[step].time, time}),
                                 H::mkOp(H::Op::LT, {time, happenings[step + 1].time})}), P::numericSatisfied(*value)}))}));
        }
        // Discrete jumps strictly inside an occurrence are observable from
        // either adjacent side. Only that occurrence's own endpoints are open.
        for (unsigned step = 0; step <= endpoint; ++step) {
            auto environment = condition.environment;
            const auto before = numericCondition(condition.formula, environment, step, diagnostics);
            const auto after = flowCondition(condition, step, diagnostics, nullptr, true);
            if (!before || !after) { return nullptr; }
            const auto internal = conjunction({happenings[step].active,
                H::mkOp(H::Op::LT, {occurrence.start, happenings[step].time}),
                H::mkOp(H::Op::LT, {happenings[step].time, occurrence.end})});
            terms.push_back(H::mkOp(H::Op::IMPLIES, {internal,
                conjunction({P::numericSatisfied(*before), P::numericSatisfied(*after)})}));
        }
        return conjunction(std::move(terms));
    }

    bool appendContinuousFlows(H::ConstraintModel& model,
        const std::vector<P::TemporalHappening>& happenings,
        const std::vector<ContinuousEffectInstance>& effects,
        const std::vector<ContinuousConditionInstance>& conditions, Uir::Diagnostics& diagnostics) {
        for (unsigned step = 0; step < happenings.size(); ++step) {
            const bool has_interval = step + 1 < happenings.size();
            const auto enabled = has_interval ? happenings[step + 1].active : H::mkBool(false);
            for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
                const auto post = numericPostAt(index, step), next = numericAt(index, step + 1);
                add(model, H::mkOp(H::Op::IMPLIES, {negation(enabled), conjunction({
                    H::mkOp(H::Op::EQ, {post.value, next.value}), H::mkOp(H::Op::EQ, {post.defined, next.defined})})}));
            }
            const auto post_substitution = flowStateSubstitution(step, nullptr, true);
            for (const auto& atom : atoms_) {
                const auto target = atom.target_base + "@post" + std::to_string(step);
                declare(model, target, "post[" + std::to_string(step) + "]::" + atom.source_label);
                addAxiom(model, H::mkOp(H::Op::EQ, {H::mkIdent(target, H::Sort::boolean()),
                    flowRewrite(atomAt(atom.target_base, step + 1), post_substitution)}));
            }
            if (!has_interval) { continue; }
            P::ContinuousSegment segment;
            segment.enabled = enabled; segment.start = happenings[step].time; segment.end = happenings[step + 1].time;
            segment.time_variable = flowTimeName(step);
            segment.derivative_domain = P::FlowDerivativeDomain::CLOSED_ONE_SIDED;
            const auto substitution = flowStateSubstitution(step);
            struct ObjectFlowDestination {
                H::ExprPtr active;
                std::map<std::size_t, H::ExprPtr> matches;
            };
            std::map<const ContinuousEffectInstance*, ObjectFlowDestination> objectDestinations;
            if (object_mode_) {
                for (const auto& effect : effects) {
                    const auto& target = effect.effect.list[1];
                    const auto declaration = numeric_functions_.find(target.head());
                    if (declaration == numeric_functions_.end()) { return false; }
                    const auto dispatch = objectDispatchFor(target, declaration->second, "numeric",
                        effect.environment, step + 1, diagnostics);
                    if (!dispatch) { return false; }
                    std::vector<H::ExprPtr> history;
                    temporal_duration_ = H::mkOp(H::Op::SUB, {effect.occurrence.end, effect.occurrence.start});
                    for (const auto& condition : effect.conditions) {
                        for (unsigned at = 0; at < happenings.size(); ++at) {
                            auto environment = condition.environment;
                            const auto value = numericCondition(condition.formula, environment, at, diagnostics);
                            if (!value) { return false; }
                            history.push_back(H::mkOp(H::Op::IMPLIES, {
                                temporalMatch(happenings[at], effect.occurrence.start), P::numericSatisfied(*value)}));
                        }
                    }
                    auto& destination = objectDestinations[&effect];
                    destination.active = conjunction({flowCovers(effect.occurrence, happenings[step], happenings[step + 1]),
                        conjunction(std::move(history))});
                    const auto& table = objectTable("numeric", target.head(), declaration->second);
                    for (std::size_t row = 0; row < table.rows.size(); ++row) {
                        destination.matches.emplace(numeric_indices_.at(objectRowKey(target.head(), table.rows[row])),
                            flowRewrite(dispatch->matches[row], substitution));
                    }
                    segment.invariants.push_back({destination.active,
                        {H::mkBool(true), flowRewrite(dispatch->defined, substitution), {}}, true, true});
                }
            }
            for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
                std::vector<H::ExprPtr> terms, defined, writes;
                for (const auto& effect : effects) {
                    H::ExprPtr objectTargetMatch;
                    if (object_mode_) {
                        const auto& destination = objectDestinations.at(&effect);
                        const auto match = destination.matches.find(index);
                        if (match == destination.matches.end()) { continue; }
                        objectTargetMatch = match->second;
                    } else {
                        const auto target = numericKey(effect.effect.list[1], effect.environment, diagnostics);
                        if (!target) { return false; }
                        if (*target != numeric_ground_[index].key) { continue; }
                    }
                    const auto syntax = continuousRate(effect.effect, diagnostics);
                    if (!syntax) { return false; }
                    auto rate = numericExpression(*syntax, effect.environment, step + 1, diagnostics);
                    if (!rate) { return false; }
                    rate->value = flowRewrite(rate->value, substitution);
                    rate->defined = flowRewrite(rate->defined, substitution);
                    if (effect.effect.head() == "decrease") { rate->value = H::mkOp(H::Op::NEG, {rate->value}); }
                    // A causal conditional rate remembers its own occurrence's
                    // start guard, evaluated in the pre-happening source state.
                    // Definedness and syntactic guard reads are checked separately
                    // at that start even if its value is false.
                    std::vector<H::ExprPtr> history;
                    temporal_duration_ = H::mkOp(H::Op::SUB, {effect.occurrence.end, effect.occurrence.start});
                    for (const auto& condition : effect.conditions) {
                        for (unsigned at = 0; at < happenings.size(); ++at) {
                            auto environment = condition.environment;
                            const auto value = numericCondition(condition.formula, environment, at, diagnostics);
                            if (!value) { return false; }
                            history.push_back(H::mkOp(H::Op::IMPLIES, {
                                temporalMatch(happenings[at], effect.occurrence.start), P::numericSatisfied(*value)}));
                        }
                    }
                    const auto active = object_mode_ ? conjunction({objectDestinations.at(&effect).active, objectTargetMatch})
                        : conjunction({flowCovers(effect.occurrence, happenings[step], happenings[step + 1]), conjunction(std::move(history))});
                    writes.push_back(active);
                    terms.push_back(H::mkOp(H::Op::ITE, {active, rate->value, H::mkReal("0")}));
                    defined.push_back(H::mkOp(H::Op::IMPLIES, {active, rate->defined}));
                }
                const auto rate = terms.empty() ? H::mkReal("0") : terms.size() == 1 ? terms.front() : H::mkOp(H::Op::ADD, terms);
                segment.coordinates.push_back({flowFunctionName(step, index), flowVariableName(step, index),
                    numericPostAt(index, step), numericAt(index, step + 1), disjunction(std::move(writes)),
                    {rate, conjunction(std::move(defined)), {}}});
            }
            for (const auto& condition : conditions) {
                temporal_duration_ = H::mkOp(H::Op::SUB, {condition.occurrence.end, condition.occurrence.start});
                auto value = flowCondition(condition.condition, step, diagnostics);
                if (!value) { return false; }
                if (condition.defined_only) { value->value = H::mkBool(true); }
                segment.invariants.push_back({flowCovers(condition.occurrence, happenings[step], happenings[step + 1]), *value, false, false});
            }
            auto encoded = P::encodeContinuousSegment(model, segment, diagnostics);
            if (!encoded) { return false; }
            for (const auto& function : encoded->trajectories) {
                model.funs.push_back(function);
            }
            for (const auto& constraint : encoded->constraints) { add(model, constraint); }
            for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
                const auto source = "flow[" + std::to_string(step) + "]::" + numeric_ground_[index].label;
                const auto target = flowFunctionName(step, index);
                source_signature_.symbols.push_back({source, S::SymbolKind::FUNCTION, {H::Sort::real()}, H::Sort::real()});
                symbol_map_.push_back({source, target}); projection_.observables.push_back({source, target, S::ProjectionKind::DIRECT});
            }
            if (object_mode_) {
                const auto point = H::mkBoundVar(flowTimeName(step), H::Sort::real());
                const auto inside = conjunction({enabled, H::mkOp(H::Op::LE, {segment.start, point}),
                    H::mkOp(H::Op::LE, {point, segment.end})});
                for (std::size_t i = 0; i < object_ground_.size(); ++i) {
                    const auto post = objectPostAt(i, step);
                    for (bool defined : {false, true}) {
                        H::FunDecl function;
                        function.name = object_ground_[i].target + "@flow" + std::to_string(step)
                            + (defined ? "@defined" : "");
                        function.params = {H::Sort::real()};
                        function.result = defined ? H::Sort::boolean() : H::Sort::integer();
                        function.binders = {{point->name, H::Sort::real()}};
                        function.body = defined ? conjunction({inside, post.defined})
                            : H::mkOp(H::Op::ITE, {inside, post.value, H::mkInt(0)});
                        const auto source = "flow[" + std::to_string(step) + "]::"
                            + (defined ? "defined(object::" + object_ground_[i].label + ")"
                                       : "object-code::" + object_ground_[i].label);
                        source_signature_.symbols.push_back({source,
                            defined ? S::SymbolKind::RELATION : S::SymbolKind::FUNCTION,
                            {H::Sort::real()}, function.result});
                        symbol_map_.push_back({source, function.name});
                        projection_.observables.push_back({source, function.name, S::ProjectionKind::DIRECT});
                        model.funs.push_back(std::move(function));
                    }
                }
            }
            // Derived facts can change inside a segment even though no basic
            // Boolean fluent changes. Expose the exact pointwise finite LFP.
            const auto point = H::mkBoundVar(flowTimeName(step), H::Sort::real());
            const auto at_point = flowStateSubstitution(step, point);
            for (const auto& atom : atoms_) {
                if (!derived_predicates_.count(atom.predicate)) { continue; }
                H::FunDecl function;
                function.name = atom.target_base + "@flow" + std::to_string(step);
                function.params = {H::Sort::real()}; function.result = H::Sort::boolean();
                function.binders = {{point->name, H::Sort::real()}};
                function.body = conjunction({enabled, H::mkOp(H::Op::LE, {segment.start, point}),
                    H::mkOp(H::Op::LE, {point, segment.end}), flowRewrite(atomAt(atom.target_base, step + 1), at_point)});
                const auto source = "flow[" + std::to_string(step) + "]::" + atom.source_label;
                source_signature_.symbols.push_back({source, S::SymbolKind::RELATION, {H::Sort::real()}, H::Sort::boolean()});
                symbol_map_.push_back({source, function.name}); projection_.observables.push_back({source, function.name, S::ProjectionKind::DIRECT});
                model.funs.push_back(std::move(function));
            }
        }
        for (const auto& condition : conditions) {
            temporal_duration_ = H::mkOp(H::Op::SUB, {condition.occurrence.end, condition.occurrence.start});
            for (unsigned step = 0; step < happenings.size(); ++step) {
                auto environment = condition.condition.environment;
                auto before = numericCondition(condition.condition.formula, environment, step, diagnostics);
                auto after = flowCondition(condition.condition, step, diagnostics, nullptr, true);
                if (!before || !after) { return false; }
                if (condition.defined_only) { before->value = after->value = H::mkBool(true); }
                const auto internal = conjunction({condition.occurrence.active, happenings[step].active,
                    H::mkOp(H::Op::LT, {condition.occurrence.start, happenings[step].time}),
                    H::mkOp(H::Op::LT, {happenings[step].time, condition.occurrence.end})});
                add(model, H::mkOp(H::Op::IMPLIES, {internal,
                    conjunction({P::numericSatisfied(*before), P::numericSatisfied(*after)})}));
            }
        }
        temporal_duration_.reset();
        for (const auto& constraint : continuous_history_constraints_) { addAxiom(model, constraint); }
        // Full source observation signature: pre/post cells (including partial
        // numeric definedness), occurrence coordinates, and entire trajectories.
        std::set<std::string> projected;
        for (const auto& observable : projection_.observables) { projected.insert(observable.source_name); }
        for (const auto& entry : symbol_map_) {
            if (projected.insert(entry.source).second) {
                projection_.observables.push_back({entry.source, entry.target, S::ProjectionKind::DIRECT});
            }
        }
        return true;
    }

    H::ConstraintModelPtr buildTemporal(Uir::Diagnostics& diagnostics, Uir::TranslationReport& report) {
        if (!requireFeature(":durative-actions", "durative action", diagnostics)) { return nullptr; }
        // Numeric state cells also express costs and duration-dependent updates.
        numeric_mode_ = true;
        if (!numeric_functions_.empty() && !featureEnabled(":fluents") && !featureEnabled(":action-costs")
            && !requireFeature(":fluents", "numeric state in a durative domain", diagnostics)) { return nullptr; }
        if (!initializeObjects(diagnostics) || !initializeNumeric(diagnostics)
            || !validatePreferenceSchemas(diagnostics)
            || !validateDerivedBodies(diagnostics)) { return nullptr; }
        for (const auto& action : actions_) {
            Environment types;
            for (const auto& parameter : action.params) { types.emplace(parameter.name, parameter.type); }
            temporal_duration_allowed_ = action.durative;
            if (action.durative) {
                if (!validateDuration(action.duration, types, diagnostics)
                    || (action.has_precondition && !validateTimed(action.precondition, types, false, diagnostics))
                    || (action.has_effect && !validateTimed(action.effect, types, true, diagnostics))) { return nullptr; }
            } else if ((action.has_precondition && !validateSchema(action.precondition, types, false, diagnostics))
                       || (action.has_effect && !validateSchema(action.effect, types, true, diagnostics))) { return nullptr; }
        }
        temporal_duration_allowed_ = false;
        if (!validateSchema(goal_, {}, false, diagnostics)) { return nullptr; }
        for (const auto& event : timed_initial_) {
            if (!validateApplication(event.literal, {}, predicates_, diagnostics)) { return nullptr; }
        }
        if (timed_initial_.size() > UINT_MAX - 1
            || horizon_ > (UINT_MAX - 1 - timed_initial_.size()) / 2) {
            diagnostics.error(ErrorCode::E_TYPE, "temporal horizon and timed events overflow the happening index"); return nullptr;
        }
        const unsigned count = horizon_ * 2 + static_cast<unsigned>(timed_initial_.size());
        auto model = std::make_shared<H::ConstraintModel>();
        object_context_ = model.get();
        temporal_object_updates_.resize(count);
        sparse_fluents_ = false;
        groundAtoms(); groundActions();
        if (object_mode_ && !prepareObjectDerivedBodies(diagnostics)) { return nullptr; }
        if (!initialState(static_initial_, diagnostics, true)) { return nullptr; }
        for (unsigned step = 0; step <= count; ++step) {
            if (object_mode_) {
                declareObjectState(*model, step);
                if (step < count) { declareObjectState(*model, step, true); }
            }
            for (const auto& atom : atoms_) {
                const auto target = atom.target_base + "@" + std::to_string(step);
                declare(*model, target, "state[" + std::to_string(step) + "]::" + atom.source_label);
                temporal_dependency_keys_[target] = {false, canonical(atom.predicate, atom.args)};
            }
            for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
                const auto cell = numericAt(index, step);
                declare(*model, cell.value->name, "state[" + std::to_string(step) + "]::" + numeric_ground_[index].label, H::Sort::real());
                declare(*model, cell.defined->name, (continuous_mode_ || object_mode_)
                    ? std::optional<std::string>("state[" + std::to_string(step) + "]::defined::" + numeric_ground_[index].label)
                    : std::nullopt);
                if (continuous_mode_ && step < count) {
                    const auto post = numericPostAt(index, step);
                    const auto source = "post[" + std::to_string(step) + "]::";
                    declare(*model, post.value->name, source + numeric_ground_[index].label, H::Sort::real());
                    declare(*model, post.defined->name, source + "defined::" + numeric_ground_[index].label);
                }
                temporal_dependency_keys_[cell.value->name] = {true, numeric_ground_[index].key};
                temporal_dependency_keys_[cell.defined->name] = {true, numeric_ground_[index].key};
            }
            if (!appendDerivedAt(*model, step, diagnostics)) { return nullptr; }
        }
        if (object_mode_) {
            std::vector<P::ObjectStateCell> initial;
            for (std::size_t i = 0; i < object_ground_.size(); ++i) { initial.push_back(objectAt(i, 0)); }
            const auto relation = P::initialObjectState(*model, object_universe_, initial, object_initial_, diagnostics);
            if (!relation) { return nullptr; }
            for (const auto& term : relation->constraints) { add(*model, term); }
        }
        for (const auto& atom : atoms_) {
            if (derived_predicates_.count(atom.predicate)) { continue; }
            auto value = atomAt(atom.target_base, 0);
            add(*model, static_initial_.count(canonical(atom.predicate, atom.args)) ? value : negation(value));
        }
        for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
            const auto cell = numericAt(index, 0);
            const auto initial = numeric_initial_.find(numeric_ground_[index].key);
            add(*model, H::mkOp(H::Op::EQ, {cell.defined, H::mkBool(initial != numeric_initial_.end())}));
            add(*model, H::mkOp(H::Op::EQ, {cell.value, initial == numeric_initial_.end() ? H::mkReal("0") : initial->second}));
        }
        std::vector<P::TemporalHappening> happenings;
        for (unsigned step = 0; step < count; ++step) {
            const auto base = "__pddl_happening_" + std::to_string(step);
            declare(*model, base + "_active"); declare(*model, base + "_time", std::nullopt, H::Sort::real());
            happenings.push_back({H::mkIdent(base + "_active", H::Sort::boolean()), H::mkIdent(base + "_time", H::Sort::real())});
        }
        trajectory_happenings_ = happenings;
        if (preferences_present_ || !trajectory_constraints_.empty()) {
            // AI2009 Definition 1: the initial state at t=0 persists for a
            // positive interval; no source PDDL3 happening occurs at zero.
            for (const auto& happening : happenings) {
                addAxiom(*model,H::mkOp(H::Op::IMPLIES,{happening.active,
                    H::mkOp(H::Op::GT,{happening.time,H::mkReal("0")})}));
            }
        }
        const auto order = P::encodeHappeningOrder(happenings, diagnostics);
        if (!order) { return nullptr; }
        for (const auto& constraint : *order) { addAxiom(*model, constraint); }
        H::ExprPtr lastActionEnd = H::mkReal("0");
        temporal_total_time_ = lastActionEnd;
        std::vector<std::vector<H::ExprPtr>> occupied(count);
        std::vector<std::map<std::string, FluentUpdates>> updates(count);
        std::vector<std::vector<P::NumericUpdate>> numeric(count);
        std::vector<P::TemporalEndpointAccess> accesses;
        temporal_object_accesses_ = &accesses;
        std::vector<ContinuousEffectInstance> continuousEffects;
        std::vector<ContinuousConditionInstance> continuousConditions;
        std::vector<P::TimedInitialLiteral> timedEvents;
        std::vector<std::string> timedTargets;
        Environment noVariables;
        for (const auto& event : timed_initial_) {
            const auto key = atomBase(event.literal, noVariables, diagnostics, true);
            const auto target = atomBase(event.literal, noVariables, diagnostics);
            if (!key || !target) { return nullptr; }
            timedEvents.push_back({event.time, *key, event.value});
            timedTargets.push_back(*target);
        }
        const auto fixed = P::encodeTimedInitialLiterals(happenings, timedEvents, "__pddl_til_", diagnostics);
        if (!fixed) { return nullptr; }
        for (const auto& constraint : fixed->constraints) { addAxiom(*model, constraint); }
        accesses.insert(accesses.end(), fixed->accesses.begin(), fixed->accesses.end());
        for (std::size_t event = 0; event < timedEvents.size(); ++event) {
            for (unsigned step = 0; step < count; ++step) {
                const auto match = fixed->matches[event][step];
                occupied[step].push_back(match);
                auto& update = updates[step][timedTargets[event]];
                (timedEvents[event].value ? update.add_conditions : update.delete_conditions).push_back(match);
            }
        }
        H::ExprPtr previousActive, previousStart;
        // A simple happening is a set of ground action names (Fox--Long,
        // Definition 11). Repeated trace entries at the same time denote
        // one instantaneous event. Durative occurrences retain their own
        // identity and history; they are deliberately not coalesced here.
        std::vector<std::vector<std::pair<H::ExprPtr, H::ExprPtr>>>
            simpleOccurrences(ground_actions_.size());
        for (unsigned slot = 0; slot < horizon_; ++slot) {
            const auto base = "__pddl_occurrence_" + std::to_string(slot);
            declare(*model, base + "_active");
            declare(*model, base + "_start", "plan[" + std::to_string(slot) + "]::start", H::Sort::real());
            declare(*model, base + "_end", "plan[" + std::to_string(slot) + "]::end", H::Sort::real());
            projection_.observables.push_back({"plan[" + std::to_string(slot) + "]::start", base + "_start", S::ProjectionKind::DIRECT});
            projection_.observables.push_back({"plan[" + std::to_string(slot) + "]::end", base + "_end", S::ProjectionKind::DIRECT});
            P::DurativeOccurrence occurrence{H::mkIdent(base + "_active", H::Sort::boolean()),
                H::mkIdent(base + "_start", H::Sort::real()), H::mkIdent(base + "_end", H::Sort::real())};
            for (const std::string endpoint : {"_start", "_end"}) {
                const auto target = base + endpoint;
                declare(*model, target + "_numerator", std::nullopt, H::Sort::integer());
                declare(*model, target + "_denominator", std::nullopt, H::Sort::integer());
                const P::RationalTimeCoordinate rational{H::mkIdent(target, H::Sort::real()),
                    H::mkIdent(target + "_numerator", H::Sort::integer()),
                    H::mkIdent(target + "_denominator", H::Sort::integer())};
                const auto constraints = P::encodeRationalTime(rational, occurrence.active, diagnostics);
                if (!constraints) { return nullptr; }
                for (const auto& constraint : *constraints) { addAxiom(*model, constraint); }
            }
            if (previousActive) {
                addAxiom(*model, H::mkOp(H::Op::IMPLIES, {occurrence.active,
                    conjunction({previousActive, H::mkOp(H::Op::LE, {previousStart, occurrence.start})})}));
            }
            previousActive = occurrence.active; previousStart = occurrence.start;
            lastActionEnd = H::mkOp(H::Op::ITE, {conjunction({occurrence.active,
                H::mkOp(H::Op::GT, {occurrence.end, lastActionEnd})}), occurrence.end, lastActionEnd});
            temporal_duration_ = H::mkOp(H::Op::SUB, {occurrence.end, occurrence.start});
            std::vector<H::ExprPtr> choices;
            S::ChoiceObservable choice;
            choice.source_name = "plan[" + std::to_string(slot) + "]";
            choice.omit_label = "__pddl_padding_noop";
            const auto noop = base + "_unused";
            declare(*model, noop);
            addAxiom(*model, H::mkOp(H::Op::EQ, {H::mkIdent(noop, H::Sort::boolean()), negation(occurrence.active)}));
            choice.alternatives.push_back({choice.omit_label, noop});
            for (std::size_t index = 0; index < ground_actions_.size(); ++index) {
                const auto& action = ground_actions_[index];
                const auto selectedName = base + "_action_" + std::to_string(index);
                declare(*model, selectedName, "choice[" + std::to_string(slot) + "]::" + action.source_label);
                const auto selected = H::mkIdent(selectedName, H::Sort::boolean());
                choices.push_back(selected); choice.alternatives.push_back({action.source_label, selectedName});
                H::ExprPtr executes = selected;
                if (!action.schema->durative) {
                    std::vector<H::ExprPtr> earlier;
                    for (const auto& prior : simpleOccurrences[index]) {
                        earlier.push_back(conjunction({prior.first,
                            H::mkOp(H::Op::EQ, {prior.second, occurrence.start})}));
                    }
                    executes = conjunction({selected, negation(disjunction(std::move(earlier)))});
                    simpleOccurrences[index].emplace_back(selected, occurrence.start);
                }
                auto environment = actionEnvironment(action);
                P::DurativeOccurrence instance{selected, occurrence.start, occurrence.end};
                if (!appendTemporalPreferenceInstances(*action.schema,environment,selectedName,executes,instance,accesses,diagnostics)) { return nullptr; }
                std::vector<TimedFormula> conditions;
                std::vector<TimedEffect> effects;
                if (action.schema->durative) {
                    if ((action.schema->has_precondition && !groundTimedConditions(action.schema->precondition, environment, conditions, diagnostics))
                        || (action.schema->has_effect && !groundTimedEffects(action.schema->effect, environment, {}, effects, diagnostics))) { return nullptr; }
                } else {
                    add(*model, H::mkOp(H::Op::IMPLIES, {selected, H::mkOp(H::Op::EQ, {occurrence.start, occurrence.end})}));
                    if (action.schema->has_precondition) { conditions.push_back({TimePoint::START, action.schema->precondition, environment}); }
                    if (action.schema->has_effect) { effects.push_back({TimePoint::START, action.schema->effect, environment, {}}); }
                }
                if (action.schema->durative) { groundDurationConditions(action.schema->duration, environment, conditions); }
                if (continuous_mode_) {
                    for (const auto& condition : conditions) {
                        if (condition.point == TimePoint::INTERVAL) { continuousConditions.push_back({instance, condition, false}); }
                    }
                    for (const auto& effect : effects) {
                        if (effect.point == TimePoint::FLOW) { continuousEffects.push_back({instance, effect.effect, effect.environment, effect.conditions}); }
                        for (const auto& condition : effect.conditions) {
                            if (condition.point == TimePoint::INTERVAL) { continuousConditions.push_back({instance, condition, true}); }
                        }
                    }
                }
                auto samples = temporalSamples(conditions, count, diagnostics);
                if (!samples) { return nullptr; }
                auto encoded = P::encodeDurativeOccurrence(happenings, instance, *samples, diagnostics);
                if (!encoded) { return nullptr; }
                for (const auto& constraint : encoded->constraints) { add(*model, constraint); }
                // Conditional guards must be well-defined even when false.
                // Their truth controls their effects, not action applicability.
                for (const auto& effect : effects) {
                    const auto defined = temporalSamples(effect.conditions, count, diagnostics, true);
                    if (!defined) { return nullptr; }
                    const auto guardDefined = P::encodeDurativeOccurrence(happenings, instance, *defined, diagnostics);
                    if (!guardDefined) { return nullptr; }
                    for (const auto& constraint : guardDefined->constraints) { add(*model, constraint); }
                }
                for (unsigned step = 0; step < count; ++step) {
                    auto start = conjunction({executes, temporalMatch(happenings[step], occurrence.start)});
                    auto end = conjunction({selected, temporalMatch(happenings[step], occurrence.end)});
                    occupied[step].push_back(start);
                    if (action.schema->durative) { occupied[step].push_back(end); }
                    const auto ownerStart = selectedName + "_start", ownerEnd = selectedName + "_end";
                    for (const auto& condition : conditions) {
                        if (condition.point == TimePoint::INTERVAL) { continue; }
                        P::TemporalEndpointAccess access;
                        access.active = condition.point == TimePoint::START ? start : end;
                        access.time = happenings[step].time;
                        access.owner_id = condition.point == TimePoint::START ? ownerStart : ownerEnd;
                        if (!temporalReads(condition.formula, condition.environment, step, access, diagnostics)) { return nullptr; }
                        accesses.push_back(std::move(access));
                    }
                    for (const auto& effect : effects) {
                        for (const auto& condition : effect.conditions) {
                            if (condition.point == TimePoint::INTERVAL) { continue; }
                            P::TemporalEndpointAccess access;
                            access.active = condition.point == TimePoint::START ? start : end;
                            access.time = happenings[step].time;
                            access.owner_id = condition.point == TimePoint::START ? ownerStart : ownerEnd;
                            if (!temporalReads(condition.formula, condition.environment, step, access, diagnostics)) { return nullptr; }
                            accesses.push_back(std::move(access));
                        }
                        if (effect.point == TimePoint::FLOW) { continue; }
                        const auto history = temporalHistoryGuard(effect.conditions, happenings, instance, step, *model, diagnostics);
                        if (!history) { return nullptr; }
                        const auto endpoint = effect.point == TimePoint::START ? start : end;
                        if (!temporalEndpointEffects(effect.effect, effect.environment, step, endpoint,
                            conjunction({endpoint, history}), effect.point == TimePoint::START ? ownerStart : ownerEnd,
                            happenings[step].time, *model, updates[step], numeric[step], accesses, diagnostics)) { return nullptr; }
                    }
                }
            }
            projection_.choices.push_back(std::move(choice));
            addAxiom(*model, H::mkOp(H::Op::EQ, {occurrence.active, disjunction(choices)}));
            // Linear sequential counter for at most one schema per occurrence.
            H::ExprPtr seen = H::mkBool(false);
            for (std::size_t index = 0; index < choices.size(); ++index) {
                addAxiom(*model, negation(conjunction({seen, choices[index]})));
                const auto name = base + "_prefix_" + std::to_string(index);
                declare(*model, name);
                const auto prefix = H::mkIdent(name, H::Sort::boolean());
                addAxiom(*model, H::mkOp(H::Op::EQ, {prefix, disjunction({seen, choices[index]})}));
                seen = prefix;
            }
        }
        temporal_duration_.reset();
        for (unsigned step = 0; step < count; ++step) {
            addAxiom(*model, H::mkOp(H::Op::EQ, {happenings[step].active, disjunction(std::move(occupied[step]))}));
            for (const auto& atom : atoms_) {
                if (derived_predicates_.count(atom.predicate)) { continue; }
                const auto now = atomAt(atom.target_base, step);
                const auto next = atomAt(atom.target_base, step + 1);
                const auto found = updates[step].find(atom.target_base);
                auto successor = now;
                if (found != updates[step].end()) {
                    successor = disjunction({disjunction(found->second.add_conditions),
                        conjunction({now, negation(disjunction(found->second.delete_conditions))})});
                }
                add(*model, H::mkOp(H::Op::EQ, {next, successor}));
            }
            if (object_mode_) {
                std::vector<P::ObjectStateCell> before, after;
                for (std::size_t i = 0; i < object_ground_.size(); ++i) {
                    before.push_back(objectAt(i, step)); after.push_back(objectPostAt(i, step));
                }
                const auto relation = P::buildObjectTransition(*model, object_universe_, before, after,
                    temporal_object_updates_[step], P::ObjectAssignmentPolicy::SINGLE_WRITER, diagnostics);
                if (!relation) { return nullptr; }
                for (const auto& term : relation->constraints) { add(*model, term); }
                for (std::size_t i = 0; i < object_ground_.size(); ++i) {
                    const auto post = objectPostAt(i, step), next = objectAt(i, step + 1);
                    add(*model, H::mkOp(H::Op::EQ, {next.value, post.value}));
                    add(*model, H::mkOp(H::Op::EQ, {next.defined, post.defined}));
                }
            }
            std::vector<P::NumericStateCell> before, after;
            for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
                before.push_back(numericAt(index, step));
                after.push_back(continuous_mode_ ? numericPostAt(index, step) : numericAt(index, step + 1));
            }
            const auto transition = P::buildNumericTransition(*model, before, after, numeric[step], diagnostics);
            if (!transition) { return nullptr; }
            for (const auto& constraint : transition->constraints) { add(*model, constraint); }
        }
        if (continuous_mode_ && !appendContinuousFlows(*model, happenings, continuousEffects, continuousConditions, diagnostics)) { return nullptr; }
        const auto mutex = P::encodeTemporalInterference(accesses, diagnostics);
        if (!mutex) { return nullptr; }
        for (const auto& constraint : *mutex) { add(*model, constraint); }
        Environment empty;
        std::vector<H::ExprPtr> goals;
        for (unsigned step = 0; step <= count; ++step) {
            auto goal = formula(goal_, empty, step, diagnostics);
            if (!goal) { return nullptr; }
            goals.push_back(goal);
        }
        const auto stable = P::encodeStableGoalMakespan(happenings, goals, lastActionEnd, diagnostics);
        if (!stable) { return nullptr; }
        for (const auto& constraint : stable->constraints) { add(*model, constraint); }
        temporal_total_time_ = stable->time;
        if (!appendClassicalTrajectory(*model,diagnostics)) { return nullptr; }
        if (!metric_direction_.empty() || anonymous_preferences_) {
            temporal_metric_allowed_ = preference_metric_allowed_ = true;
            if (!metric_direction_.empty() && !validateNumeric(metric_, {}, diagnostics)) { return nullptr; }
            const auto metric = metric_direction_.empty() ? P::numericConstant("0",diagnostics)
                : numericExpression(metric_, {}, count, diagnostics);
            temporal_metric_allowed_ = preference_metric_allowed_ = false;
            if (!metric) { return nullptr; }
            add(*model, metric->defined);
            const bool minimize = metric_direction_.empty() || metric_direction_ == "minimize";
            const auto objectiveTerm = anonymous_preferences_
                ? P::preferenceMetric(*model,metric->value,preference_counts_,minimize,diagnostics)
                : std::optional<H::ExprPtr>{metric->value};
            if(!objectiveTerm) { return nullptr; }
            H::Objective objective;
            objective.name = "plan-metric";
            objective.kind = minimize ? H::ObjKind::MINIMIZE : H::ObjKind::MAXIMIZE;
            objective.term = *objectiveTerm;
            model->objectives.push_back(std::move(objective));
        }
        if (object_mode_) {
            Uir::EncodingChoice objects;
            objects.site = file_; objects.unified_op = "object-fluents";
            objects.strategy = "finite-temporal-strict-undefined-single-writer";
            objects.fidelity = Uir::Fidelity::exact();
            objects.rationale = "Explicit temporal object extension of the preliminary PDDL3.1 proposal: "
                "old-state endpoint guards, addresses and RHS; STRICT definedness; SINGLE_WRITER object cells; "
                "guarded dynamic basic/numeric/object reads and exclusive object writes under no-moving-targets; "
                "finite transitive derived-source dependencies; complete pre/post named object observations. "
                "Object functions are constant between happenings. Continuous numeric addresses and rates "
                "are evaluated in each interval's current object state, and must be defined whenever active. "
                "This policy is explicit rather than a claim that IPC2008 supplied complete temporal object semantics.";
            report.addChoice(std::move(objects));
        }
        temporal_object_accesses_ = nullptr;
        Uir::EncodingChoice reportChoice;
        reportChoice.site = file_;
        reportChoice.unified_op = "temporal-plan-existence";
        reportChoice.strategy = "bounded-occurrences-symbolic-real-happenings";
        Uir::Fidelity::Bound bound;
        bound.kind = Uir::Fidelity::Bound::PLAN_HORIZON;
        bound.value = static_cast<int64_t>(horizon_); bound.site = file_;
        reportChoice.fidelity = Uir::Fidelity::underApprox(bound);
        reportChoice.rationale = std::string(continuous_mode_
            ? "Continuous trajectories constrained by simultaneous exact ODEs, closed-interval continuity, one-sided endpoint derivatives and pointwise derived closure; "
              "the endpoint policy interprets a full defined flow restricted to each compact happening interval. "
              "Rates are not restricted to a polynomial degree, and target solver completeness is not claimed. "
            : "Exact discrete durative-plan relation ") + "within the declared action-occurrence bound, "
            "with exact rational endpoint coordinates, overlapping occurrences, old-state endpoint effects, "
            "open-interval conditions, occurrence-specific historical guards, all mandatory timed initial literals, "
            "stable-goal makespan after the final actual action, and no-moving-targets mutexes. "
            "UNSAT is only bounded non-existence; optimization is bounded to these occurrences.";
        report.addChoice(std::move(reportChoice));
        recordTrajectoryInterpretation(report);
        recordRelaxations(report);
        return model;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diagnostics,
                                Uir::TranslationReport& report) {
        if (!initializeObjects(diagnostics)) { return nullptr; }
        if (!(numeric_mode_ ? initializeNumeric(diagnostics) : initializeCosts(diagnostics))) { return nullptr; }
        if (!validatePreferenceSchemas(diagnostics) || !validateFinalMetric(diagnostics)) { return nullptr; }
        if (!validateDerivedBodies(diagnostics)) { return nullptr; }
        for (const auto& action : actions_) {
            Environment types;
            for (const auto& parameter : action.params) { types.emplace(parameter.name, parameter.type); }
            if ((action.has_precondition && !validateSchema(action.precondition, types, false, diagnostics))
                || (action.has_effect && !validateSchema(action.effect, types, true, diagnostics))) {
                return nullptr;
            }
        }
        if (!validateSchema(goal_, {}, false, diagnostics)) { return nullptr; }
        static_conditions_validated_ = true;
        sparse_fluents_ = derived_.empty() && !object_mode_;
        auto model = std::make_shared<H::ConstraintModel>();
        object_context_ = model.get();
        const H::Sort boolean = H::Sort::boolean();

        // Validate every source fact before reachability or target allocation.
        if (!initialState(static_initial_, diagnostics, true)) { return nullptr; }
        if (!derived_.empty() || object_mode_) {
            // Object-addressed predicates require the entire finite relation.
            // Derived atoms are observations of every complete basic state,
            // including tuples whose truth changes only through inference.
            groundAtoms();
            groundActions();
        } else {
            if (allowed_actions_) { groundActions(); }
            else if (!groundReachableActions(diagnostics)) { return nullptr; }
            if (!groundChangedAtoms(diagnostics)) { return nullptr; }
        }
        // The validated closed-world table now owns the facts. Do not keep a
        // duplicate set and the original syntax alive during HIR construction.
        std::vector<Sexp>{}.swap(init_);

        for (unsigned step = 0; step <= horizon_; ++step) {
            if (object_mode_) { declareObjectState(*model, step); }
            for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
                const auto cell = numericAt(index, step);
                declare(*model, cell.value->name, "state[" + std::to_string(step) + "]::" + numeric_ground_[index].label, H::Sort::real());
                declare(*model, cell.defined->name, "state[" + std::to_string(step) + "]::defined(" + numeric_ground_[index].label + ")");
            }
            if (!cost_target_.empty()) {
                declare(*model, cost_target_ + "@" + std::to_string(step),
                        "state[" + std::to_string(step) + "]::(total-cost)", H::Sort::real());
            }
            for (const GroundAtom& atom : atoms_) {
                declare(*model, atom.target_base + "@" + std::to_string(step),
                        "state[" + std::to_string(step) + "]::" + atom.source_label);
            }
            if (step == horizon_) { continue; }
            S::ChoiceObservable choice;
            choice.source_name = "plan[" + std::to_string(step) + "]";
            choice.omit_label = "__pddl_padding_noop";
            for (const GroundAction& action : ground_actions_) {
                if (action.earliest_step > step) { continue; }
                const std::string target = action.target_base + "@" + std::to_string(step);
                declare(*model, target,
                        "choice[" + std::to_string(step) + "]::"
                            + action.source_label);
                choice.alternatives.push_back({action.source_label, target});
            }
            const std::string noop = "__pddl_noop@" + std::to_string(step);
            declare(*model, noop);
            choice.alternatives.push_back({choice.omit_label, noop});
            projection_.choices.push_back(std::move(choice));
        }

        if (object_mode_) {
            std::vector<P::ObjectStateCell> initial;
            for (std::size_t i = 0; i < object_ground_.size(); ++i) { initial.push_back(objectAt(i, 0)); }
            const auto relation = P::initialObjectState(*model, object_universe_, initial, object_initial_, diagnostics);
            if (!relation) { return nullptr; }
            for (const auto& term : relation->constraints) { add(*model, term); }
        }
        for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
            const auto cell = numericAt(index, 0);
            const auto initial = numeric_initial_.find(numeric_ground_[index].key);
            add(*model, H::mkOp(H::Op::EQ, {cell.defined, H::mkBool(initial != numeric_initial_.end())}));
            add(*model, H::mkOp(H::Op::EQ, {cell.value, initial == numeric_initial_.end() ? H::mkReal("0") : initial->second}));
        }
        for (unsigned step = 0; step <= horizon_; ++step) {
            if (!appendDerivedAt(*model, step, diagnostics)) { return nullptr; }
        }

        if (!cost_target_.empty()) {
            add(*model, H::mkOp(H::Op::EQ,
                {costAt(0), numeric_initial_.at(canonical("total-cost", {}))}));
        }
        for (const GroundAtom& atom : atoms_) {
            if (derived_predicates_.count(atom.predicate)) { continue; }
            H::ExprPtr value = atomAt(atom.target_base, 0);
            add(*model, static_initial_.count(canonical(atom.predicate, atom.args)) != 0
                            ? value
                            : H::mkOp(H::Op::NOT, {value}));
        }

        for (unsigned step = 0; step < horizon_; ++step) {
            std::vector<H::ExprPtr> choices;
            std::map<std::string, FluentUpdates> selected_updates;
            std::vector<P::NumericUpdate> selected_numeric;
            std::vector<P::ObjectUpdate> selected_objects;
            for (const GroundAction& action : ground_actions_) {
                // The first relaxed reachability layer is a lower bound on
                // actual applicability. Earlier choices reconstruct as false.
                if (action.earliest_step > step) { continue; }
                const std::string action_name =
                    action.target_base + "@" + std::to_string(step);
                H::ExprPtr selected = H::mkIdent(action_name, boolean);
                choices.push_back(selected);
                Environment environment = actionEnvironment(action);
                if (!appendPreferenceInstances(action_preferences_[action.schema->name], environment,
                    action_name, selected, step, *model, diagnostics)) { return nullptr; }

                if (action.schema->has_precondition) {
                    H::ExprPtr precondition = formula(
                        action.schema->precondition, environment, step, diagnostics);
                    if (!precondition) { return nullptr; }
                    if (precondition->kind == H::ExprKind::LIT_BOOL) {
                        if (!precondition->bool_value) {
                            add(*model, negation(selected));
                            continue;
                        }
                    } else {
                        add(*model, H::mkOp(H::Op::IMPLIES, {selected, precondition}));
                    }
                }

                std::map<std::string, FluentUpdates> updates;
                pending_costs_.clear();
                pending_numeric_.clear();
                pending_objects_.clear();
                pending_numeric_conditions_.clear();
                if (action.schema->has_effect
                    && !collectEffects(action.schema->effect, environment, step,
                                       H::mkBool(true), updates, diagnostics)) {
                    return nullptr;
                }
                for (const auto& requirement : pending_numeric_conditions_) {
                    add(*model, H::mkOp(H::Op::IMPLIES, {selected, requirement}));
                }
                for (auto update : pending_objects_) {
                    update.guard = conjunction({selected, update.guard});
                    selected_objects.push_back(std::move(update));
                }
                for (auto update : pending_numeric_) {
                    update.guard = conjunction({selected, update.guard});
                    update.owner_id = action_name;
                    selected_numeric.push_back(std::move(update));
                }
                if (!cost_target_.empty()) {
                    auto next_cost = costAt(step);
                    for (const auto& amount : pending_costs_) {
                        next_cost = H::mkOp(H::Op::ADD, {next_cost, amount});
                    }
                    add(*model, H::mkOp(H::Op::IMPLIES,
                        {selected, H::mkOp(H::Op::EQ, {costAt(step + 1), next_cost})}));
                }
                for (const auto& [atom, update] : updates) {
                    auto& combined = selected_updates[atom];
                    if (!update.add_conditions.empty()) {
                        combined.add_conditions.push_back(conjunction(
                            {selected, disjunction(update.add_conditions)}));
                    }
                    if (!update.delete_conditions.empty()) {
                        combined.delete_conditions.push_back(conjunction(
                            {selected, disjunction(update.delete_conditions)}));
                    }
                }
            }

            if (object_mode_) {
                std::vector<P::ObjectStateCell> before, after;
                for (std::size_t i = 0; i < object_ground_.size(); ++i) {
                    before.push_back(objectAt(i, step)); after.push_back(objectAt(i, step + 1));
                }
                const auto relation = P::buildObjectTransition(*model, object_universe_, before, after,
                    selected_objects, P::ObjectAssignmentPolicy::SINGLE_WRITER, diagnostics);
                if (!relation) { return nullptr; }
                for (const auto& term : relation->constraints) { add(*model, term); }
            }
            if (numeric_mode_) {
                std::vector<P::NumericStateCell> before, after;
                for (std::size_t index = 0; index < numeric_ground_.size(); ++index) {
                    before.push_back(numericAt(index, step));
                    after.push_back(numericAt(index, step + 1));
                }
                auto transition = P::buildNumericTransition(*model, before, after, selected_numeric, diagnostics);
                if (!transition) { return nullptr; }
                for (const auto& formula : transition->constraints) { add(*model, formula); }
            }
            // Exactly one action/noop is selected below. Aggregate only the
            // selected effects and write one successor equation per fluent,
            // rather than an action-by-fluent Cartesian set of frame clauses.
            // Guards use the old state; simultaneous adds still win deletes.
            for (const GroundAtom& atom : atoms_) {
                if (derived_predicates_.count(atom.predicate)) { continue; }
                const auto now = atomAt(atom.target_base, step);
                const auto next = atomAt(atom.target_base, step + 1);
                const auto update = selected_updates.find(atom.target_base);
                H::ExprPtr successor = now;
                if (update != selected_updates.end()) {
                    const auto adds = disjunction(update->second.add_conditions);
                    const auto deletes = disjunction(update->second.delete_conditions);
                    successor = H::mkOp(H::Op::OR, {adds,
                        H::mkOp(H::Op::AND, {now, H::mkOp(H::Op::NOT, {deletes})})});
                }
                add(*model, H::mkOp(H::Op::EQ, {next, successor}));
            }

            const std::string noop_name = "__pddl_noop@" + std::to_string(step);
            H::ExprPtr noop = H::mkIdent(noop_name, boolean);
            choices.push_back(noop);
            if (!cost_target_.empty()) {
                addAxiom(*model, H::mkOp(H::Op::IMPLIES,
                    {noop, H::mkOp(H::Op::EQ, {costAt(step + 1), costAt(step)})}));
            }
            for (const GroundAtom& atom : atoms_) {
                if (derived_predicates_.count(atom.predicate)) { continue; }
                H::ExprPtr now = atomAt(atom.target_base, step);
                H::ExprPtr next = atomAt(atom.target_base, step + 1);
                addAxiom(*model, H::mkOp(
                    H::Op::IMPLIES,
                    {noop, H::mkOp(H::Op::EQ, {now, next})}));
            }
            if (step + 1 < horizon_) {
                H::ExprPtr next_noop = H::mkIdent(
                    "__pddl_noop@" + std::to_string(step + 1), boolean);
                addAxiom(*model,
                         H::mkOp(H::Op::IMPLIES, {noop, next_noop}));
            }

            addAxiom(*model, disjunction(choices));
            // A prefix records whether an earlier choice was selected. This
            // is linear in the action count, with existential target-only
            // witnesses, instead of all pairs of mutually exclusive actions.
            H::ExprPtr seen = choices.front();
            for (std::size_t i = 1; i < choices.size(); ++i) {
                addAxiom(*model, H::mkOp(H::Op::OR,
                    {H::mkOp(H::Op::NOT, {seen}), H::mkOp(H::Op::NOT, {choices[i]})}));
                if (i + 1 < choices.size()) {
                    const std::string name = "__pddl_choice_prefix@" + std::to_string(step)
                                           + "_" + std::to_string(i);
                    declare(*model, name);
                    const auto prefix = H::mkIdent(name, boolean);
                    addAxiom(*model, H::mkOp(H::Op::EQ,
                        {prefix, H::mkOp(H::Op::OR, {seen, choices[i]})}));
                    seen = prefix;
                }
            }
        }

        Environment no_variables;
        H::ExprPtr goal = formula(goal_, no_variables, horizon_, diagnostics);
        if (!goal) { return nullptr; }
        add(*model, goal);
        if (!appendClassicalTrajectory(*model, diagnostics)) { return nullptr; }
        if (((numeric_mode_ || featureEnabled(":preferences")) && !metric_direction_.empty()) || anonymous_preferences_) {
            const bool minimize = metric_direction_.empty() || metric_direction_ == "minimize";
            preference_metric_allowed_ = true;
            auto value = metric_direction_.empty() ? P::numericConstant("0", diagnostics)
                : numericExpression(metric_, no_variables, horizon_, diagnostics);
            preference_metric_allowed_ = false;
            if (!value) { return nullptr; }
            add(*model, value->defined);
            const auto metric = anonymous_preferences_
                ? P::preferenceMetric(*model, value->value, preference_counts_, minimize, diagnostics)
                : std::optional<H::ExprPtr>{value->value};
            if (!metric) { return nullptr; }
            H::Objective objective;
            objective.name = "pddl-metric";
            objective.kind = minimize ? H::ObjKind::MINIMIZE : H::ObjKind::MAXIMIZE;
            objective.term = *metric;
            model->objectives.push_back(std::move(objective));
        }
        if (minimize_cost_ && !numeric_mode_ && !featureEnabled(":preferences") && !anonymous_preferences_) {
            H::Objective objective;
            objective.name = "total-cost";
            objective.kind = H::ObjKind::MINIMIZE;
            objective.term = costAt(horizon_);
            model->objectives.push_back(std::move(objective));
            Uir::EncodingChoice costs;
            costs.site = file_;
            costs.unified_op = "action-cost";
            costs.strategy = "exact-rational-cost-progression";
            costs.fidelity = Uir::Fidelity::exact();
            costs.rationale = "Each selected action adds its simultaneous, old-state-guarded "
                "nonnegative static costs to total-cost. Noops cost zero. The final accumulator "
                "and minimization direction are preserved for every admitted bounded plan; "
                "this does not assert an unbounded globally optimal plan.";
            report.addChoice(std::move(costs));
        }

        if (object_mode_) {
            Uir::EncodingChoice objects;
            objects.site = file_; objects.unified_op = "object-fluents";
            objects.strategy = "finite-sequential-strict-undefined-single-writer";
            objects.fidelity = Uir::Fidelity::exact();
            objects.rationale = "The explicit sequential object-fluent profile uses nominal finite union types, "
                "STRICT atom/Boolean definedness and SINGLE_WRITER simultaneous assignments. All addresses and RHS "
                "are evaluated in the old state; omitted initial values are undefined, explicit assign undefined "
                "resets a cell, and undefined evaluated RHS values cannot fire. Named object choices plus code/defined "
                "coordinates reconstruct every source state. IPC2008 describes object/temporal semantics as preliminary; "
                "this recorded sequential policy does not claim a temporal object-fluent standard or mutex support.";
            report.addChoice(std::move(objects));
        }
        Uir::EncodingChoice choice;
        choice.site = file_;
        choice.unified_op = "plan-existence";
        choice.strategy = "bounded-prefix-with-noop-suffix";
        Uir::Fidelity::Bound bound;
        bound.kind = Uir::Fidelity::Bound::PLAN_HORIZON;
        bound.value = static_cast<int64_t>(horizon_);
        bound.site = file_;
        choice.fidelity = Uir::Fidelity::underApprox(bound);
        choice.rationale =
            "the target is satisfiable exactly when the accepted PDDL task has a "
            "source action sequence of length at most " + std::to_string(horizon_)
            + "; generated noops form a suffix and beta removes them. SAT therefore "
              "decodes to a real plan, while UNSAT proves only that no plan exists "
              "within this PLAN_HORIZON";
        report.addChoice(std::move(choice));

        recordTrajectoryInterpretation(report);
        recordRelaxations(report);
        return model;
    }

    struct PreferenceSyntax {
        std::string identity, name;
        Sexp body;
        std::vector<std::vector<Typed>> outer_quantifiers;
        bool trajectory = false;
    };

    static bool containsPreference(const Sexp& expression) {
        if (expression.head() == "preference") { return true; }
        for (const auto& child : expression.list) { if (containsPreference(child)) { return true; } }
        return false;
    }

    bool stripPreferences(Sexp& expression, const std::string& path, bool trajectory,
        std::vector<PreferenceSyntax>& output, std::vector<std::vector<Typed>> frames,
        Uir::Diagnostics& diagnostics) {
        if (!containsPreference(expression)) { return true; }
        const auto head = expression.head();
        if (head == "preference") {
            if (!requireFeature(":preferences", "preference", diagnostics)) { return false; }
            const bool named = expression.list.size() == 3;
            if ((!named && expression.list.size() != 2)
                || (named && (!expression.list[1].isAtom() || !isName(expression.list[1].atom)))) {
                diagnostics.error(ErrorCode::E_PARSE, "preference requires an optional name and one condition"); return false;
            }
            const auto& body = expression.list[named ? 2 : 1];
            if (containsPreference(body)) {
                diagnostics.error(ErrorCode::E_PARSE, "PDDL3 preferences cannot contain another preference"); return false;
            }
            const auto name = named ? expression.list[1].atom : std::string{};
            if (named) { preference_names_.insert(name); } else { anonymous_preferences_ = true; }
            preferences_present_ = true;
            output.push_back({path, name, body, std::move(frames), trajectory});
            expression = Sexp{}; expression.list.push_back(Sexp{"and", {}});
            return true;
        }
        if (head == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!stripPreferences(expression.list[i], path + "/and/" + std::to_string(i),
                                      trajectory, output, frames, diagnostics)) { return false; }
            }
            return true;
        }
        if (head == "forall" && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            if (!requireFeature(":universal-preconditions", "forall containing preferences", diagnostics)) { return false; }
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "preference quantifier", variables, diagnostics)) { return false; }
            frames.push_back(std::move(variables));
            return stripPreferences(expression.list[2], path + "/forall", trajectory, output, std::move(frames), diagnostics);
        }
        diagnostics.error(ErrorCode::E_PARSE,
            "PDDL3 preferences may occur only below conjunction/forall, not inside other connectives, modalities or effects");
        return false;
    }

    bool prepareTrajectorySource(Uir::Diagnostics& diagnostics) {
        if (!trajectory_constraints_.empty()
            && !requireFeature(":constraints", "state trajectory constraints", diagnostics)) { return false; }
        for (std::size_t i = 0; i < trajectory_constraints_.size(); ++i) {
            if (!stripPreferences(trajectory_constraints_[i], "constraints/" + std::to_string(i),
                                  true, goal_preferences_, {}, diagnostics)) { return false; }
        }
        if (!stripPreferences(goal_, "goal", false, goal_preferences_, {}, diagnostics)) { return false; }
        for (auto& action : actions_) {
            if (containsPreference(action.effect)) {
                diagnostics.error(ErrorCode::E_PARSE, "preferences are invalid inside action effects and conditional-effect guards");
                return false;
            }
            if (action.has_precondition && !stripPreferences(action.precondition,
                "action/" + action.name, false, action_preferences_[action.name], {}, diagnostics)) { return false; }
        }
        if ((preferences_present_ || !trajectory_constraints_.empty()) && usesPolicy()) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "PDDL3 trajectory/preference integration requires a deterministic linear trace; "
                "FOND source integration has not yet been qualified");
            return false;
        }
        return true;
    }

    struct TrajectorySyntax {
        P::TrajectoryOperator operation;
        const Sexp* first = nullptr;
        const Sexp* second = nullptr;
        H::ExprPtr lower, upper;
    };

    std::optional<TrajectorySyntax> trajectorySyntax(const Sexp& expression, Uir::Diagnostics& diagnostics) {
        using K = P::TrajectoryOperator;
        static const std::map<std::string, K> names{{"always",K::ALWAYS},{"sometime",K::SOMETIME},
            {"within",K::WITHIN},{"at-most-once",K::AT_MOST_ONCE},{"sometime-before",K::SOMETIME_BEFORE},
            {"sometime-after",K::SOMETIME_AFTER},{"always-within",K::ALWAYS_WITHIN},
            {"hold-during",K::HOLD_DURING},{"hold-after",K::HOLD_AFTER}};
        const auto found = names.find(expression.head());
        TrajectorySyntax result;
        std::size_t argument = 1;
        if (expression.head() == "at" && expression.list.size() == 3 && expression.list[1].atom == "end") {
            result.operation = K::AT_END; argument = 2;
        } else if (found != names.end()) { result.operation = found->second; }
        else {
            diagnostics.error(ErrorCode::E_PARSE, "unknown PDDL3 trajectory modality: " + expression.head()); return std::nullopt;
        }
        const bool timed = result.operation == K::WITHIN || result.operation == K::ALWAYS_WITHIN
            || result.operation == K::HOLD_DURING || result.operation == K::HOLD_AFTER;
        const bool pair = result.operation == K::SOMETIME_BEFORE || result.operation == K::SOMETIME_AFTER
            || result.operation == K::ALWAYS_WITHIN;
        const auto read_bound = [&](H::ExprPtr& output) {
            if (argument >= expression.list.size() || !decimalNumber(expression.list[argument])) {
                diagnostics.error(ErrorCode::E_PARSE, "trajectory time bound must be an exact numeric literal"); return false;
            }
            const auto& number = expression.list[argument++].atom;
            auto value = P::numericConstant(number.front() == '+' ? number.substr(1) : number, diagnostics);
            if (!value) { return false; } output = value->value; return true;
        };
        if (timed && !read_bound(result.lower)) { return std::nullopt; }
        if (result.operation == K::HOLD_DURING && !read_bound(result.upper)) { return std::nullopt; }
        if (expression.list.size() != argument + (pair ? 2 : 1)) {
            diagnostics.error(ErrorCode::E_PARSE, "wrong trajectory modality arity"); return std::nullopt;
        }
        result.first = &expression.list[argument];
        if (pair) { result.second = &expression.list[argument+1]; }
        return result;
    }

    bool trajectoryVariables(const Sexp& list, std::vector<Typed>& variables,
                             Environment& types, Uir::Diagnostics& diagnostics) {
        if (list.isAtom() || !typedList(list, 0, true, "trajectory quantifier", variables, diagnostics)) { return false; }
        for (const auto& variable : variables) {
            if (!knownObjectType(variable.type)) {
                diagnostics.error(ErrorCode::E_TYPE, "unknown object type in trajectory/preference quantifier"); return false;
            }
            if (variable.type != "object" && !requireFeature(":typing", "typed trajectory quantifier", diagnostics)) { return false; }
            types[variable.name] = variable.type;
        }
        return true;
    }

    bool validateTrajectory(const Sexp& expression, Environment types, Uir::Diagnostics& diagnostics) {
        if (expression.isAtom() || expression.list.empty()) {
            diagnostics.error(ErrorCode::E_PARSE, "trajectory expression must be a modality, conjunction or forall"); return false;
        }
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!validateTrajectory(expression.list[i], types, diagnostics)) { return false; }
            }
            return true;
        }
        if (expression.head() == "forall") {
            if (expression.list.size() != 3) {
                diagnostics.error(ErrorCode::E_PARSE, "trajectory forall requires variables and one body"); return false;
            }
            std::vector<Typed> variables;
            return trajectoryVariables(expression.list[1], variables, types, diagnostics)
                && validateTrajectory(expression.list[2], std::move(types), diagnostics);
        }
        const auto syntax = trajectorySyntax(expression, diagnostics);
        return syntax && validateSchema(*syntax->first, types, false, diagnostics)
            && (!syntax->second || validateSchema(*syntax->second, types, false, diagnostics));
    }

    bool validatePreferenceSchemas(Uir::Diagnostics& diagnostics) {
        const auto check = [&](const PreferenceSyntax& preference, Environment types) {
            for (const auto& frame : preference.outer_quantifiers) {
                for (const auto& variable : frame) {
                    if (!knownObjectType(variable.type)) {
                        diagnostics.error(ErrorCode::E_TYPE, "unknown type in preference quantifier"); return false;
                    }
                    if (variable.type != "object" && !requireFeature(":typing", "typed preference quantifier", diagnostics)) { return false; }
                    types[variable.name] = variable.type;
                }
            }
            return preference.trajectory ? validateTrajectory(preference.body, std::move(types), diagnostics)
                : validateSchema(preference.body, std::move(types), false, diagnostics);
        };
        for (const auto& expression : trajectory_constraints_) { if (!validateTrajectory(expression, {}, diagnostics)) { return false; } }
        for (const auto& preference : goal_preferences_) { if (!check(preference, {})) { return false; } }
        for (const auto& action : actions_) {
            Environment types;for (const auto& parameter : action.params) { types[parameter.name] = parameter.type; }
            temporal_duration_allowed_ = action.durative;
            for (const auto& preference : action_preferences_[action.name]) {
                if (!action.durative) { if (!check(preference, types)) { return false; }continue; }
                auto scoped = types;
                for (const auto& frame : preference.outer_quantifiers) {
                    for (const auto& variable : frame) {
                        if (!knownObjectType(variable.type)) {
                            diagnostics.error(ErrorCode::E_TYPE,"unknown type in durative preference quantifier");return false;
                        }
                        if (variable.type != "object" && !requireFeature(":typing","typed preference quantifier",diagnostics)) { return false; }
                        scoped[variable.name]=variable.type;
                    }
                }
                const auto point=timePoint(preference.body);
                if (!point || *point==TimePoint::FLOW) {
                    diagnostics.error(ErrorCode::E_PARSE,"durative preference must enclose one at-start/at-end/over-all condition");return false;
                }
                if (!validateTimed(preference.body,scoped,false,diagnostics)) { return false; }
            }
            temporal_duration_allowed_ = false;
        }
        return true;
    }

    bool validateFinalMetric(Uir::Diagnostics& diagnostics) {
        if (metric_direction_.empty() || (!numeric_mode_ && !featureEnabled(":preferences"))) { return true; }
        preference_metric_allowed_ = true;
        const bool valid = validateNumeric(metric_, {}, diagnostics);
        preference_metric_allowed_ = false;
        return valid;
    }

    std::optional<P::NumericCondition> trajectoryCondition(const Sexp& expression,
        Environment& environment, unsigned step, Uir::Diagnostics& diagnostics) {
        if (numeric_mode_) { return numericCondition(expression, environment, step, diagnostics); }
        const auto value = formula(expression, environment, step, diagnostics);
        return value ? P::numericPredicate(value, diagnostics) : std::nullopt;
    }

    H::ExprPtr classicalTrajectory(const Sexp& expression, Environment& environment,
        H::ConstraintModel& model, Uir::Diagnostics& diagnostics) {
        if (expression.head() == "and") {
            std::vector<H::ExprPtr> terms;
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                auto term = classicalTrajectory(expression.list[i], environment, model, diagnostics);
                if (!term) { return nullptr; } terms.push_back(term);
            }
            return conjunction(std::move(terms));
        }
        if (expression.head() == "forall") {
            std::vector<Typed> variables;
            if (!typedList(expression.list[1], 0, true, "trajectory quantifier", variables, diagnostics)) { return nullptr; }
            std::vector<H::ExprPtr> terms;bool ok = true;
            enumerate(variables, 0, environment, [&](Environment& bound) {
                auto term = classicalTrajectory(expression.list[2], bound, model, diagnostics);
                if (!term) { return false; } terms.push_back(term);return true;
            }, ok);
            return ok ? conjunction(std::move(terms)) : nullptr;
        }
        const auto syntax = trajectorySyntax(expression, diagnostics);if (!syntax) { return nullptr; }
        if (temporal_mode_) { return temporalTrajectoryAtom(*syntax,environment,model,diagnostics); }
        std::vector<P::TrajectorySample> samples;
        for (unsigned step = 0; step <= horizon_; ++step) {
            auto first = trajectoryCondition(*syntax->first, environment, step, diagnostics);
            if (!first) { return nullptr; }
            std::optional<P::NumericCondition> second;
            if (syntax->second) {
                second = trajectoryCondition(*syntax->second, environment, step, diagnostics);
                if (!second) { return nullptr; }
            }
            auto active = step == 0 ? H::mkBool(true)
                : negation(H::mkIdent("__pddl_noop@" + std::to_string(step-1), H::Sort::boolean()));
            samples.push_back({active, H::mkReal(std::to_string(step)), *first, second});
        }
        auto encoding = P::encodeFiniteTrajectory(model, syntax->operation, samples, syntax->lower, syntax->upper, diagnostics);
        if (!encoding) { return nullptr; }
        for (const auto& domain : encoding->domain_constraints) { addAxiom(model, domain); }
        return encoding->satisfied;
    }

    bool appendPreferenceInstances(const std::vector<PreferenceSyntax>& preferences,
        Environment environment, const std::string& occurrence, H::ExprPtr active,
        unsigned step, H::ConstraintModel& model, Uir::Diagnostics& diagnostics) {
        for (const auto& preference : preferences) {
            std::function<bool(std::size_t,Environment&,const std::string&)> ground;
            ground = [&](std::size_t depth, Environment& bound, const std::string& identity) {
                if (depth == preference.outer_quantifiers.size()) {
                    auto satisfied = preference.trajectory ? classicalTrajectory(preference.body, bound, model, diagnostics)
                        : formula(preference.body, bound, step, diagnostics);
                    if (!satisfied) { return false; }
                    preference_instances_.push_back({identity, preference.name, active, satisfied});return true;
                }
                const auto& frame = preference.outer_quantifiers[depth];bool ok = true;
                enumerate(frame, 0, bound, [&](Environment& inner) {
                    std::vector<std::string> arguments;
                    for (const auto& variable : frame) { arguments.push_back(inner.at(variable.name)); }
                    return ground(depth+1, inner, identity + "/" + canonical("forall", arguments));
                }, ok);
                return ok;
            };
            if (!ground(0, environment, occurrence + "/" + preference.identity)) { return false; }
        }
        return true;
    }

    bool appendClassicalTrajectory(H::ConstraintModel& model, Uir::Diagnostics& diagnostics) {
        preference_counts_.anonymous_violations = H::mkInt(0);
        if (!preferences_present_ && trajectory_constraints_.empty()) { return true; }
        Environment empty;
        for (const auto& expression : trajectory_constraints_) {
            auto satisfied = classicalTrajectory(expression, empty, model, diagnostics);
            if (!satisfied) { return false; }add(model, satisfied);
        }
        if (!preferences_present_) { return true; }
        if (!appendPreferenceInstances(goal_preferences_, {}, "whole-plan", H::mkBool(true),
                                       temporal_mode_ ? static_cast<unsigned>(trajectory_happenings_.size()) : horizon_,
                                       model, diagnostics)) { return false; }
        std::vector<std::string> names(preference_names_.begin(), preference_names_.end());
        auto encoded = P::encodePreferences(model, preference_instances_, diagnostics, names);
        if (!encoded) { return false; }preference_counts_ = std::move(*encoded);return true;
    }

    std::optional<P::NumericCondition> observedCondition(const Sexp& expression,
        Environment& environment, const P::TrajectoryObservationDomain& domain,
        Uir::Diagnostics& diagnostics) {
        auto initial = numericCondition(expression, environment, 0, diagnostics);
        if (!initial) { return std::nullopt; }
        auto value = initial->value, defined = initial->defined;
        const auto time = H::mkBoundVar(domain.time_variable, H::Sort::real());
        const auto phase = H::mkBoundVar(domain.phase_variable, H::Sort::integer());
        const auto insert = [&](const H::ExprPtr& selected, const P::NumericCondition& condition) {
            value = H::mkOp(H::Op::ITE, {selected, condition.value, value});
            defined = H::mkOp(H::Op::ITE, {selected, condition.defined, defined});
        };
        const TimedFormula source{TimePoint::INTERVAL, expression, environment};
        for (unsigned step = 0; step < trajectory_happenings_.size(); ++step) {
            const auto& happening = trajectory_happenings_[step];
            auto before = numericCondition(expression, environment, step, diagnostics);
            auto after = flowCondition(source, step, diagnostics, nullptr, true);
            if (!before || !after) { return std::nullopt; }
            const auto at = conjunction({happening.active, H::mkOp(H::Op::EQ, {time, happening.time})});
            insert(conjunction({at, H::mkOp(H::Op::EQ, {phase,H::mkInt(0)})}), *before);
            insert(conjunction({at, H::mkOp(H::Op::EQ, {phase,H::mkInt(1)})}), *after);
            if (step + 1 < trajectory_happenings_.size()) {
                auto interior = flowCondition(source, step, diagnostics, time);
                if (!interior) { return std::nullopt; }
                const auto inside = conjunction({trajectory_happenings_[step+1].active,
                    H::mkOp(H::Op::LT, {happening.time,time}),
                    H::mkOp(H::Op::LT, {time,trajectory_happenings_[step+1].time})});
                insert(inside, *interior);
            }
        }
        return P::NumericCondition{value,defined,{}};
    }

    P::TrajectoryObservationDomain continuousTrajectoryDomain() {
        P::TrajectoryObservationDomain domain;
        domain.time_variable = "__pddl3_observed_time";
        domain.phase_variable = "__pddl3_observed_phase";
        const auto time = H::mkBoundVar(domain.time_variable,H::Sort::real());
        const auto phase = H::mkBoundVar(domain.phase_variable,H::Sort::integer());
        const auto ordinary = H::mkOp(H::Op::EQ, {phase,H::mkInt(0)});
        std::vector<H::ExprPtr> members{conjunction({ordinary,H::mkOp(H::Op::EQ,{time,H::mkReal("0")})})};
        domain.first = {H::mkReal("0"),H::mkInt(0)};
        domain.last = domain.first;
        if (!trajectory_happenings_.empty()) {
            members.push_back(conjunction({trajectory_happenings_[0].active,ordinary,
                H::mkOp(H::Op::LT,{H::mkReal("0"),time}),
                H::mkOp(H::Op::LT,{time,trajectory_happenings_[0].time})}));
        }
        for (unsigned step=0;step<trajectory_happenings_.size();++step) {
            const auto& happening=trajectory_happenings_[step];
            members.push_back(conjunction({happening.active,
                H::mkOp(H::Op::EQ,{time,happening.time}),
                disjunction({ordinary,H::mkOp(H::Op::EQ,{phase,H::mkInt(1)})})}));
            domain.last.time=H::mkOp(H::Op::ITE,{happening.active,happening.time,domain.last.time});
            domain.last.phase=H::mkOp(H::Op::ITE,{happening.active,H::mkInt(1),domain.last.phase});
            if(step+1<trajectory_happenings_.size()) {
                members.push_back(conjunction({trajectory_happenings_[step+1].active,ordinary,
                    H::mkOp(H::Op::LT,{happening.time,time}),
                    H::mkOp(H::Op::LT,{time,trajectory_happenings_[step+1].time})}));
            }
        }
        domain.contains=disjunction(std::move(members));
        return domain;
    }

    H::ExprPtr temporalTrajectoryAtom(const TrajectorySyntax& syntax,
        Environment& environment,H::ConstraintModel& model,Uir::Diagnostics& diagnostics) {
        std::optional<P::TrajectoryEncoding> encoding;
        if (continuous_mode_) {
            // Explicit full observation domain: all interior real instants,
            // plus both one-sided values at discrete jumps. Phase orders the
            // pre/post values at the same physical time. No sampling is used.
            const auto domain=continuousTrajectoryDomain();
            const auto first=observedCondition(*syntax.first,environment,domain,diagnostics);
            if(!first) { return nullptr; }
            std::optional<P::NumericCondition> second;
            if(syntax.second) {
                second=observedCondition(*syntax.second,environment,domain,diagnostics);
                if(!second) { return nullptr; }
            }
            encoding=P::encodeObservedTrajectory(model,domain,syntax.operation,*first,second,
                syntax.lower,syntax.upper,diagnostics);
        } else {
            std::vector<P::TrajectorySample> samples;
            for(unsigned step=0;step<=trajectory_happenings_.size();++step) {
                const auto first=numericCondition(*syntax.first,environment,step,diagnostics);
                if(!first) { return nullptr; }
                std::optional<P::NumericCondition> second;
                if(syntax.second) {
                    second=numericCondition(*syntax.second,environment,step,diagnostics);
                    if(!second) { return nullptr; }
                }
                samples.push_back({step ? trajectory_happenings_[step-1].active : H::mkBool(true),
                    step ? trajectory_happenings_[step-1].time : H::mkReal("0"),*first,second});
            }
            encoding=P::encodeFiniteTrajectory(model,syntax.operation,samples,syntax.lower,syntax.upper,diagnostics);
        }
        if(!encoding) { return nullptr; }
        for(const auto& constraint:encoding->domain_constraints) { addAxiom(model,constraint); }
        return encoding->satisfied;
    }

    bool appendTemporalPreferenceInstances(const Action& action,Environment environment,
        const std::string& occurrence,const H::ExprPtr& active,const P::DurativeOccurrence& instance,
        std::vector<P::TemporalEndpointAccess>& accesses,Uir::Diagnostics& diagnostics) {
        for(const auto& preference:action_preferences_[action.name]) {
            std::function<bool(std::size_t,Environment&,const std::string&)> ground;
            ground=[&](std::size_t depth,Environment& bound,const std::string& identity) {
                if(depth<preference.outer_quantifiers.size()) {
                    const auto& frame=preference.outer_quantifiers[depth];bool ok=true;
                    enumerate(frame,0,bound,[&](Environment& inner) {
                        std::vector<std::string> arguments;
                        for(const auto& variable:frame) { arguments.push_back(inner.at(variable.name)); }
                        return ground(depth+1,inner,identity+"/"+canonical("forall",arguments));
                    },ok);return ok;
                }
                const auto point=action.durative ? *timePoint(preference.body) : TimePoint::START;
                const auto& body=action.durative ? preference.body.list[2] : preference.body;
                if (point != TimePoint::INTERVAL) {
                    // A soft condition is always true for applicability, but
                    // its source reads still obey no-moving-targets. VAL's
                    // PreferenceGoal::markOwnedPreconditions delegates to the
                    // underlying condition, independently of its truth value.
                    for (unsigned step = 0; step < trajectory_happenings_.size(); ++step) {
                        const auto& happening = trajectory_happenings_[step];
                        P::TemporalEndpointAccess access;
                        access.active = conjunction({active, temporalMatch(happening,
                            point == TimePoint::START ? instance.start : instance.end)});
                        access.time = happening.time;
                        access.owner_id = occurrence + (point == TimePoint::START ? "_start" : "_end");
                        if (!temporalReads(body,bound,step,access,diagnostics)) { return false; }
                        accesses.push_back(std::move(access));
                    }
                }
                H::ExprPtr satisfied;
                if(point==TimePoint::INTERVAL && continuous_mode_) {
                    // Unlike an invariant precondition, this formula is only
                    // counted. Neither truth nor definedness is asserted hard.
                    if(trajectory_happenings_.empty()) { satisfied=H::mkBool(true); }
                    else { satisfied=continuousHistory({point,body,bound},trajectory_happenings_,instance,
                        static_cast<unsigned>(trajectory_happenings_.size()-1),diagnostics); }
                } else {
                    std::vector<H::ExprPtr> terms;
                    for(unsigned step=0;step<trajectory_happenings_.size();++step) {
                        if(point==TimePoint::INTERVAL && step+1==trajectory_happenings_.size()) { continue; }
                        const auto condition=numericCondition(body,bound,point==TimePoint::INTERVAL ? step+1 : step,diagnostics);
                        if(!condition) { return false; }
                        const auto applies=point==TimePoint::INTERVAL
                            ? flowCovers(instance,trajectory_happenings_[step],trajectory_happenings_[step+1])
                            : temporalMatch(trajectory_happenings_[step],point==TimePoint::START ? instance.start : instance.end);
                        terms.push_back(H::mkOp(H::Op::IMPLIES,{applies,P::numericSatisfied(*condition)}));
                    }
                    satisfied=conjunction(std::move(terms));
                }
                if(!satisfied) { return false; }
                preference_instances_.push_back({identity,preference.name,active,satisfied});return true;
            };
            if(!ground(0,environment,occurrence+"/"+preference.identity)) { return false; }
        }
        return true;
    }

    std::vector<P::TemporalHappening> trajectory_happenings_;

    void recordTrajectoryInterpretation(Uir::TranslationReport& report) const {
        if (!preferences_present_ && trajectory_constraints_.empty()) { return; }
        Uir::EncodingChoice choice;
        choice.site=file_; choice.unified_op="pddl3-trajectory-and-preference";
        choice.strategy=continuous_mode_ ? "full-real-time-one-sided-jump-observations"
            : temporal_mode_ ? "ai2009-exact-happening-sequence" : "ai2009-unit-step-prefix-sequence";
        choice.fidelity=Uir::Fidelity::exact();
        choice.rationale=continuous_mode_
            ? "Explicit continuous extension of the PDDL3 observation domain: every real interior time and both one-sided values at jumps, ordered by physical time then pre/post phase. This is not endpoint sampling or a claim that AI2009 uniquely specifies this continuous extension. Preference violations are exact counts, including complete occurrence-specific over-all conditions; solver completeness for quantified ODEs is not asserted."
            : "AI2009 Figure 1 over the actual bounded state sequence: initial state at zero, positive strictly increasing happening times (unit action positions in the classical profile), inactive suffix omitted. Soft goal/trajectory preferences count per ground instance; soft action preconditions count per executed occurrence. Named groups are summed and anonymous violations receive unit cost with the metric direction preserved.";
        report.addChoice(std::move(choice));
    }

    std::vector<Sexp> trajectory_constraints_;
    std::vector<PreferenceSyntax> goal_preferences_;
    std::map<std::string,std::vector<PreferenceSyntax>> action_preferences_;
    std::set<std::string> preference_names_;
    std::vector<P::PreferenceInstance> preference_instances_;
    P::PreferenceEncoding preference_counts_;
    bool preferences_present_ = false;
    bool anonymous_preferences_ = false;
    bool preference_metric_allowed_ = false;

    /** Set from `lenient_requirements`; see requireFeature. */
    bool lenient_requirements_ = false;
    std::string policy_mode_;
    unsigned policy_size_ = 0;
    bool has_horizon_ = true;
    /** Requirements accepted without being declared, for the report. */
    std::set<std::string> relaxed_features_;

    std::string domain_text_;
    std::string problem_text_;
    std::string file_;
    unsigned    horizon_ = 0;
    std::string domain_name_;
    std::string problem_name_;

    PlanningInternal::TypeHierarchy types_;
    std::map<std::string, std::set<std::string>> union_types_;
    bool multiple_inheritance_ = false;
    std::set<std::string> requirements_;
    bool uses_typing_ = false;
    std::set<std::string> missing_features_;
    std::map<std::string, Predicate> predicates_;
    std::vector<DerivedRule> derived_;
    std::set<std::string> derived_predicates_;
    // State-local, transitively expanded basic reads for happening mutexes.
    std::map<unsigned, std::map<std::string, std::set<std::string>>> derived_reads_;
    std::map<std::string, Predicate> numeric_functions_;
    std::map<std::string, Predicate> object_functions_;
    std::map<std::string, std::string> object_result_types_;
    bool object_mode_ = false;
    P::ObjectUniverse object_universe_;
    std::map<std::string, std::size_t> object_name_indices_;
    std::map<std::string, P::ObjectTable> object_tables_;
    struct GroundObject { std::string key, target, label, type; };
    std::vector<GroundObject> object_ground_;
    std::map<std::string, std::size_t> object_indices_;
    std::vector<std::pair<std::size_t, std::size_t>> object_initial_;
    std::vector<P::ObjectUpdate> pending_objects_;
    H::ConstraintModel* object_context_ = nullptr;
    std::unordered_set<const H::Expr*> object_obligation_seen_;
    std::map<std::string, std::vector<std::pair<Sexp, Environment>>> object_derived_bodies_;
    std::vector<std::vector<P::ObjectUpdate>> temporal_object_updates_;
    std::vector<P::TemporalEndpointAccess>* temporal_object_accesses_ = nullptr;
    std::map<std::string, H::ExprPtr> numeric_initial_;
    std::string cost_target_;
    std::vector<H::ExprPtr> pending_costs_;
    bool minimize_cost_ = false;
    bool temporal_mode_ = false;
    bool continuous_mode_ = false;
    std::map<unsigned, FlowReplacements> continuous_derived_;
    std::vector<H::ExprPtr> continuous_history_constraints_;
    unsigned continuous_history_serial_ = 0;
    bool temporal_duration_allowed_ = false;
    bool temporal_metric_allowed_ = false;
    H::ExprPtr temporal_duration_, temporal_total_time_;
    std::map<std::string, std::pair<bool, std::string>> temporal_dependency_keys_;
    bool numeric_mode_ = false;
    Sexp metric_;
    std::string metric_direction_;
    struct GroundNumeric { std::string key, target, label; };
    std::vector<GroundNumeric> numeric_ground_;
    std::map<std::string, std::size_t> numeric_indices_;
    std::vector<P::NumericUpdate> pending_numeric_;
    std::vector<H::ExprPtr> pending_numeric_conditions_;
    const PddlInternal::ActionInstances* allowed_actions_ = nullptr;
    bool sparse_fluents_ = false;
    bool static_conditions_validated_ = false;
    std::set<std::string> static_initial_;
    std::vector<Action> actions_;
    std::set<std::string> action_names_;
    std::vector<Typed> domain_objects_;
    std::vector<Typed> problem_objects_;
    std::vector<Typed> objects_;
    std::map<std::string, std::string> object_types_;
    std::vector<Sexp> init_;
    std::vector<TimedInitialSource> timed_initial_;
    Sexp goal_;
    bool has_goal_ = false;

    std::unordered_map<std::string, H::ExprPtr> fluent_identifiers_;
    std::unordered_map<std::string, H::ExprPtr> cost_identifiers_;
    std::vector<GroundAtom> atoms_;
    std::vector<GroundAction> ground_actions_;
    std::map<std::string, std::string> atom_targets_;
    std::map<std::string, std::string> target_owners_;
    std::set<std::string> declared_;

    S::ModelProjection projection_;
    S::Signature source_signature_;
    std::vector<S::SymbolMapping> symbol_map_;
    std::vector<S::Sentence> target_axioms_;
};

class PddlLanguage : public Language {
public:
    PddlLanguage() {
        // Feature families, not an empirical benchmark success percentage.
        // The original nine ADL/cost/FOND families now include five additional
        // constructions: numeric state, derived closure, durations, TILs and exact flows.
        coverage_.supported = 14;
        coverage_.missing = {
            "PDDL3 trajectory constraints/preferences over nondeterministic FOND traces",
            "object/numeric/derived temporal combinations under FOND policy semantics",
            "mixed fairness and oneof under forall",
        };
        coverage_.total = coverage_.supported + coverage_.missing.size();
    }

    std::string id() const override { return "pddl"; }
    std::string displayName() const override { return "PDDL (ADL, numeric, derived, temporal, PDDL3.1 objects, FOND)"; }
    std::string version() const override { return "PDDL 2.1/2.2 temporal; PDDL 3.1 explicit object policy; bounded FOND"; }
    std::vector<std::string> extensions() const override { return {".pddl"}; }

    /** HDDL also claims `.pddl`, so the tie is broken here.
     *
     *  The score is 0.5 and not 0.95 on purpose. HDDL is PDDL plus a task
     *  hierarchy, so the two are not symmetric: a hierarchy marker means HDDL
     *  and nothing else, while everything a plain PDDL file contains an HDDL
     *  file contains too. Ordering the scores -- "this is a PDDL-family file"
     *  under "this is specifically HDDL" (hddl.cpp returns 0.95) -- lets the
     *  more specific language win whenever it recognises itself, and this one
     *  win otherwise. `smtlib2.cpp` solves the same ambiguity against CHC by
     *  re-testing CHC's marker and returning 0.0; that is one token, while
     *  HDDL's discriminator is three and may grow, and a marker list copied
     *  into two files is a list that drifts.
     *
     *  Until 2026-09-20 this was not overridden at all. Both frontends then
     *  scored the base 0.0, `LanguageRegistry::detect` kept its first
     *  candidate, and HDDL is registered first -- so registration ORDER
     *  decided which frontend read a plain PDDL domain. It went to HDDL and was
     *  refused with "plain PDDL belongs to --from pddl": a correct message
     *  about a file the detector should never have handed over. Every PDDL
     *  fixture and every vendored PDDL instance needed an explicit `--from`. */
    double sniff(std::string_view head) const override {
        return head.find("(define") != std::string_view::npos ? 0.5 : 0.0;
    }

    const OpCoverage& coverage() const override { return coverage_; }
    bool acceptsDataFiles() const override { return true; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& options) override {
        ParseOutcome result;
        const auto slurp = [&](const std::string& path, std::string& into) {
            std::ifstream input(path, std::ios::binary);
            if (!input) {
                result.diagnostics.error(ErrorCode::E_IO,
                                         "cannot open '" + path + "'");
                return false;
            }
            std::ostringstream buffer;
            buffer << input.rdbuf();
            into = buffer.str();
            return true;
        };

        std::string domain = unit.inline_source;
        if (domain.empty()) {
            std::error_code error;
            if (std::filesystem::is_directory(unit.main_path, error)) {
                result.diagnostics.error(ErrorCode::E_IO,
                                         "'" + unit.main_path + "' is a directory");
                return result;
            }
            if (!slurp(unit.main_path, domain)) { return result; }
        }
        if (unit.data_paths.empty()) {
            result.diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "no problem file: a PDDL domain is only a schema; pass exactly one "
                "problem with `--data`");
            return result;
        }
        if (unit.data_paths.size() != 1) {
            result.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                     "PDDL translation takes exactly one problem file, not "
                                         + std::to_string(unit.data_paths.size()));
            return result;
        }
        std::string problem;
        if (!slurp(unit.data_paths[0], problem)) { return result; }

        std::string policy_mode;
        unsigned policy_size = 0;
        const auto policy_option = options.options.find("fond_policy");
        const auto size_option = options.options.find("policy_size");
        if (policy_option != options.options.end()) {
            policy_mode = policy_option->second;
            if (policy_mode != "strong" && policy_mode != "strong-cyclic") {
                result.diagnostics.error(ErrorCode::E_PARSE,
                    "fond_policy must be strong or strong-cyclic");
                return result;
            }
            const std::string size = size_option == options.options.end() ? "" : size_option->second;
            if (size.empty() || size.size() > 2
                || !std::all_of(size.begin(), size.end(), [](unsigned char c) { return std::isdigit(c); })) {
                result.diagnostics.error(ErrorCode::E_PARSE,
                    "fond_policy requires policy_size in 1..64");
                return result;
            }
            policy_size = static_cast<unsigned>(std::stoul(size));
            if (!policy_size || policy_size > 64) {
                result.diagnostics.error(ErrorCode::E_PARSE, "policy_size must be in 1..64");
                return result;
            }
        } else if (size_option != options.options.end()) {
            result.diagnostics.error(ErrorCode::E_PARSE,
                "policy_size requires an explicit fond_policy fairness choice");
            return result;
        }

        const auto horizon_option = options.options.find("plan_horizon");
        if (horizon_option == options.options.end() && policy_mode.empty()) {
            result.diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "no plan horizon: pass `plan_horizon=<k>`; there is deliberately no "
                "default because completeness is relative to this bound");
            return result;
        }
        const std::string text = horizon_option == options.options.end() ? "0" : horizon_option->second;
        if (text.empty()
            || !std::all_of(text.begin(), text.end(),
                            [](unsigned char c) { return std::isdigit(c) != 0; })) {
            result.diagnostics.error(ErrorCode::E_PARSE,
                                     "plan_horizon must be a non-negative decimal integer");
            return result;
        }
        unsigned long long parsed = 0;
        try {
            parsed = std::stoull(text);
        } catch (const std::exception&) {
            result.diagnostics.error(ErrorCode::E_PARSE,
                                     "plan_horizon is outside the supported integer range");
            return result;
        }
        if (parsed > UINT_MAX) {
            result.diagnostics.error(ErrorCode::E_PARSE,
                                     "plan_horizon exceeds the frontend's supported range");
            return result;
        }

        const std::string name = unit.main_path.empty() ? unit.display_name
                                                         : unit.main_path;
        try {
            PddlInternal::ClassicalEncoding encoding;
            bool uses_policy = false;
            {
                PddlParser parser(domain, problem, name, static_cast<unsigned>(parsed));
                parser.setLenientRequirements(PddlInternal::lenientRequirements(options));
                parser.setPolicy(policy_mode, policy_size);
                parser.setHasHorizon(horizon_option != options.options.end());
                result.model = parser.parse(result.diagnostics, result.report);
                uses_policy = parser.usesPolicy();
                if (result.model) {
                    encoding.projection = parser.takeModelProjection();
                    encoding.source_signature = parser.takeSourceSignature();
                    encoding.symbol_map = parser.takeSymbolMap();
                    encoding.target_axioms = parser.takeTargetAxioms();
                }
            }
            // The completed HIR and semantic metadata own their contents.
            // Release source syntax, grounded actions and name indexes before
            // building the contract's signatures and checking the next stage.
            if (result.model) {
                result.semantics.add(S::pddlToRelationalContract(
                    *result.model, result.report.fidelity(),
                    std::move(encoding.projection), std::move(encoding.source_signature),
                    std::move(encoding.symbol_map), std::move(encoding.target_axioms),
                    uses_policy ? policy_mode : std::string{}));
            }
        } catch (const std::exception& error) {
            result.model = nullptr;
            result.diagnostics.error(ErrorCode::E_INTERNAL,
                                     std::string("pddl frontend: ") + error.what());
        }
        return result;
    }

private:
    OpCoverage coverage_;
};

} // namespace

bool PddlInternal::lenientRequirements(const Lang::ParseOptions& options) {
    const auto it = options.options.find("lenient_requirements");
    if (it == options.options.end()) { return false; }
    // Anything but an explicit off is on, so `lenient_requirements=` with no
    // value does not silently mean strict -- a flag that reads as its own
    // opposite is worse than one that is not there.
    return it->second != "0" && it->second != "false" && it->second != "off";
}

PddlInternal::ClassicalEncoding PddlInternal::buildClassicalEncoding(
    const std::string& domain, const std::string& problem,
    const std::string& display_name, unsigned horizon,
    Uir::Diagnostics& diagnostics, Uir::TranslationReport& report,
    bool lenient_requirements, const PddlInternal::ActionInstances* allowed_actions,
    bool multiple_inheritance) {
    PddlInternal::ClassicalEncoding result;
    PddlParser parser(domain, problem, display_name, horizon);
    parser.setLenientRequirements(lenient_requirements);
    parser.setAllowedActions(allowed_actions);
    parser.setMultipleInheritance(multiple_inheritance);
    result.model = parser.parse(diagnostics, report);
    if (!result.model) { return result; }
    result.projection = parser.takeModelProjection();
    result.source_signature = parser.takeSourceSignature();
    result.symbol_map = parser.takeSymbolMap();
    result.target_axioms = parser.takeTargetAxioms();
    return result;
}

LanguagePtr mkPddlLanguage() { return std::make_shared<PddlLanguage>(); }

} // namespace SOMTParser::Lang
