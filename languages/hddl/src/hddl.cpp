/* -*- Source -*-
 * HDDL bounded hierarchical-planning frontend.
 *
 * The hierarchy is not erased.  Abstract tasks are expanded through grounded
 * methods into partially ordered primitive frontiers.  Every topological
 * linearization within the two explicit bounds is related to the action-choice
 * coordinates produced by the shared PDDL transition encoder.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/hddl.h"
#include "somtparser/languages/pddl_internal.h"
#include "somtparser/languages/planning_types.h"

#include <algorithm>
#include <cctype>
#include <climits>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iterator>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <system_error>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
namespace S = Uir::Sem;
using Uir::ErrorCode;

constexpr std::size_t EXPANSION_LIMIT = 100000;

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
        // A leading '-' is a typing separator, even without following space.
        // Internal hyphens in names and signed numeric literals stay intact.
        if (source_[at_] == '-' && at_ + 1 < source_.size()
            && std::isalpha(static_cast<unsigned char>(source_[at_ + 1]))) {
            ++at_;
            result.atom = "-";
            return true;
        }
        const std::size_t begin = at_;
        while (at_ < source_.size()
               && !std::isspace(static_cast<unsigned char>(source_[at_]))
               && source_[at_] != '(' && source_[at_] != ')' && source_[at_] != ';') {
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

std::string printSexp(const Sexp& expression) {
    if (expression.isAtom()) { return expression.atom; }
    std::string result = "(";
    for (std::size_t i = 0; i < expression.list.size(); ++i) {
        if (i != 0) { result += " "; }
        result += printSexp(expression.list[i]);
    }
    return result + ")";
}

bool emptyConjunction(const Sexp& expression) {
    return !expression.isAtom() && (expression.list.empty()
        || (expression.head() == "and" && expression.list.size() == 1));
}

struct Typed {
    std::string name;
    std::string type = "object";
};

struct TaskSchema {
    std::string        name;
    std::vector<Typed> params;
    bool               primitive = false;
};

struct TaskCall {
    std::string              name;
    std::vector<std::string> terms;
};

struct NetworkSyntax {
    std::vector<std::string> labels;
    std::vector<TaskCall>    tasks;
    std::vector<std::pair<std::size_t, std::size_t>> edges;
};

struct BindingConstraint {
    std::string left;
    std::string right;
    bool equal = true;
};

struct MethodSchema {
    std::string        name;
    std::vector<Typed> params;
    TaskCall           head;
    NetworkSyntax      network;
    std::optional<Sexp> precondition;
    std::optional<Sexp> effect;
    std::vector<BindingConstraint> bindings;
};

struct GroundTask {
    std::string label;
    bool        primitive = false;
    std::string name;
    std::vector<std::string> args;
};

struct GroundNetwork {
    std::vector<GroundTask> tasks;
    std::vector<std::pair<std::size_t, std::size_t>> edges;
};

struct PartialPlan {
    std::vector<std::string> primitives;
    std::set<std::pair<std::size_t, std::size_t>> edges;
};

using Environment = std::unordered_map<std::string, std::string>;

std::string sourceCall(const std::string& name,
                       const std::vector<std::string>& args) {
    std::string result = "(" + name;
    for (const std::string& arg : args) { result += " " + arg; }
    return result + ")";
}

H::ExprPtr conjunction(std::vector<H::ExprPtr> terms) {
    if (terms.empty()) { return H::mkBool(true); }
    if (terms.size() == 1) { return std::move(terms.front()); }
    return H::mkOp(H::Op::AND, std::move(terms));
}

H::ExprPtr disjunction(std::vector<H::ExprPtr> terms) {
    if (terms.empty()) { return H::mkBool(false); }
    if (terms.size() == 1) { return std::move(terms.front()); }
    return H::mkOp(H::Op::OR, std::move(terms));
}

// Factor an OR of conjunctions without enumerating truth assignments. A trie
// shares common prefixes; bottom-up interning also shares identical suffixes.
// Every edge denotes the original conjunct, so only Boolean distributivity
// is used, including when different conjuncts have semantic dependencies.
class FrontierFormula {
public:
    void add(const std::vector<H::ExprPtr>& terms) {
        std::size_t node = 0;
        for (const auto& term : terms) {
            auto entry = terms_.emplace(term.get(), expressions_.size());
            if (entry.second) { expressions_.push_back(term); }
            const auto id = entry.first->second;
            auto child = nodes_[node].children.find(id);
            if (child == nodes_[node].children.end()) {
                const auto next = nodes_.size();
                nodes_[node].children.emplace(id, next);
                nodes_.push_back({});
                node = next;
            } else { node = child->second; }
        }
        nodes_[node].terminal = true;
    }

    H::ExprPtr formula() const {
        using Key = std::vector<std::pair<std::size_t, std::size_t>>;
        std::map<Key, std::size_t> interned;
        std::vector<H::ExprPtr> formulas{H::mkBool(false), H::mkBool(true)};
        std::vector<std::size_t> ids(nodes_.size(), 0);
        interned.emplace(Key{}, 0);
        for (std::size_t at = nodes_.size(); at-- > 0;) {
            const auto& node = nodes_[at];
            if (node.terminal) { ids[at] = 1; continue; }
            Key key;
            for (const auto& [term, child] : node.children) {
                if (ids[child] != 0) { key.emplace_back(term, ids[child]); }
            }
            auto found = interned.find(key);
            if (found != interned.end()) { ids[at] = found->second; continue; }
            std::vector<H::ExprPtr> alternatives;
            for (const auto& [term, child] : key) {
                alternatives.push_back(child == 1 ? expressions_[term]
                    : conjunction({expressions_[term], formulas[child]}));
            }
            ids[at] = formulas.size();
            interned.emplace(std::move(key), ids[at]);
            formulas.push_back(disjunction(std::move(alternatives)));
        }
        return formulas[ids[0]];
    }

private:
    struct Node {
        std::map<std::size_t, std::size_t> children;
        bool terminal = false;
    };
    std::vector<Node> nodes_{1};
    std::map<const H::Expr*, std::size_t> terms_;
    std::vector<H::ExprPtr> expressions_;
};

class HddlParser {
public:
    HddlParser(std::string domain, std::string problem, std::string file,
               unsigned horizon, unsigned depth)
        : domain_text_(std::move(domain)), problem_text_(std::move(problem)),
          file_(std::move(file)), horizon_(horizon), depth_(depth) {
        types_.emplace("object", std::set<std::string>{});
    }

    /** Forwarded to the shared classical checker; see PDDL's requireFeature. */
    void setLenientRequirements(bool on) { lenient_requirements_ = on; }
    void setIpcCompatibility(bool on) { ipc_compatibility_ = on; }

    PddlInternal::ClassicalEncoding parse(Uir::Diagnostics& diagnostics,
                                          Uir::TranslationReport& report) {
        PddlInternal::ClassicalEncoding result;
        if (!readInputs(diagnostics) || !validate(diagnostics)
            || !compileMethodState(diagnostics)
            || !groundHierarchy(diagnostics)) {
            return result;
        }

        std::vector<PartialPlan> frontiers;
        for (const GroundNetwork& initial : initial_networks_) {
            auto plans = expandNetwork(initial, depth_, diagnostics);
            if (diagnostics.hasErrors()) { return result; }
            for (PartialPlan& plan : plans) {
                if (sourceLength(plan.primitives) > horizon_) { continue; }
                frontiers.push_back(std::move(plan));
            }
        }
        // Frontiers own their labels and precedence edges. Grounding caches
        // are no longer used by classical encoding or the hierarchy formula.
        ground_methods_.clear();
        memo_.clear();
        std::vector<GroundNetwork>{}.swap(initial_networks_);
        initial_relations_.clear();
        method_joins_.clear();

        // Method events are real state transitions, but not source primitive
        // actions. Derive the execution capacity from the complete bounded
        // frontier set; charging them to PLAN_HORIZON would lose valid plans.
        execution_horizon_ = horizon_;
        for (const auto& plan : frontiers) {
            if (plan.primitives.size() > EXPANSION_LIMIT) {
                diagnostics.error(ErrorCode::E_RESOURCE,
                                  "HDDL compiled execution exceeds the resource guard");
                return result;
            }
            execution_horizon_ = std::max(execution_horizon_,
                                          static_cast<unsigned>(plan.primitives.size()));
        }
        Uir::TranslationReport classical_report;
        PddlInternal::ActionInstances allowed_actions;
        std::set<std::string> labels;
        for (const auto& plan : frontiers) {
            labels.insert(plan.primitives.begin(), plan.primitives.end());
        }
        for (const auto& label : labels) {
            std::vector<Sexp> parsed;
            SexpReader reader(label);
            if (!reader.readAll(parsed) || parsed.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL, "invalid generated HDDL action label");
                return result;
            }
            std::vector<std::string> args;
            for (std::size_t i = 1; i < parsed[0].list.size(); ++i) {
                args.push_back(parsed[0].list[i].atom);
            }
            allowed_actions[parsed[0].head()].push_back(std::move(args));
        }
        result = PddlInternal::buildClassicalEncoding(
            sanitized_domain_, sanitized_problem_, file_, execution_horizon_, diagnostics,
            classical_report,
            lenient_requirements_, &allowed_actions, ipc_compatibility_);
        if (!result.model) { return result; }

        for (auto choice : classical_report.choices()) {
            if (!prefix_methods_.empty() && choice.unified_op == "plan-existence") {
                for (auto& bound : choice.fidelity.bounds) {
                    if (bound.kind == Uir::Fidelity::Bound::PLAN_HORIZON) {
                        bound.value = horizon_;
                    }
                }
                choice.strategy = "bounded-htn-method-execution";
                choice.rationale = "PLAN_HORIZON counts source primitive actions. The "
                    "hierarchy admits at most " + std::to_string(horizon_)
                    + " such actions. Method prefix events are additional state "
                      "transitions; execution capacity " + std::to_string(execution_horizon_)
                    + " is derived from all admitted frontiers, not an extra source bound.";
            }
            report.addChoice(std::move(choice));
        }
        for (const auto& warning : classical_report.warnings()) { report.addWarning(warning); }

        H::ExprPtr hierarchy = hierarchyFormula(frontiers, result, diagnostics);
        if (!hierarchy) {
            result.model.reset();
            return result;
        }
        H::Constraint constraint;
        constraint.formula = std::move(hierarchy);
        result.model->constraints.push_back(std::move(constraint));
        projectMethodEvents(result);

        Uir::EncodingChoice choice;
        choice.site = file_;
        choice.unified_op = "htn-decomposition";
        choice.strategy = "bounded-partial-order-expansion";
        Uir::Fidelity::Bound bound;
        bound.kind = Uir::Fidelity::Bound::DECOMPOSITION_DEPTH;
        bound.value = static_cast<int64_t>(depth_);
        bound.site = file_;
        choice.fidelity = Uir::Fidelity::underApprox(bound);
        choice.rationale =
            "ground method expansion preserves task-network precedence and admits "
            "exactly its primitive linearizations up to DECOMPOSITION_DEPTH "
            + std::to_string(depth_) + "; together with PLAN_HORIZON "
            + std::to_string(horizon_)
            + ", target SAT decodes to a real HDDL plan while target UNSAT is "
              "only a bounded negative result";
        report.addChoice(std::move(choice));
        for (const auto& normalization : ipc_normalizations_) {
            Uir::EncodingChoice compatibility;
            compatibility.site = file_;
            compatibility.unified_op = "source-dialect";
            compatibility.strategy = "ipc-hddl-compatibility";
            compatibility.fidelity = Uir::Fidelity::exact();
            compatibility.rationale = normalization;
            report.addChoice(std::move(compatibility));
            report.addWarning({Uir::Severity::WARNING, ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                               normalization, {}});
        }
        if (relaxed_method_state_) {
            Uir::EncodingChoice relaxed;
            relaxed.site = file_;
            relaxed.unified_op = "requirements";
            relaxed.strategy = "lenient-requirements";
            relaxed.fidelity = Uir::Fidelity::exact();
            relaxed.rationale = "assumed undeclared :htn-method-pre-eff; method state "
                                "conditions/effects use the reference prefix-task compilation";
            report.addChoice(std::move(relaxed));
        }
        return result;
    }

private:
    bool parseBindings(const Sexp& expression, std::vector<BindingConstraint>& bindings,
                       Uir::Diagnostics& diagnostics) const {
        if (emptyConjunction(expression)) { return true; }
        if (expression.head() == "and") {
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                if (!parseBindings(expression.list[i], bindings, diagnostics)) { return false; }
            }
            return true;
        }
        const bool negated = expression.head() == "not";
        const Sexp* equality = &expression;
        if (negated && expression.list.size() == 2) { equality = &expression.list[1]; }
        if ((negated && expression.list.size() != 2) || equality->head() != "="
            || equality->list.size() != 3) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "HDDL binding constraints require conjunctions of object "
                              "equalities or disequalities, not state formulas");
            return false;
        }
        for (std::size_t i = 1; i < 3; ++i) {
            const Sexp& term = equality->list[i];
            if (!term.isAtom() || (!isVariable(term.atom) && !isName(term.atom))) {
                diagnostics.error(ErrorCode::E_PARSE, "invalid HDDL binding constraint term");
                return false;
            }
        }
        bindings.push_back({equality->list[1].atom, equality->list[2].atom, !negated});
        return true;
    }

    // Object equality is independent of the execution state. A conjunctive
    // equality/disequality in a method condition can filter substitutions
    // before producing a task network; keep the original state condition too.
    static void collectMandatoryBindings(const Sexp& condition,
                                         std::vector<BindingConstraint>& bindings) {
        if (condition.head() == "and") {
            for (std::size_t i = 1; i < condition.list.size(); ++i) {
                collectMandatoryBindings(condition.list[i], bindings);
            }
            return;
        }
        const bool negated = condition.head() == "not";
        const Sexp* equality = &condition;
        if (negated && condition.list.size() == 2) { equality = &condition.list[1]; }
        if ((negated && condition.list.size() != 2) || equality->head() != "="
            || equality->list.size() != 3) { return; }
        for (std::size_t i = 1; i < 3; ++i) {
            const Sexp& term = equality->list[i];
            if (!term.isAtom() || (!isVariable(term.atom) && !isName(term.atom))) { return; }
        }
        bindings.push_back({equality->list[1].atom, equality->list[2].atom, !negated});
    }

    static bool bindingsPossible(const std::vector<BindingConstraint>& bindings,
                                 const Environment& environment) {
        const auto value = [&](const std::string& term) -> const std::string* {
            if (!isVariable(term)) { return &term; }
            const auto found = environment.find(term);
            return found == environment.end() ? nullptr : &found->second;
        };
        for (const auto& binding : bindings) {
            if (binding.left == binding.right && !binding.equal) { return false; }
            const auto* left = value(binding.left);
            const auto* right = value(binding.right);
            if (left && right && ((*left == *right) != binding.equal)) { return false; }
        }
        return true;
    }

    bool validateBindings(const std::vector<BindingConstraint>& bindings,
                          const std::map<std::string, std::string>& variables,
                          Uir::Diagnostics& diagnostics) const {
        for (const auto& binding : bindings) {
            for (const auto& term : {binding.left, binding.right}) {
                if ((isVariable(term) && !variables.count(term))
                    || (!isVariable(term) && !object_types_.count(term))) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "undeclared term '" + term + "' in HDDL binding constraint");
                    return false;
                }
            }
        }
        return true;
    }

    static bool bindingsHold(const std::vector<BindingConstraint>& bindings,
                             const Environment& environment) {
        const auto value = [&](const std::string& term) -> const std::string& {
            return isVariable(term) ? environment.at(term) : term;
        };
        return std::all_of(bindings.begin(), bindings.end(), [&](const BindingConstraint& c) {
            return (value(c.left) == value(c.right)) == c.equal;
        });
    }

    static bool containsAtom(const Sexp& expression, const std::string& atom) {
        if (expression.isAtom()) { return expression.atom == atom; }
        return std::any_of(expression.list.begin(), expression.list.end(),
            [&](const Sexp& child) { return containsAtom(child, atom); });
    }

    static void addedPredicates(const Sexp& effect, std::set<std::string>& added) {
        const auto& head = effect.head();
        if (head.empty() || head == "not" || head == "increase") { return; }
        if (head == "and") {
            for (std::size_t i = 1; i < effect.list.size(); ++i) {
                addedPredicates(effect.list[i], added);
            }
        } else if (head == "when" || head == "forall") {
            if (effect.list.size() == 3) { addedPredicates(effect.list[2], added); }
        } else {
            added.insert(head);
        }
    }

    void collectMethodJoins(const Sexp& condition, const std::set<std::string>& added,
                            std::vector<TaskCall>& joins) {
        const auto& head = condition.head();
        if (head == "and") {
            for (std::size_t i = 1; i < condition.list.size(); ++i) {
                collectMethodJoins(condition.list[i], added, joins);
            }
            return;
        }
        if (head.empty() || head == "not" || head == "or" || head == "imply"
            || head == "forall" || head == "exists" || head == "=" || added.count(head)) {
            return;
        }
        TaskCall call;
        call.name = head;
        for (std::size_t i = 1; i < condition.list.size(); ++i) {
            if (!condition.list[i].isAtom()) { return; }
            call.terms.push_back(condition.list[i].atom);
        }
        joins.push_back(std::move(call));
    }

    void prepareMethodJoins(const Sexp& domain) {
        std::set<std::string> added;
        for (const auto& section : domain.list) {
            if (section.head() != ":action") { continue; }
            for (std::size_t i = 2; i + 1 < section.list.size(); ++i) {
                if (section.list[i].atom == ":effect") { addedPredicates(section.list[i + 1], added); }
            }
        }
        for (const auto& method : methods_) {
            if (method.effect) { addedPredicates(*method.effect, added); }
        }
        std::map<std::string, std::vector<TaskCall>> action_joins;
        for (const auto& section : domain.list) {
            if (section.head() != ":action") { continue; }
            for (std::size_t i = 2; i + 1 < section.list.size(); ++i) {
                if (section.list[i].atom == ":precondition") {
                    collectMethodJoins(section.list[i + 1], added,
                                       action_joins[section.list[1].atom]);
                }
            }
        }
        for (const auto& method : methods_) {
            auto& joins = method_joins_[method.name];
            if (method.precondition) {
                collectMethodJoins(*method.precondition, added, joins);
            }
            // Every direct primitive child must eventually execute. A
            // mandatory condition on a never-added relation must already be
            // present initially, regardless of ordering or intervening steps.
            for (const auto& call : method.network.tasks) {
                const auto schema = tasks_.find(call.name);
                const auto conditions = action_joins.find(call.name);
                if (schema == tasks_.end() || !schema->second.primitive
                    || conditions == action_joins.end()
                    || call.terms.size() != schema->second.params.size()) { continue; }
                for (auto condition : conditions->second) {
                    bool valid = true;
                    for (auto& term : condition.terms) {
                        if (!isVariable(term)) { continue; }
                        const auto parameter = std::find_if(schema->second.params.begin(),
                            schema->second.params.end(), [&](const auto& p) { return p.name == term; });
                        if (parameter == schema->second.params.end()) { valid = false; break; }
                        term = call.terms[static_cast<std::size_t>(parameter - schema->second.params.begin())];
                    }
                    if (valid) { joins.push_back(std::move(condition)); }
                }
            }
            for (const auto& condition : joins) { initial_relations_.try_emplace(condition.name); }
        }
    }

    bool compileMethodState(Uir::Diagnostics&) {
        for (auto& method : methods_) {
            if (!method.precondition && !method.effect) { continue; }
            std::string name = "somt-hddl-method-" + std::to_string(prefix_methods_.size());
            while (tasks_.count(name)) { name += "x"; }
            prefix_methods_.emplace(name, method.name);
            TaskSchema action;
            action.name = name;
            action.primitive = true;
            TaskCall call;
            call.name = name;
            Sexp parameters;
            for (const auto& parameter : method.params) {
                // Keep the parameters relevant to the state step. Carrying
                // every head parameter would Cartesian-ground unused objects.
                if ((!method.precondition || !containsAtom(*method.precondition, parameter.name))
                    && (!method.effect || !containsAtom(*method.effect, parameter.name))) {
                    continue;
                }
                action.params.push_back(parameter);
                call.terms.push_back(parameter.name);
                parameters.list.push_back({parameter.name, {}});
                // Every item needs a separator: an omitted root annotation
                // would inherit the next parameter's non-root type.
                parameters.list.push_back({"-", {}});
                parameters.list.push_back({parameter.type, {}});
            }
            Sexp schema{"", {{":action", {}}, {name, {}}, {":parameters", {}}, parameters}};
            if (method.precondition) {
                schema.list.push_back({":precondition", {}});
                schema.list.push_back(*method.precondition);
            }
            if (method.effect) {
                schema.list.push_back({":effect", {}});
                schema.list.push_back(*method.effect);
            }
            classical_domain_.list.push_back(std::move(schema));
            tasks_.emplace(name, std::move(action));
            const auto prefix = method.network.tasks.size();
            for (std::size_t i = 0; i < prefix; ++i) {
                method.network.edges.emplace_back(prefix, i);
            }
            method.network.tasks.push_back(std::move(call));
            method.network.labels.push_back("__method_state");
        }
        sanitized_domain_ = printSexp(classical_domain_);
        return true;
    }

    std::string methodEvent(const std::string& label) const {
        if (label.empty() || label[0] != '(') { return {}; }
        const auto end = label.find_first_of(" )", 1);
        if (end == std::string::npos) { return {}; }
        const auto method = prefix_methods_.find(label.substr(1, end - 1));
        if (method == prefix_methods_.end()) { return {}; }
        return "(method " + method->second + label.substr(end);
    }

    std::size_t sourceLength(const std::vector<std::string>& sequence) const {
        return static_cast<std::size_t>(std::count_if(sequence.begin(), sequence.end(),
            [&](const std::string& label) { return methodEvent(label).empty(); }));
    }

    void projectMethodEvents(PddlInternal::ClassicalEncoding& result) const {
        if (prefix_methods_.empty()) { return; }
        std::vector<S::ChoiceObservable> events;
        for (std::size_t step = 0; step < result.projection.choices.size(); ++step) {
            auto& primitive = result.projection.choices[step];
            S::ChoiceObservable event;
            event.source_name = "method[" + std::to_string(step) + "]";
            event.omit_label = "__hddl_no_method_event";
            for (auto& alternative : primitive.alternatives) {
                const auto label = methodEvent(alternative.label);
                event.alternatives.push_back(
                    {label.empty() ? event.omit_label : label, alternative.target_name});
                if (!label.empty()) { alternative.label = primitive.omit_label; }
            }
            events.push_back(std::move(event));
        }
        result.projection.choices.insert(result.projection.choices.end(),
                                         events.begin(), events.end());
        // Phi names method events as source events, not generated PDDL actions.
        const auto rename = [&](const std::string& name) {
            const auto at = name.find("::");
            if (at == std::string::npos) { return name; }
            const auto event = methodEvent(name.substr(at + 2));
            return event.empty() ? name : "method-" + name.substr(0, at + 2) + event;
        };
        for (auto& symbol : result.source_signature.symbols) { symbol.name = rename(symbol.name); }
        for (auto& mapping : result.symbol_map) { mapping.source = rename(mapping.source); }
    }

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
        if (!reader.readAll(roots) || roots.size() != 1
            || roots[0].head() != "define") {
            diagnostics.error(ErrorCode::E_PARSE,
                              "the HDDL " + kind
                                  + " file must contain exactly one well-formed `(define ...)`");
            return false;
        }
        result = std::move(roots[0]);
        return true;
    }

    bool typedList(const Sexp& expression, std::size_t from, bool variables,
                   const std::string& context, std::vector<Typed>& result,
                   Uir::Diagnostics& diagnostics, bool repeated_types = false) const {
        std::vector<std::string> pending;
        std::set<std::string> names;
        const auto flush = [&](const std::string& type) {
            for (const std::string& name : pending) {
                if (!names.insert(name).second && !repeated_types) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "duplicate '" + name + "' in " + context);
                    return false;
                }
                result.push_back({name, type});
            }
            pending.clear();
            return true;
        };
        for (std::size_t i = from; i < expression.list.size(); ++i) {
            const Sexp& item = expression.list[i];
            if (!item.isAtom()) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  context + " uses a compound type");
                return false;
            }
            if (item.atom == "-") {
                if (pending.empty() || i + 1 >= expression.list.size()
                    || !expression.list[i + 1].isAtom()
                    || !isName(expression.list[i + 1].atom)) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed typed list in " + context);
                    return false;
                }
                if (!flush(expression.list[++i].atom)) { return false; }
                continue;
            }
            if ((variables && !isVariable(item.atom))
                || (!variables && !isName(item.atom))) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "invalid name '" + item.atom + "' in " + context);
                return false;
            }
            pending.push_back(item.atom);
        }
        return flush("object");
    }

    bool parseCall(const Sexp& expression, const std::string& context,
                   TaskCall& result, Uir::Diagnostics& diagnostics) const {
        if (expression.list.empty() || !expression.list[0].isAtom()
            || !isName(expression.list[0].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed task call in " + context);
            return false;
        }
        result.name = expression.list[0].atom;
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            if (!expression.list[i].isAtom()
                || (!isVariable(expression.list[i].atom)
                    && !isName(expression.list[i].atom))) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed task argument in " + context);
                return false;
            }
            result.terms.push_back(expression.list[i].atom);
        }
        return true;
    }

    bool parseNetwork(const Sexp& tasks_expression, bool ordered,
                      const std::optional<Sexp>& ordering,
                      const std::string& context, NetworkSyntax& result,
                      Uir::Diagnostics& diagnostics) const {
        std::vector<Sexp> occurrences;
        if (tasks_expression.head() == "and") {
            occurrences.assign(tasks_expression.list.begin() + 1,
                               tasks_expression.list.end());
        } else if (tasks_expression.list.empty()) {
            occurrences.clear();
        } else {
            occurrences.push_back(tasks_expression);
        }

        std::map<std::string, std::size_t> label_index;
        for (std::size_t i = 0; i < occurrences.size(); ++i) {
            const Sexp* call = &occurrences[i];
            std::string label = "__task_" + std::to_string(i);
            if (occurrences[i].list.size() == 2
                && occurrences[i].list[0].isAtom()
                && !occurrences[i].list[1].isAtom()) {
                label = occurrences[i].list[0].atom;
                call = &occurrences[i].list[1];
                if (!isName(label)) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "invalid subtask identifier '" + label
                                          + "' in " + context);
                    return false;
                }
            }
            if (!label_index.emplace(label, i).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate subtask identifier '" + label
                                      + "' in " + context);
                return false;
            }
            TaskCall parsed;
            if (!parseCall(*call, context, parsed, diagnostics)) { return false; }
            result.labels.push_back(label);
            result.tasks.push_back(std::move(parsed));
            if (ordered && i != 0) { result.edges.emplace_back(i - 1, i); }
        }

        if (ordering) {
            std::vector<Sexp> relations;
            if (ordering->head() == "and") {
                relations.assign(ordering->list.begin() + 1, ordering->list.end());
            } else if (!ordering->list.empty()) {
                relations.push_back(*ordering);
            }
            for (const Sexp& relation : relations) {
                if (relation.list.size() != 3 || relation.head() != "<"
                    || !relation.list[1].isAtom() || !relation.list[2].isAtom()) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed ordering relation in " + context);
                    return false;
                }
                const auto before = label_index.find(relation.list[1].atom);
                const auto after = label_index.find(relation.list[2].atom);
                if (before == label_index.end() || after == label_index.end()) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "ordering in " + context
                                          + " references an unknown subtask identifier");
                    return false;
                }
                result.edges.emplace_back(before->second, after->second);
            }
        }
        return acyclic(result.tasks.size(), result.edges, context, diagnostics);
    }

    static bool acyclic(std::size_t count,
                        const std::vector<std::pair<std::size_t, std::size_t>>& edges,
                        const std::string& context, Uir::Diagnostics& diagnostics) {
        std::vector<unsigned> indegree(count, 0);
        std::vector<std::vector<std::size_t>> successors(count);
        for (const auto& [from, to] : edges) {
            if (from == to || from >= count || to >= count) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "self or out-of-range ordering in " + context);
                return false;
            }
            successors[from].push_back(to);
            ++indegree[to];
        }
        std::vector<std::size_t> ready;
        for (std::size_t i = 0; i < count; ++i) {
            if (indegree[i] == 0) { ready.push_back(i); }
        }
        std::size_t seen = 0;
        while (!ready.empty()) {
            const std::size_t at = ready.back();
            ready.pop_back();
            ++seen;
            for (std::size_t next : successors[at]) {
                if (--indegree[next] == 0) { ready.push_back(next); }
            }
        }
        if (seen != count) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "cyclic task ordering in " + context);
            return false;
        }
        return true;
    }

    bool parseTaskSection(const Sexp& section, Uir::Diagnostics& diagnostics) {
        if (section.list.size() < 2 || !section.list[1].isAtom()
            || !isName(section.list[1].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed HDDL task declaration");
            return false;
        }
        TaskSchema task;
        task.name = section.list[1].atom;
        for (std::size_t i = 2; i < section.list.size();) {
            if (!section.list[i].isAtom() || i + 1 >= section.list.size()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed abstract task '" + task.name + "'");
                return false;
            }
            const std::string key = section.list[i].atom;
            const Sexp& value = section.list[i + 1];
            i += 2;
            if (key == ":parameters") {
                if (value.isAtom()
                    || !typedList(value, 0, true,
                                  "parameters of task '" + task.name + "'",
                                  task.params, diagnostics)) {
                    return false;
                }
            } else if (key == ":precondition" || key == ":effect") {
                if (!emptyConjunction(value)) {
                    diagnostics.error(
                        ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "abstract-task " + key
                            + " needs HDDL state semantics independent of method expansion");
                    return false;
                }
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unsupported abstract-task field '" + key + "'");
                return false;
            }
        }
        if (!tasks_.emplace(task.name, std::move(task)).second) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "duplicate task/action name '" + section.list[1].atom + "'");
            return false;
        }
        saw_hierarchy_ = true;
        return true;
    }

    bool parseActionSignature(const Sexp& section, Uir::Diagnostics& diagnostics) {
        if (section.list.size() < 2 || !section.list[1].isAtom()
            || !isName(section.list[1].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed HDDL action declaration");
            return false;
        }
        TaskSchema task;
        task.name = section.list[1].atom;
        task.primitive = true;
        for (std::size_t i = 2; i < section.list.size();) {
            if (!section.list[i].isAtom() || i + 1 >= section.list.size()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed action '" + task.name + "'");
                return false;
            }
            const std::string key = section.list[i].atom;
            const Sexp& value = section.list[i + 1];
            i += 2;
            if (key == ":parameters") {
                if (value.isAtom()
                    || !typedList(value, 0, true,
                                  "parameters of action '" + task.name + "'",
                                  task.params, diagnostics)) {
                    return false;
                }
            }
        }
        if (!tasks_.emplace(task.name, std::move(task)).second) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "duplicate task/action name '" + section.list[1].atom + "'");
            return false;
        }
        return true;
    }

    bool parseMethod(const Sexp& section, Uir::Diagnostics& diagnostics) {
        if (section.list.size() < 2 || !section.list[1].isAtom()
            || !isName(section.list[1].atom)) {
            diagnostics.error(ErrorCode::E_PARSE, "malformed HDDL method header");
            return false;
        }
        MethodSchema method;
        method.name = section.list[1].atom;
        std::optional<Sexp> subtasks;
        std::optional<Sexp> ordering;
        bool ordered = false;
        bool has_head = false;
        std::set<std::string> keys;
        for (std::size_t i = 2; i < section.list.size();) {
            if (!section.list[i].isAtom() || i + 1 >= section.list.size()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed method '" + method.name + "'");
                return false;
            }
            const std::string key = section.list[i].atom;
            const Sexp& value = section.list[i + 1];
            i += 2;
            if (!keys.insert(key).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate '" + key + "' in method '" + method.name + "'");
                return false;
            }
            if (key == ":parameters") {
                if (value.isAtom()
                    || !typedList(value, 0, true,
                                  "parameters of method '" + method.name + "'",
                                  method.params, diagnostics)) {
                    return false;
                }
            } else if (key == ":task") {
                if (!parseCall(value, "method head '" + method.name + "'",
                               method.head, diagnostics)) {
                    return false;
                }
                has_head = true;
            } else if (key == ":subtasks" || key == ":tasks"
                       || key == ":ordered-subtasks" || key == ":ordered-tasks") {
                if (subtasks) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "method '" + method.name
                                          + "' declares more than one subtask network");
                    return false;
                }
                subtasks = value;
                ordered = key == ":ordered-subtasks" || key == ":ordered-tasks";
            } else if (key == ":ordering") {
                ordering = value;
            } else if (key == ":precondition" || key == ":effect") {
                if (!emptyConjunction(value)) {
                    const bool declared = saw_method_pre_eff_
                        || (key == ":precondition" && saw_method_preconditions_);
                    if (!declared && !lenient_requirements_) {
                        diagnostics.error(ErrorCode::E_PARSE,
                            "method " + key + " needs the `:htn-method-pre-eff` requirement"
                            + (key == ":precondition" ? " or `:method-preconditions`" : ""));
                        return false;
                    }
                    if (!declared) {
                        relaxed_method_state_ = true;
                        diagnostics.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "assumed undeclared :htn-method-pre-eff because lenient_requirements is set");
                    }
                    if (key == ":precondition") { method.precondition = value; }
                    else { method.effect = value; }
                }
            } else if (key == ":constraints") {
                if (!parseBindings(value, method.bindings, diagnostics)) { return false; }
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unsupported method field '" + key + "'");
                return false;
            }
        }
        if (!has_head) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "method '" + method.name + "' requires one :task");
            return false;
        }
        // The reference syntax allows an omitted (empty) task network,
        // including methods whose only executable content is their effect.
        if (!parseNetwork(subtasks.value_or(Sexp{}), ordered, ordering,
                          "method '" + method.name + "'", method.network,
                          diagnostics)) {
            return false;
        }
        if (!method_names_.insert(method.name).second) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "duplicate method name '" + method.name + "'");
            return false;
        }
        if (method.precondition) {
            collectMandatoryBindings(*method.precondition, method.bindings);
        }
        methods_.push_back(std::move(method));
        saw_hierarchy_ = true;
        return true;
    }

    bool parseHtn(const Sexp& section, Uir::Diagnostics& diagnostics) {
        std::optional<Sexp> subtasks;
        std::optional<Sexp> ordering;
        bool ordered = false;
        std::set<std::string> keys;
        for (std::size_t i = 1; i < section.list.size();) {
            if (!section.list[i].isAtom() || i + 1 >= section.list.size()) {
                diagnostics.error(ErrorCode::E_PARSE, "malformed problem :htn section");
                return false;
            }
            const std::string key = section.list[i].atom;
            const Sexp& value = section.list[i + 1];
            i += 2;
            if (!keys.insert(key).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate '" + key + "' in problem :htn");
                return false;
            }
            if (key == ":parameters") {
                if (value.isAtom()
                    || !typedList(value, 0, true, "initial task-network parameters",
                                  initial_params_, diagnostics)) {
                    return false;
                }
            } else if (key == ":subtasks" || key == ":tasks"
                       || key == ":ordered-subtasks" || key == ":ordered-tasks") {
                if (subtasks) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "problem :htn declares multiple task networks");
                    return false;
                }
                subtasks = value;
                ordered = key == ":ordered-subtasks" || key == ":ordered-tasks";
            } else if (key == ":ordering") {
                ordering = value;
            } else if (key == ":constraints") {
                if (!parseBindings(value, initial_bindings_, diagnostics)) { return false; }
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unsupported problem :htn field '" + key + "'");
                return false;
            }
        }
        if (!subtasks) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "problem :htn requires a subtask network");
            return false;
        }
        saw_initial_htn_ = true;
        return parseNetwork(*subtasks, ordered, ordering, "initial task network",
                            initial_network_, diagnostics);
    }

    bool readInputs(Uir::Diagnostics& diagnostics) {
        if (!readSingle(domain_text_, "domain", domain_root_, diagnostics)
            || !readSingle(problem_text_, "problem", problem_root_, diagnostics)) {
            return false;
        }
        if (domain_root_.list.size() < 2 || domain_root_.list[1].head() != "domain"
            || problem_root_.list.size() < 2
            || problem_root_.list[1].head() != "problem") {
            diagnostics.error(ErrorCode::E_PARSE,
                              "malformed HDDL domain or problem header");
            return false;
        }

        // Scanned BEFORE the section loop rather than inside it. `:requirements`
        // conventionally comes first and in these files does, but a flag that a
        // refusal depends on must not depend on the order sections happen to
        // appear in: a domain declaring `:htn-method-pre-eff` after its methods
        // would otherwise be told it had not declared it.
        for (std::size_t i = 2; i < domain_root_.list.size(); ++i) {
            const Sexp& section = domain_root_.list[i];
            if (section.head() != ":requirements") { continue; }
            for (std::size_t r = 1; r < section.list.size(); ++r) {
                if (section.list[r].isAtom()
                    && section.list[r].atom == ":htn-method-pre-eff") {
                    saw_method_pre_eff_ = true;
                }
                if (section.list[r].isAtom()
                    && section.list[r].atom == ":method-preconditions") {
                    saw_method_preconditions_ = true;
                }
            }
        }

        Sexp clean_domain;
        clean_domain.list.assign(domain_root_.list.begin(), domain_root_.list.begin() + 2);
        for (std::size_t i = 2; i < domain_root_.list.size(); ++i) {
            const Sexp& section = domain_root_.list[i];
            const std::string head = section.head();
            if (head == ":requirements") {
                Sexp clean = section;
                clean.list.resize(1);
                for (std::size_t r = 1; r < section.list.size(); ++r) {
                    if (!section.list[r].isAtom()) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "malformed HDDL :requirements entry");
                        return false;
                    }
                    const std::string requirement = section.list[r].atom;
                    if (requirement == ":hierarchy" || requirement == ":hierachie"
                        || requirement == ":htn") {
                        saw_hierarchy_ = true;
                    } else if (requirement == ":method-preconditions") {
                        // IPC HDDL grants method preconditions, not effects.
                        saw_method_preconditions_ = true;
                    } else if (requirement == ":htn-method-pre-eff") {
                        // An HTN requirement, so it is consumed here for the
                        // reason `:hierarchy` is: the shared PDDL adapter
                        // checks requirements against the classical fragment
                        // and would report a perfectly good HDDL declaration
                        // as an unknown one.
                        saw_method_pre_eff_ = true;
                    } else {
                        clean.list.push_back(section.list[r]);
                    }
                }
                if (clean.list.size() > 1) { clean_domain.list.push_back(std::move(clean)); }
            } else if (head == ":types") {
                std::vector<Typed> declarations;
                if (!typedList(section, 1, false, "HDDL :types", declarations,
                               diagnostics, ipc_compatibility_)) {
                    return false;
                }
                Sexp clean;
                clean.list.push_back(Sexp{":types", {}});
                for (const Typed& declaration : declarations) {
                    // pandaPIparser's official fixtures use `(:types object)`.
                    // It is the identity declaration of the built-in root, so
                    // erase it before delegating to the stricter PDDL parser.
                    if (declaration.name == "object") {
                        if (declaration.type != "object") {
                            diagnostics.error(ErrorCode::E_PARSE,
                                              "the root type 'object' cannot have a parent");
                            return false;
                        }
                        continue;
                    }
                    if (types_.count(declaration.name) && !ipc_compatibility_) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "duplicate type '" + declaration.name + "'");
                        return false;
                    }
                    auto& parents = types_[declaration.name];
                    if (parents.insert(declaration.type).second && parents.size() > 1) {
                        const std::string message = "IPC HDDL dialect: type '"
                            + declaration.name + "' also inherits from '" + declaration.type + "'";
                        ipc_normalizations_.push_back(message);
                        diagnostics.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT, message);
                    }
                    clean.list.push_back(Sexp{declaration.name, {}});
                    // Typed lists group *all* pending names before '-'.
                    // Omitting '- object' can invent edges and even cycles.
                    clean.list.push_back(Sexp{"-", {}});
                    clean.list.push_back(Sexp{declaration.type, {}});
                }
                if (clean.list.size() > 1) {
                    clean_domain.list.push_back(std::move(clean));
                }
            } else if (head == ":constants") {
                if (!typedList(section, 1, false, "HDDL :constants", constants_,
                               diagnostics)) {
                    return false;
                }
                clean_domain.list.push_back(section);
            } else if (head == ":task") {
                if (!parseTaskSection(section, diagnostics)) { return false; }
            } else if (head == ":method") {
                if (!parseMethod(section, diagnostics)) { return false; }
            } else if (head == ":action") {
                if (!parseActionSignature(section, diagnostics)) { return false; }
                clean_domain.list.push_back(section);
            } else {
                clean_domain.list.push_back(section);
            }
        }

        if (ipc_compatibility_) {
            // pandaPIparser introduces sorts appearing on either side of a
            // type declaration. Complete only missing parents, after reading
            // every explicit declaration; never invent arbitrary term types.
            std::set<std::string> missing;
            for (const auto& [type, parents] : types_) {
                for (const auto& parent : parents) {
                    if (!types_.count(parent)) { missing.insert(parent); }
                }
            }
            if (!missing.empty()) {
                Sexp added{"", {{":types", {}}}};
                for (const auto& parent : missing) {
                    types_.emplace(parent, std::set<std::string>{"object"});
                    added.list.push_back({parent, {}});
                    added.list.push_back({"-", {}});
                    added.list.push_back({"object", {}});
                    const std::string message = "IPC HDDL dialect: parent-only type '"
                        + parent + "' is introduced under object";
                    ipc_normalizations_.push_back(message);
                    diagnostics.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT, message);
                }
                auto section = std::find_if(clean_domain.list.begin(), clean_domain.list.end(),
                    [](const Sexp& entry) { return entry.head() == ":types"; });
                if (section == clean_domain.list.end()) {
                    clean_domain.list.push_back(std::move(added));
                } else {
                    section->list.insert(section->list.end(), added.list.begin() + 1,
                                         added.list.end());
                }
            }
        }

        // A predicate with no positive effect can only lose initial tuples.
        // Its positive method conditions therefore admit a sparse, sound join
        // before local parameters are enumerated, even if actions delete it.
        prepareMethodJoins(clean_domain);
        Sexp clean_problem;
        clean_problem.list.assign(problem_root_.list.begin(), problem_root_.list.begin() + 2);
        bool has_goal = false;
        for (std::size_t i = 2; i < problem_root_.list.size(); ++i) {
            Sexp& section = problem_root_.list[i];
            const std::string head = section.head();
            if (head == ":domain" && ipc_compatibility_
                && section.list.size() == 2 && section.list[1].isAtom()
                && domain_root_.list[1].list.size() == 2
                && domain_root_.list[1].list[1].isAtom()
                && section.list[1].atom != domain_root_.list[1].list[1].atom) {
                // The caller supplies exactly one domain and one problem.
                // This opt-in follows the reference parser's file pairing,
                // without changing input files or suppressing schema checks.
                Sexp paired = section;
                paired.list[1] = domain_root_.list[1].list[1];
                const std::string message = "IPC HDDL dialect: problem domain name '"
                    + section.list[1].atom + "' paired with explicitly supplied domain '"
                    + paired.list[1].atom + "'";
                ipc_normalizations_.push_back(message);
                diagnostics.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT, message);
                clean_problem.list.push_back(std::move(paired));
            } else if (head == ":objects") {
                if (!typedList(section, 1, false, "HDDL :objects", objects_,
                               diagnostics)) {
                    return false;
                }
                Sexp clean = section;
                if (ipc_compatibility_) {
                    clean.list.resize(1);
                    std::vector<Typed> retained;
                    for (const auto& object : objects_) {
                        const auto constant = std::find_if(constants_.begin(), constants_.end(),
                            [&](const Typed& c) { return c.name == object.name; });
                        if (constant != constants_.end() && constant->type == object.type) {
                            const std::string message = "IPC HDDL dialect: repeated object '"
                                + object.name + "' denotes the existing domain constant of type '"
                                + object.type + "'";
                            ipc_normalizations_.push_back(message);
                            diagnostics.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT, message);
                            continue;
                        }
                        retained.push_back(object);
                        clean.list.push_back({object.name, {}});
                        clean.list.push_back({"-", {}});
                        clean.list.push_back({object.type, {}});
                    }
                    objects_ = std::move(retained);
                }
                clean_problem.list.push_back(std::move(clean));
            } else if (head == ":requirements") {
                Sexp clean = section;
                clean.list.resize(1);
                for (std::size_t r = 1; r < section.list.size(); ++r) {
                    if (!section.list[r].isAtom()) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "malformed HDDL problem :requirements entry");
                        return false;
                    }
                    const std::string requirement = section.list[r].atom;
                    if (requirement != ":hierarchy" && requirement != ":hierachie"
                        && requirement != ":htn") {
                        clean.list.push_back(section.list[r]);
                    }
                }
                if (clean.list.size() > 1) {
                    clean_problem.list.push_back(std::move(clean));
                }
            } else if (head == ":htn") {
                if (saw_initial_htn_) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "duplicate problem :htn section");
                    return false;
                }
                if (!parseHtn(section, diagnostics)) { return false; }
            } else {
                if (head == ":goal") { has_goal = true; }
                if (head == ":init") {
                    for (std::size_t j = 1; j < section.list.size(); ++j) {
                        const auto& fact = section.list[j];
                        auto relation = initial_relations_.find(fact.head());
                        if (relation == initial_relations_.end()) { continue; }
                        std::vector<std::string> tuple;
                        for (std::size_t k = 1; k < fact.list.size(); ++k) {
                            tuple.push_back(fact.list[k].atom);
                        }
                        relation->second.insert(std::move(tuple));
                    }
                }
                clean_problem.list.push_back(std::move(section));
            }
        }
        if (!has_goal) {
            Sexp goal;
            goal.list.push_back(Sexp{":goal", {}});
            Sexp truth;
            truth.list.push_back(Sexp{"and", {}});
            goal.list.push_back(std::move(truth));
            clean_problem.list.push_back(std::move(goal));
        }
        if (!saw_hierarchy_ || !saw_initial_htn_) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "HDDL requires hierarchy declarations and one problem :htn; "
                              "plain PDDL belongs to --from pddl");
            return false;
        }
        classical_domain_ = std::move(clean_domain);
        sanitized_domain_ = printSexp(classical_domain_);
        sanitized_problem_ = printSexp(clean_problem);
        // Only the normalized classical text is needed by the next parser.
        // Releasing the original trees avoids retaining the entire initial
        // fact table throughout classical parsing and HIR construction.
        domain_root_ = Sexp{};
        problem_root_ = Sexp{};
        std::string{}.swap(domain_text_);
        std::string{}.swap(problem_text_);
        return true;
    }

    bool validate(Uir::Diagnostics& diagnostics) {
        if (!PlanningInternal::validateTypes(types_, "HDDL", diagnostics)) { return false; }
        const auto typed = [&](const std::vector<Typed>& declarations,
                               const std::string& context) {
            for (const Typed& value : declarations) {
                if (types_.count(value.type) == 0) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      context + " uses unknown type '" + value.type + "'");
                    return false;
                }
            }
            return true;
        };
        for (const auto& [name, task] : tasks_) {
            if (!typed(task.params, "task/action '" + name + "'")) { return false; }
        }
        for (const MethodSchema& method : methods_) {
            if (!typed(method.params, "method '" + method.name + "'")) { return false; }
        }
        if (!typed(constants_, "domain constants") || !typed(objects_, "problem objects")
            || !typed(initial_params_, "initial task-network parameters")) {
            return false;
        }

        for (const Typed& object : constants_) {
            if (!object_types_.emplace(object.name, object.type).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate object/constant '" + object.name + "'");
                return false;
            }
        }
        for (const Typed& object : objects_) {
            if (!object_types_.emplace(object.name, object.type).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate object/constant '" + object.name + "'");
                return false;
            }
        }

        using TypeRequirements = std::map<std::string, std::set<std::string>>;
        const auto checkCall = [&](const TaskCall& call,
                                   const std::map<std::string, std::string>& variables,
                                   TypeRequirements& requirements,
                                   const std::string& context) {
            const auto task = tasks_.find(call.name);
            if (task == tasks_.end()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  context + " calls undeclared task/action '"
                                      + call.name + "'");
                return false;
            }
            if (call.terms.size() != task->second.params.size()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  context + " gives '" + call.name
                                      + "' the wrong arity");
                return false;
            }
            for (std::size_t i = 0; i < call.terms.size(); ++i) {
                const std::string& term = call.terms[i];
                std::string actual;
                if (isVariable(term)) {
                    const auto variable = variables.find(term);
                    if (variable == variables.end()) {
                        diagnostics.error(ErrorCode::E_TYPE,
                                          context + " uses undeclared variable '" + term + "'");
                        return false;
                    }
                    actual = variable->second;
                    if (ipc_compatibility_) {
                        // An unbound method/network variable denotes only
                        // substitutions satisfying every argument signature.
                        // Constants cannot be narrowed this way.
                        requirements[term].insert(task->second.params[i].type);
                        continue;
                    }
                } else {
                    const auto object = object_types_.find(term);
                    if (object == object_types_.end()) {
                        diagnostics.error(ErrorCode::E_TYPE,
                                          context + " uses undeclared constant '" + term + "'");
                        return false;
                    }
                    actual = object->second;
                }
                if (!isSubtype(actual, task->second.params[i].type)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      context + " passes '" + term + "' of type '"
                                          + actual + "' where '"
                                          + task->second.params[i].type + "' is required");
                    return false;
                }
            }
            return true;
        };

        bool refined = false;
        const auto refineParameters = [&](std::vector<Typed>& params,
                                           const TypeRequirements& requirements,
                                           const std::string& context) {
            for (auto& parameter : params) {
                const auto found = requirements.find(parameter.name);
                if (found == requirements.end()) { continue; }
                auto required = found->second;
                required.insert(parameter.type);
                const auto satisfies = [&](const std::string& type) {
                    return std::all_of(required.begin(), required.end(),
                        [&](const std::string& parent) { return isSubtype(type, parent); });
                };
                if (satisfies(parameter.type)) { continue; }
                std::string intersection;
                for (const auto& type : required) {
                    if (satisfies(type)) { intersection = type; break; }
                }
                if (intersection.empty()) {
                    // In a DAG two incomparable parents may have several
                    // common descendants. Retain all of them, not one chosen
                    // child. With no descendants the domain is correctly empty.
                    intersection = "somt-hddl-intersection-" + std::to_string(types_.size());
                    while (types_.count(intersection)) { intersection += "x"; }
                    std::vector<std::string> members;
                    for (const auto& [type, parents] : types_) {
                        if (satisfies(type)) { members.push_back(type); }
                    }
                    types_.emplace(intersection, required);
                    for (const auto& type : members) { types_.at(type).insert(intersection); }
                }
                std::string message = "IPC HDDL dialect: " + context + " parameter '"
                    + parameter.name + "' is restricted to the intersection of";
                for (const auto& type : required) { message += " '" + type + "'"; }
                ipc_normalizations_.push_back(message);
                diagnostics.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT, message);
                parameter.type = intersection;
                refined = true;
            }
        };

        for (MethodSchema& method : methods_) {
            const auto head = tasks_.find(method.head.name);
            if (head == tasks_.end() || head->second.primitive) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "method '" + method.name
                                      + "' head must name a declared abstract task");
                return false;
            }
            std::map<std::string, std::string> variables;
            for (const Typed& param : method.params) {
                variables.emplace(param.name, param.type);
            }
            TypeRequirements requirements;
            if (!validateBindings(method.bindings, variables, diagnostics)) { return false; }
            if (!checkCall(method.head, variables, requirements,
                           "method '" + method.name + "' head")) {
                return false;
            }
            for (const TaskCall& task : method.network.tasks) {
                if (!checkCall(task, variables, requirements, "method '" + method.name + "'")) {
                    return false;
                }
            }
            refineParameters(method.params, requirements, "method '" + method.name + "'");
        }
        std::map<std::string, std::string> initial_variables;
        for (const Typed& param : initial_params_) {
            initial_variables.emplace(param.name, param.type);
        }
        TypeRequirements initial_requirements;
        if (!validateBindings(initial_bindings_, initial_variables, diagnostics)) { return false; }
        for (const TaskCall& task : initial_network_.tasks) {
            if (!checkCall(task, initial_variables, initial_requirements, "initial task network")) {
                return false;
            }
        }
        refineParameters(initial_params_, initial_requirements, "initial task network");
        if (refined) {
            if (!PlanningInternal::validateTypes(types_, "HDDL", diagnostics)) { return false; }
            Sexp declarations{"", {{":types", {}}}};
            for (const auto& [type, parents] : types_) {
                for (const auto& parent : parents) {
                    declarations.list.push_back({type, {}});
                    declarations.list.push_back({"-", {}});
                    declarations.list.push_back({parent, {}});
                }
            }
            const auto section = std::find_if(classical_domain_.list.begin(),
                classical_domain_.list.end(), [](const Sexp& value) { return value.head() == ":types"; });
            if (section == classical_domain_.list.end()) {
                classical_domain_.list.push_back(std::move(declarations));
            } else { *section = std::move(declarations); }
        }
        return true;
    }

    bool isSubtype(std::string actual, const std::string& expected) const {
        return PlanningInternal::isSubtype(types_, actual, expected);
    }

    std::vector<std::string> objectsOfType(const std::string& type) const {
        std::vector<std::string> result;
        for (const auto& [object, actual] : object_types_) {
            if (isSubtype(actual, type)) { result.push_back(object); }
        }
        return result;
    }

    template <typename Callback>
    bool enumerateEnvironments(const std::vector<Typed>& params, Callback callback,
                               Uir::Diagnostics& diagnostics,
                               Environment environment = {}) {
        std::function<bool(std::size_t)> visit = [&](std::size_t at) {
            if (at == params.size()) { return callback(environment); }
            if (environment.count(params[at].name)) { return visit(at + 1); }
            const auto domain = objectsOfType(params[at].type);
            for (const std::string& object : domain) {
                environment[params[at].name] = object;
                if (!visit(at + 1)) { return false; }
            }
            environment.erase(params[at].name);
            return true;
        };
        const bool completed = visit(0);
        if (ground_count_ > EXPANSION_LIMIT) {
            diagnostics.error(ErrorCode::E_RESOURCE,
                              "HDDL grounding exceeds the finite expansion limit");
            return false;
        }
        return completed;
    }

    template <typename Callback>
    bool enumerateMethodEnvironments(const MethodSchema& method, const Environment& head,
                                     Callback callback, Uir::Diagnostics& diagnostics) {
        if (!bindingsPossible(method.bindings, head)) { return true; }
        const auto found = method_joins_.find(method.name);
        if (found == method_joins_.end() || found->second.empty()) {
            return enumerateEnvironments(method.params, callback, diagnostics, head);
        }
        std::vector<const TaskCall*> joins;
        for (const auto& call : found->second) { joins.push_back(&call); }
        std::stable_sort(joins.begin(), joins.end(), [&](const auto* a, const auto* b) {
            return initial_relations_.at(a->name).size() < initial_relations_.at(b->name).size();
        });
        std::map<std::string, std::string> parameter_types;
        for (const auto& parameter : method.params) { parameter_types.emplace(parameter.name, parameter.type); }
        std::function<bool(std::size_t, const Environment&)> visit;
        visit = [&](std::size_t at, const Environment& environment) {
            if (at == joins.size()) {
                return enumerateEnvironments(method.params, callback, diagnostics, environment);
            }
            const auto& call = *joins[at];
            for (const auto& tuple : initial_relations_.at(call.name)) {
                if (tuple.size() != call.terms.size()) { continue; }
                auto bound = environment;
                bool matches = true;
                for (std::size_t i = 0; i < tuple.size(); ++i) {
                    const auto& term = call.terms[i];
                    if (isVariable(term)) {
                        const auto type = parameter_types.find(term);
                        const auto object = object_types_.find(tuple[i]);
                        if (type == parameter_types.end() || object == object_types_.end()
                            || !isSubtype(object->second, type->second)) {
                            matches = false; break;
                        }
                        const auto entry = bound.emplace(term, tuple[i]);
                        if (entry.first->second != tuple[i]) { matches = false; break; }
                    } else if (term != tuple[i]) { matches = false; break; }
                }
                if (matches && !visit(at + 1, bound)) { return false; }
            }
            return true;
        };
        return visit(0, head);
    }

    std::optional<GroundTask> groundTask(const TaskCall& call,
                                         const Environment& environment,
                                         const std::string& context,
                                         Uir::Diagnostics& diagnostics) {
        const auto schema = tasks_.find(call.name);
        if (schema == tasks_.end()) { return std::nullopt; }
        std::vector<std::string> args;
        for (std::size_t i = 0; i < call.terms.size(); ++i) {
            std::string object = call.terms[i];
            if (isVariable(object)) {
                const auto value = environment.find(object);
                if (value == environment.end()) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      context + " has no binding for '" + object + "'");
                    return std::nullopt;
                }
                object = value->second;
            }
            const auto actual = object_types_.find(object);
            if (actual == object_types_.end()
                || !isSubtype(actual->second, schema->second.params[i].type)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  context + " passes object '" + object
                                      + "' at an incompatible task parameter");
                return std::nullopt;
            }
            args.push_back(std::move(object));
        }
        return GroundTask{sourceCall(call.name, args), schema->second.primitive, call.name, args};
    }

    std::optional<GroundNetwork> groundNetwork(const NetworkSyntax& network,
                                               const Environment& environment,
                                               const std::string& context,
                                               Uir::Diagnostics& diagnostics) {
        GroundNetwork result;
        for (const TaskCall& call : network.tasks) {
            auto task = groundTask(call, environment, context, diagnostics);
            if (!task) { return std::nullopt; }
            result.tasks.push_back(std::move(*task));
        }
        result.edges = network.edges;
        return result;
    }

    bool groundHierarchy(Uir::Diagnostics& diagnostics) {
        // The same sound lower bound used on grounded networks also applies
        // before choosing any initial variables. All source schemas are still
        // checked, including by the classical encoder when no frontier fits.
        if (minimumNetworkLength(initial_network_, depth_) > horizon_) { return true; }
        return enumerateEnvironments(
            initial_params_,
            [&](const Environment& environment) {
                if (!bindingsHold(initial_bindings_, environment)) { return true; }
                auto network = groundNetwork(initial_network_, environment,
                                             "initial task network", diagnostics);
                if (!network) { return false; }
                initial_networks_.push_back(std::move(*network));
                return ++ground_count_ <= EXPANSION_LIMIT;
            }, diagnostics);
    }

    // A parameter-independent lower bound, capped just above the source
    // horizon. Ignoring bindings and preconditions can only lower it. This
    // lets us reject impossible bounded branches before Cartesian grounding.
    std::size_t minimumTaskLength(const std::string& name, unsigned depth) {
        if (prefix_methods_.count(name)) { return 0; }
        if (tasks_.at(name).primitive) { return 1; }
        const auto key = std::make_pair(name, depth);
        const auto cached = minimum_lengths_.find(key);
        if (cached != minimum_lengths_.end()) { return cached->second; }
        std::size_t best = static_cast<std::size_t>(horizon_) + 1;
        if (depth != 0) {
            for (const auto& method : methods_) {
                if (method.head.name == name) {
                    best = std::min(best, minimumNetworkLength(method.network, depth - 1));
                }
            }
        }
        minimum_lengths_.emplace(key, best);
        return best;
    }

    template <typename Network>
    std::size_t minimumNetworkLength(const Network& network, unsigned depth) {
        const auto cap = static_cast<std::size_t>(horizon_) + 1;
        std::size_t length = 0;
        for (const auto& task : network.tasks) {
            length = std::min(cap, length + minimumTaskLength(task.name, depth));
            if (length == cap) { break; }
        }
        return length;
    }

    const std::vector<GroundNetwork>& groundMethods(const GroundTask& task,
                                                   unsigned depth,
                                                   Uir::Diagnostics& diagnostics) {
        const auto key = task.label + "#" + std::to_string(depth);
        const auto cached = ground_methods_.find(key);
        if (cached != ground_methods_.end()) { return cached->second; }
        auto& alternatives = ground_methods_[key];
        for (const MethodSchema& method : methods_) {
            if (method.head.name != task.name) { continue; }
            if (minimumNetworkLength(method.network, depth - 1) > horizon_) { continue; }
            Environment bound;
            bool matches = true;
            for (std::size_t i = 0; i < method.head.terms.size(); ++i) {
                const auto& term = method.head.terms[i];
                if (isVariable(term)) {
                    const auto inserted = bound.emplace(term, task.args[i]);
                    if (!inserted.second && inserted.first->second != task.args[i]) {
                        matches = false;
                    }
                } else if (term != task.args[i]) { matches = false; }
            }
            for (const auto& parameter : method.params) {
                const auto value = bound.find(parameter.name);
                if (value != bound.end()
                    && !isSubtype(object_types_.at(value->second), parameter.type)) {
                    matches = false;
                }
            }
            if (!matches) { continue; }
            // Head arguments are already fixed by the reached task. Only
            // genuine method-local parameters range over objects. Eagerly
            // multiplying every head parameter made high-arity, unreachable
            // methods dominate both time and memory.
            if (!enumerateMethodEnvironments(
                    method, bound,
                    [&](const Environment& environment) {
                        // These are restrictions on substitutions, evaluated
                        // before either the subtasks or method state event.
                        if (!bindingsHold(method.bindings, environment)) { return true; }
                        auto network = groundNetwork(method.network, environment,
                                                     "method '" + method.name + "'",
                                                     diagnostics);
                        if (!network) { return false; }
                        alternatives.push_back(std::move(*network));
                        return ++ground_count_ <= EXPANSION_LIMIT;
                    }, diagnostics)) {
                return alternatives;
            }
        }
        return alternatives;
    }

    const std::vector<PartialPlan>& expandTask(const GroundTask& task, unsigned depth,
                                        Uir::Diagnostics& diagnostics) {
        const std::string key = task.label + "#" + std::to_string(depth);
        const auto cached = memo_.find(key);
        if (cached != memo_.end()) { return cached->second; }
        std::vector<PartialPlan> result;
        if (task.primitive) {
            result.push_back(PartialPlan{{task.label}, {}});
        } else if (depth != 0) {
            const auto& alternatives = groundMethods(task, depth, diagnostics);
            if (diagnostics.hasErrors()) { return empty_plans_; }
            {
                for (const GroundNetwork& network : alternatives) {
                    auto expanded = expandNetwork(network, depth - 1, diagnostics);
                    result.insert(result.end(), std::make_move_iterator(expanded.begin()),
                                  std::make_move_iterator(expanded.end()));
                    expansion_count_ += expanded.size();
                    if (expansion_count_ > EXPANSION_LIMIT) {
                        diagnostics.error(ErrorCode::E_RESOURCE,
                                          "HDDL method expansion exceeds the configured "
                                          "resource guard");
                        return empty_plans_;
                    }
                }
            }
        }
        // std::map preserves references while recursive expansion inserts
        // other entries. The cache is cleared only after all root frontiers
        // have been materialized, so callers can borrow these alternatives.
        return memo_.emplace(key, std::move(result)).first->second;
    }

    std::vector<PartialPlan> expandNetwork(const GroundNetwork& network,
                                           unsigned depth,
                                           Uir::Diagnostics& diagnostics) {
        if (network.tasks.empty()) { return {PartialPlan{}}; }
        if (minimumNetworkLength(network, depth) > horizon_) { return {}; }
        std::vector<const std::vector<PartialPlan>*> alternatives;
        for (const GroundTask& task : network.tasks) {
            const auto& expanded = expandTask(task, depth, diagnostics);
            if (diagnostics.hasErrors() || expanded.empty()) { return {}; }
            alternatives.push_back(&expanded);
        }

        const std::size_t n = network.tasks.size();
        std::vector<std::vector<bool>> reach(n, std::vector<bool>(n, false));
        for (const auto& [from, to] : network.edges) { reach[from][to] = true; }
        for (std::size_t k = 0; k < n; ++k) {
            for (std::size_t i = 0; i < n; ++i) {
                for (std::size_t j = 0; j < n; ++j) {
                    reach[i][j] = reach[i][j] || (reach[i][k] && reach[k][j]);
                }
            }
        }

        // Count only source primitives: compiled method-state events consume
        // execution slots but never the user's source PLAN_HORIZON. A suffix
        // lower bound rejects only products that no completion can admit.
        const auto cap = static_cast<std::size_t>(horizon_) + 1;
        std::vector<std::vector<std::size_t>> lengths(n);
        std::vector<std::size_t> suffix_minimum(n + 1, 0);
        for (std::size_t i = n; i-- > 0;) {
            std::size_t minimum = cap;
            lengths[i].reserve(alternatives[i]->size());
            for (const auto& plan : *alternatives[i]) {
                const auto length = sourceLength(plan.primitives);
                lengths[i].push_back(length);
                minimum = std::min(minimum, length);
            }
            suffix_minimum[i] = std::min(cap, minimum + suffix_minimum[i + 1]);
        }
        std::vector<PartialPlan> result;
        std::vector<const PartialPlan*> selected(n, nullptr);
        std::function<void(std::size_t, std::size_t)> choose =
            [&](std::size_t at, std::size_t prefix_length) {
            if (diagnostics.hasErrors() || suffix_minimum[at] > horizon_ - prefix_length) {
                return;
            }
            if (at != n) {
                for (std::size_t i = 0; i < alternatives[at]->size(); ++i) {
                    const auto length = lengths[at][i];
                    if (length > horizon_ - prefix_length) { continue; }
                    selected[at] = &(*alternatives[at])[i];
                    choose(at + 1, prefix_length + length);
                }
                return;
            }

            PartialPlan combined;
            std::vector<std::size_t> offsets(n, 0);
            std::vector<std::vector<std::size_t>> minima(n), maxima(n);
            for (std::size_t i = 0; i < n; ++i) {
                offsets[i] = combined.primitives.size();
                const PartialPlan& child = *selected[i];
                combined.primitives.insert(combined.primitives.end(),
                                           child.primitives.begin(),
                                           child.primitives.end());
                std::vector<bool> has_in(child.primitives.size(), false);
                std::vector<bool> has_out(child.primitives.size(), false);
                for (const auto& [from, to] : child.edges) {
                    combined.edges.emplace(offsets[i] + from, offsets[i] + to);
                    has_out[from] = true;
                    has_in[to] = true;
                }
                for (std::size_t p = 0; p < child.primitives.size(); ++p) {
                    if (!has_in[p]) { minima[i].push_back(offsets[i] + p); }
                    if (!has_out[p]) { maxima[i].push_back(offsets[i] + p); }
                }
            }
            if (sourceLength(combined.primitives) > horizon_) { return; }
            for (std::size_t i = 0; i < n; ++i) {
                for (std::size_t j = 0; j < n; ++j) {
                    if (!reach[i][j]) { continue; }
                    for (std::size_t from : maxima[i]) {
                        for (std::size_t to : minima[j]) {
                            combined.edges.emplace(from, to);
                        }
                    }
                }
            }
            result.push_back(std::move(combined));
            if (++expansion_count_ > EXPANSION_LIMIT) {
                diagnostics.error(ErrorCode::E_RESOURCE,
                                  "HDDL partial-plan product exceeds the resource guard");
            }
        };
        choose(0, 0);
        return result;
    }

    H::ExprPtr hierarchyFormula(const std::vector<PartialPlan>& frontiers,
                                PddlInternal::ClassicalEncoding& encoding,
                                Uir::Diagnostics& diagnostics) const {
        const auto& projection = encoding.projection;
        if (projection.choices.size() != execution_horizon_) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "HDDL/PDDL action-coordinate count disagrees with horizon");
            return nullptr;
        }
        std::vector<std::map<std::string, H::ExprPtr>> choices(execution_horizon_);
        for (std::size_t step = 0; step < execution_horizon_; ++step) {
            for (const auto& choice : projection.choices[step].alternatives) {
                choices[step].emplace(choice.label,
                    H::mkIdent(choice.target_name, H::Sort::boolean()));
            }
        }
        const auto actionAt = [&](const std::string& label, std::size_t step) -> H::ExprPtr {
            const auto found = choices[step].find(label);
            if (found != choices[step].end()) { return found->second; }
            diagnostics.error(ErrorCode::E_TYPE,
                "hierarchy produces primitive task '" + label
                + "' for which the classical domain has no grounded action");
            return nullptr;
        };
        std::set<std::string> names;
        for (const auto& declaration : encoding.model->decls) { names.insert(declaration.name); }
        // The disjunction selects one frontier. Its existential scheduling
        // witnesses can be shared with every other alternative: any shorter
        // permutation extends to the common finite position domain.
        std::vector<H::ExprPtr> positions;
        std::map<std::tuple<std::size_t, std::size_t, std::string>, H::ExprPtr> placements;
        std::map<std::pair<std::size_t, std::size_t>, H::ExprPtr> precedences;
        std::vector<H::ExprPtr> alternatives;
        // Keep long single paths flat to avoid reintroducing recursive HIR
        // depth proportional to a large source horizon.
        const bool factor = frontiers.size() > 1 && execution_horizon_ <= 128
            && std::all_of(frontiers.begin(), frontiers.end(), [&](const auto& plan) {
                return plan.edges.size() <= 128 - execution_horizon_;
            });
        FrontierFormula factored;
        for (std::size_t at = 0; at < frontiers.size(); ++at) {
            const auto& plan = frontiers[at];
            const std::size_t n = plan.primitives.size();
            std::vector<H::ExprPtr> selected;

            // A uniquely ordered frontier needs no scheduling witnesses.
            std::vector<std::vector<std::size_t>> successors(n);
            std::vector<unsigned> indegree(n, 0);
            for (const auto& [from, to] : plan.edges) {
                successors[from].push_back(to);
                ++indegree[to];
            }
            std::set<std::size_t> ready;
            for (std::size_t i = 0; i < n; ++i) {
                if (indegree[i] == 0) { ready.insert(i); }
            }
            std::vector<std::size_t> order;
            while (ready.size() == 1) {
                const auto i = *ready.begin();
                ready.erase(i);
                order.push_back(i);
                for (auto next : successors[i]) {
                    if (--indegree[next] == 0) { ready.insert(next); }
                }
            }
            if (order.size() == n) {
                for (std::size_t step = 0; step < n; ++step) {
                    auto action = actionAt(plan.primitives[order[step]], step);
                    if (!action) { return nullptr; }
                    selected.push_back(std::move(action));
                }
            } else {
                // Inject n distinct occurrence positions into [0,n). This is
                // a bijection, even when several occurrences have one label.
                // Edge inequalities select exactly the linear extensions of
                // the partial order without enumerating up to n! sequences.
                while (positions.size() < n) {
                    H::VarDecl position;
                    position.name = "__hddl_position@shared_" + std::to_string(positions.size());
                    while (!names.insert(position.name).second) { position.name += "_"; }
                    position.sort = H::Sort::integer();
                    position.auxiliary = true;
                    position.lower_bound = H::mkInt(0);
                    position.upper_bound = H::mkInt(execution_horizon_ - 1);
                    positions.push_back(H::mkIdent(position.name, position.sort));
                    encoding.model->decls.push_back(std::move(position));
                }
                for (std::size_t i = 0; i < n; ++i) {
                    const auto key = std::make_tuple(n, i, plan.primitives[i]);
                    auto placement = placements.find(key);
                    if (placement == placements.end()) {
                        std::vector<H::ExprPtr> slots;
                        for (std::size_t step = 0; step < n; ++step) {
                            auto action = actionAt(plan.primitives[i], step);
                            if (!action) { return nullptr; }
                            slots.push_back(H::mkOp(H::Op::AND, {
                                H::mkOp(H::Op::EQ, {positions[i], H::mkInt(step)}), action}));
                        }
                        placement = placements.emplace(key, disjunction(std::move(slots))).first;
                    }
                    selected.push_back(placement->second);
                }
                for (const auto& [from, to] : plan.edges) {
                    auto precedence = precedences.find({from, to});
                    if (precedence == precedences.end()) {
                        precedence = precedences.emplace(std::make_pair(from, to),
                            H::mkOp(H::Op::LT, {positions[from], positions[to]})).first;
                    }
                    selected.push_back(precedence->second);
                }
            }
            for (std::size_t step = n; step < execution_horizon_; ++step) {
                auto noop = actionAt(projection.choices[step].omit_label, step);
                if (!noop) { return nullptr; }
                selected.push_back(std::move(noop));
            }
            if (factor) { factored.add(selected); }
            else { alternatives.push_back(conjunction(std::move(selected))); }
        }
        auto formula = factor ? factored.formula() : disjunction(std::move(alternatives));
        if (positions.size() > 1) {
            formula = conjunction({H::mkOp(H::Op::DISTINCT, std::move(positions)), formula});
        }
        return formula;
    }

    std::string domain_text_;
    std::string problem_text_;
    std::string file_;
    unsigned horizon_ = 0;
    unsigned execution_horizon_ = 0;
    Sexp classical_domain_;
    std::map<std::string, std::string> prefix_methods_;
    bool relaxed_method_state_ = false;
    bool lenient_requirements_ = false;
    bool ipc_compatibility_ = false;
    std::vector<std::string> ipc_normalizations_;
    unsigned depth_ = 0;
    Sexp domain_root_;
    Sexp problem_root_;
    std::string sanitized_domain_;
    std::string sanitized_problem_;

    PlanningInternal::TypeHierarchy types_;
    std::vector<Typed> constants_;
    std::vector<Typed> objects_;
    std::map<std::string, std::string> object_types_;
    std::map<std::string, TaskSchema> tasks_;
    std::vector<MethodSchema> methods_;
    std::set<std::string> method_names_;
    std::vector<Typed> initial_params_;
    std::vector<BindingConstraint> initial_bindings_;
    NetworkSyntax initial_network_;
    bool saw_hierarchy_ = false;
    /** Requirement licensing method state conditions and effects. */
    bool saw_method_pre_eff_ = false;
    bool saw_method_preconditions_ = false;
    bool saw_initial_htn_ = false;

    std::map<std::string, std::vector<GroundNetwork>> ground_methods_;
    std::map<std::string, std::vector<TaskCall>> method_joins_;
    std::map<std::string, std::set<std::vector<std::string>>> initial_relations_;
    std::map<std::pair<std::string, unsigned>, std::size_t> minimum_lengths_;
    std::vector<GroundNetwork> initial_networks_;
    std::map<std::string, std::vector<PartialPlan>> memo_;
    const std::vector<PartialPlan> empty_plans_;
    std::size_t ground_count_ = 0;
    std::size_t expansion_count_ = 0;
};

bool parseBound(const Uir::ParamMap& options, const std::string& name,
                unsigned& result, Uir::Diagnostics& diagnostics) {
    const auto found = options.find(name);
    if (found == options.end()) {
        diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                          "no " + name + ": pass `" + name
                              + "=<k>`; HDDL completeness is relative to both bounds");
        return false;
    }
    const std::string& text = found->second;
    if (text.empty()
        || !std::all_of(text.begin(), text.end(),
                        [](unsigned char c) { return std::isdigit(c) != 0; })) {
        diagnostics.error(ErrorCode::E_PARSE,
                          name + " must be a non-negative decimal integer");
        return false;
    }
    unsigned long long parsed = 0;
    try {
        parsed = std::stoull(text);
    } catch (const std::exception&) {
        diagnostics.error(ErrorCode::E_PARSE,
                          name + " is outside the supported integer range");
        return false;
    }
    if (parsed > UINT_MAX) {
        diagnostics.error(ErrorCode::E_PARSE,
                          name + " exceeds the frontend's supported range");
        return false;
    }
    result = static_cast<unsigned>(parsed);
    return true;
}

class HddlLanguage : public Language {
public:
    HddlLanguage() {
        coverage_.total = 3;
        coverage_.supported = 2;
        coverage_.missing = {
            "binding constraints beyond object equality/disequality",
        };
    }

    std::string id() const override { return "hddl"; }
    std::string displayName() const override {
        return "HDDL (bounded finite hierarchical planning)";
    }
    std::string version() const override { return "HDDL 1.0 finite Boolean subset"; }
    std::vector<std::string> extensions() const override { return {".hddl", ".pddl"}; }
    const OpCoverage& coverage() const override { return coverage_; }
    bool acceptsDataFiles() const override { return true; }

    double sniff(std::string_view head) const override {
        return head.find(":method") != std::string_view::npos
                   || head.find("(:task ") != std::string_view::npos
                   || head.find(":htn") != std::string_view::npos
               ? 0.95 : 0.0;
    }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& options) override {
        ParseOutcome result;
        const auto slurp = [&](const std::string& path, std::string& into) {
            std::error_code error;
            if (std::filesystem::is_directory(path, error)) {
                result.diagnostics.error(ErrorCode::E_IO, "'" + path + "' is a directory");
                return false;
            }
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
        if (domain.empty() && !slurp(unit.main_path, domain)) { return result; }
        if (unit.data_paths.size() != 1) {
            result.diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "HDDL translation takes exactly one companion problem file, not "
                    + std::to_string(unit.data_paths.size()));
            return result;
        }
        std::string problem;
        if (!slurp(unit.data_paths.front(), problem)) { return result; }

        unsigned horizon = 0;
        unsigned depth = 0;
        if (!parseBound(options.options, "plan_horizon", horizon, result.diagnostics)
            || !parseBound(options.options, "decomposition_depth", depth,
                           result.diagnostics)) {
            return result;
        }

        const std::string name = unit.main_path.empty() ? unit.display_name
                                                         : unit.main_path;
        bool ipc_compatibility = false;
        const auto ipc_option = options.options.find("ipc_compatibility");
        if (ipc_option != options.options.end()) {
            const auto& value = ipc_option->second;
            if (value != "true" && value != "false" && value != "1" && value != "0") {
                result.diagnostics.error(ErrorCode::E_PARSE,
                                         "ipc_compatibility must be true, false, 1, or 0");
                return result;
            }
            ipc_compatibility = value == "true" || value == "1";
        }
        try {
            HddlParser parser(domain, problem, name, horizon, depth);
            // Four of the eight files in this language's own upstream corpus
            // -- IPC test instances -- use constructs their `:requirements` do
            // not declare, so the strict default reports a figure about the
            // corpus's conformance rather than about this frontend.
            parser.setLenientRequirements(ipc_compatibility
                                         || PddlInternal::lenientRequirements(options));
            parser.setIpcCompatibility(ipc_compatibility);
            PddlInternal::ClassicalEncoding encoding =
                parser.parse(result.diagnostics, result.report);
            result.model = std::move(encoding.model);
            if (result.model) {
                result.semantics.add(S::hddlToRelationalContract(
                    *result.model, result.report.fidelity(),
                    std::move(encoding.projection),
                    std::move(encoding.source_signature),
                    std::move(encoding.symbol_map),
                    std::move(encoding.target_axioms)));
            }
        } catch (const std::exception& error) {
            result.model.reset();
            result.diagnostics.error(ErrorCode::E_INTERNAL,
                                     std::string("hddl frontend: ") + error.what());
        }
        return result;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkHddlLanguage() { return std::make_shared<HddlLanguage>(); }

} // namespace SOMTParser::Lang
