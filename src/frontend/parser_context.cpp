/* -*- C++ -*-
 * ParserContext implementations
 */

#include "somtparser/frontend/parser_context.h"
#include <stdexcept>

namespace SOMTParser {

std::vector<std::shared_ptr<DAGNode>> ParserContext::getAssertions() const {
    return assertions;
}

std::unordered_map<std::string, std::unordered_set<size_t>> ParserContext::getGroupedAssertions() const {
    return assertion_groups;
}

std::unordered_map<std::string, std::shared_ptr<DAGNode>> ParserContext::getNamedAssertions() const {
    return named_assertions;
}

std::vector<std::vector<std::shared_ptr<DAGNode>>> ParserContext::getAssumptions() const {
    return assumptions;
}

std::vector<std::shared_ptr<DAGNode>> ParserContext::getSoftAssertions() const {
    return soft_assertions;
}

std::vector<std::shared_ptr<DAGNode>> ParserContext::getSoftWeights() const {
    return soft_weights;
}

std::unordered_map<std::string, std::unordered_set<size_t>> ParserContext::getGroupedSoftAssertions() const {
    return soft_assertion_groups;
}

std::vector<std::shared_ptr<Objective>> ParserContext::getObjectives() const {
    auto om = getObjectiveManager();
    return om ? om->getObjectives() : std::vector<std::shared_ptr<Objective>>{};
}

std::vector<std::shared_ptr<DAGNode>> ParserContext::getSplitLemmas() const {
    return split_lemmas;
}

// --- Incremental push/pop scope stack ---

void ParserContext::pushScope(size_t n) {
    for (size_t i = 0; i < n; ++i) {
        ScopeFrame frame;
        frame.assertions_size = assertions.size();
        frame.assumptions_size = assumptions.size();
        frame.soft_assertions_size = soft_assertions.size();
        frame.soft_weights_size = soft_weights.size();
        frame.objectives_size = getObjectiveManager() ? getObjectiveManager()->getObjectives().size() : 0;
        frame.split_lemmas_size = split_lemmas.size();
        scope_stack_.push_back(std::move(frame));
    }
}

void ParserContext::popScope(size_t n) {
    if (n > scope_stack_.size()) {
        throw std::invalid_argument("assertion stack pop underflow");
    }
    for (size_t i = 0; i < n; ++i) {
        const ScopeFrame& frame = scope_stack_.back();

        // Truncate vectors to recorded sizes
        assertions.resize(frame.assertions_size);
        assumptions.resize(frame.assumptions_size);
        soft_assertions.resize(frame.soft_assertions_size);
        soft_weights.resize(frame.soft_weights_size);
        soft_objective_positions.resize(frame.soft_assertions_size);
        split_lemmas.resize(frame.split_lemmas_size);

        // Remove added symbols from SymbolManager
        if (auto sm = getSymbolManager()) {
            for (const auto& name : frame.added_vars) sm->removeVar(name);
            for (const auto& name : frame.added_funs) sm->removeFun(name);
            for (const auto& name : frame.added_sorts) sm->removeSort(name);
        }

        // Remove added named assertions, then put back whatever they displaced.
        // Reverse order so that when a name was displaced repeatedly the
        // outermost binding -- recorded first -- is the one that survives.
        for (const auto& key : frame.added_named_assertion_keys) {
            auto it = named_assertions.find(key);
            if (it != named_assertions.end()) {
                assertion_names_.erase(it->second);
                named_assertions.erase(it);
            }
        }
        for (auto it = frame.replaced_named_assertions.rbegin();
             it != frame.replaced_named_assertions.rend(); ++it) {
            named_assertions[it->first] = it->second;
            assertion_names_[it->second] = it->first;
        }

        // Remove added assertion group indices
        for (const auto& key : frame.added_assertion_group_keys) {
            auto it = assertion_groups.find(key);
            if (it != assertion_groups.end()) {
                // Remove indices >= frame.assertions_size from this group
                std::unordered_set<size_t> new_set;
                for (size_t idx : it->second) {
                    if (idx < frame.assertions_size) new_set.insert(idx);
                }
                if (new_set.empty()) assertion_groups.erase(it);
                else it->second = std::move(new_set);
            }
        }

        // Remove added soft assertion group indices
        for (const auto& key : frame.added_soft_assertion_group_keys) {
            auto it = soft_assertion_groups.find(key);
            if (it != soft_assertion_groups.end()) {
                std::unordered_set<size_t> new_set;
                for (size_t idx : it->second) {
                    if (idx < frame.soft_assertions_size) new_set.insert(idx);
                }
                if (new_set.empty()) soft_assertion_groups.erase(it);
                else it->second = std::move(new_set);
            }
        }

        // Truncate objectives
        if (auto om = getObjectiveManager()) {
            om->popToSize(frame.objectives_size);
        }

        scope_stack_.pop_back();
    }
}

void ParserContext::resetAssertions() {
    assertions.clear();
    assumptions.clear();
    soft_assertions.clear();
    soft_weights.clear();
    soft_objective_positions.clear();
    assertion_groups.clear();
    soft_assertion_groups.clear();
    named_assertions.clear();
    assertion_names_.clear();
    split_lemmas.clear();
    scope_stack_.clear();
    if (auto om = getObjectiveManager()) om->clear();

    // reset-assertions removes every assertion level, including declarations
    // at the base level. Global declarations survive, as do options and logic.
    auto options = getOptions();
    if (!options || !options->getGlobalDeclarations()) {
        if (auto sm = getSymbolManager()) sm->clear();
    }
}

void ParserContext::resetAll() {
    resetAssertions();
    heap_location_sort.reset();
    heap_data_sort.reset();
    heap_declaration_open = true;
    scope_stack_.clear();
    if (auto symbols = getSymbolManager()) symbols->clear();
    else setSymbolManager(std::make_shared<SymbolManager>());
    if (auto objectives = getObjectiveManager()) objectives->clear();
    else setObjectiveManager(std::make_shared<ObjectiveManager>());
    GlobalOptions defaults;
    if (auto old = getOptions()) {
        // Script options reset to defaults; policies set by the embedding API
        // survive. Keep the options object visible to existing API holders.
        if (!old->options.count("keep_let")) defaults.parsing_preserve_let = old->parsing_preserve_let;
        if (!old->options.count("expand_functions")) defaults.expand_functions = old->expand_functions;
        if (!old->options.count("expand_recursive_functions"))
            defaults.expand_recursive_functions = old->expand_recursive_functions;
        if (!old->options.count("strict_smtlib_fp")) defaults.strict_smtlib_fp = old->strict_smtlib_fp;
        *old = std::move(defaults);
    } else setOptions(std::make_shared<GlobalOptions>(std::move(defaults)));
}

// --- Named assertions ---

NameAssertionOutcome ParserContext::nameAssertion(const std::string& name,
                                                 const std::shared_ptr<DAGNode>& node) {
    NameAssertionOutcome out;
    if (!node) return out;

    // Already bound exactly this way: nothing changes, and in particular this
    // scope must not claim it added the binding -- popping would then delete a
    // name that an enclosing scope owns.
    auto existing = named_assertions.find(name);
    if (existing != named_assertions.end() && existing->second == node) return out;

    ScopeFrame* frame = scope_stack_.empty() ? nullptr : &scope_stack_.back();

    // Naming an assertion that already has a name: the old name goes away, so
    // the bijection holds and a dump has exactly one name to print for it.
    auto old = assertion_names_.find(node);
    if (old != assertion_names_.end() && old->second != name) {
        out.assertion_was_named = true;
        out.previous_name = old->second;
        if (frame) frame->replaced_named_assertions.emplace_back(old->second, node);
        named_assertions.erase(old->second);
        assertion_names_.erase(old);
    }

    // Reusing a name for a different assertion: the earlier one loses it.
    auto taken = named_assertions.find(name);
    if (taken != named_assertions.end() && taken->second != node) {
        out.name_was_reused = true;
        if (frame) frame->replaced_named_assertions.emplace_back(name, taken->second);
        assertion_names_.erase(taken->second);
    }

    named_assertions[name] = node;
    assertion_names_[node] = name;
    registerNamedAssertionInScope(name);
    return out;
}

const std::string* ParserContext::getAssertionName(const std::shared_ptr<DAGNode>& node) const {
    auto it = assertion_names_.find(node);
    return it == assertion_names_.end() ? nullptr : &it->second;
}

// --- Scope recording helpers ---

void ParserContext::registerVarInScope(const std::string& name) {
    if (getOptions() && getOptions()->getGlobalDeclarations()) return;
    if (!scope_stack_.empty()) scope_stack_.back().added_vars.push_back(name);
}

void ParserContext::registerFunInScope(const std::string& name) {
    if (getOptions() && getOptions()->getGlobalDeclarations()) return;
    if (!scope_stack_.empty()) scope_stack_.back().added_funs.push_back(name);
}

void ParserContext::registerSortInScope(const std::string& name) {
    if (getOptions() && getOptions()->getGlobalDeclarations()) return;
    if (!scope_stack_.empty()) scope_stack_.back().added_sorts.push_back(name);
}

void ParserContext::registerNamedAssertionInScope(const std::string& name) {
    if (!scope_stack_.empty()) scope_stack_.back().added_named_assertion_keys.push_back(name);
}

void ParserContext::registerAssertionGroupInScope(const std::string& name) {
    if (!scope_stack_.empty()) scope_stack_.back().added_assertion_group_keys.push_back(name);
}

void ParserContext::registerSoftAssertionGroupInScope(const std::string& name) {
    if (!scope_stack_.empty()) scope_stack_.back().added_soft_assertion_group_keys.push_back(name);
}

} // namespace SOMTParser
