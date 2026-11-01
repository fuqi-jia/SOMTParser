/* -*- Header -*-
 *
 * ParserContext: frontend context with SymbolManager, ObjectiveManager and parser state.
 *
 * Extends Context with symbol_manager_, objective_manager_, and assertions/assumptions.
 * Used by Parser only; passes (Rewriter, etc.) depend only on Context.
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#ifndef PARSER_CONTEXT_HEADER
#define PARSER_CONTEXT_HEADER

#include "somtparser/context/context.h"
#include "somtparser/ir/dag.h"
#include "somtparser/frontend/objective.h"
#include "somtparser/frontend/symbol_manager.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser {

/**
 * Snapshot of parser state for a single push/pop scope level.
 */
struct ScopeFrame {
    size_t assertions_size = 0;
    size_t assumptions_size = 0;
    size_t soft_assertions_size = 0;
    size_t soft_weights_size = 0;
    size_t objectives_size = 0;
    size_t split_lemmas_size = 0;

    std::vector<std::string> added_vars;
    std::vector<std::string> added_funs;
    std::vector<std::string> added_sorts;
    std::vector<std::string> added_named_assertion_keys;
    // Bindings this scope displaced. Naming an assertion drops any earlier name
    // for the same node, and may steal a name from another node; popping has to
    // put the outer binding back or it would be lost with no way to recover it.
    std::vector<std::pair<std::string, std::shared_ptr<DAGNode>>> replaced_named_assertions;
    std::vector<std::string> added_assertion_group_keys;
    std::vector<std::string> added_soft_assertion_group_keys;
};

/**
 * What naming an assertion displaced. Both flags can be set at once, e.g. when
 * the assertion already had a name and the new name belonged to another one.
 */
struct NameAssertionOutcome {
    /** The assertion already carried a name; previous_name has been dropped. */
    bool assertion_was_named = false;
    std::string previous_name;
    /** The name already referred to a different assertion, which loses it. */
    bool name_was_reused = false;
};

/**
 * Context implementation that holds parser data (symbols, objectives, assertions, etc.).
 * Inherits NodeManager, SortManager, Options from Context; adds SymbolManager, ObjectiveManager.
 */
class ParserContext : public Context {
protected:
    std::shared_ptr<SymbolManager>   symbol_manager_;
    std::shared_ptr<ObjectiveManager> objective_manager_;

public:
    void setSymbolManager(std::shared_ptr<SymbolManager> sm) { symbol_manager_ = std::move(sm); }
    void setObjectiveManager(std::shared_ptr<ObjectiveManager> om) { objective_manager_ = std::move(om); }

    std::shared_ptr<SymbolManager> getSymbolManager() { return symbol_manager_; }
    std::shared_ptr<SymbolManager> getSymbolManager() const { return symbol_manager_; }
    std::shared_ptr<ObjectiveManager> getObjectiveManager() { return objective_manager_; }
    std::shared_ptr<ObjectiveManager> getObjectiveManager() const { return objective_manager_; }

public:
    // One heap signature per script, retained by reset-assertions and scopes.
    // Only a full reset permits a new signature.
    std::shared_ptr<Sort> heap_location_sort;
    std::shared_ptr<Sort> heap_data_sort;
    bool heap_declaration_open = true;
    std::vector<std::shared_ptr<DAGNode>> assertions;
    std::unordered_map<std::string, std::unordered_set<size_t>> assertion_groups;
    // Kept a bijection by nameAssertion(): every name refers to one assertion
    // and every assertion carries at most one name. Nodes are hash-consed, so
    // two textually distinct `:named` annotations on equal terms land on the
    // same node; without the bijection dumpSMT2 could not tell which name to
    // print for it. Register through nameAssertion(), not by writing here.
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> named_assertions;
    std::vector<std::vector<std::shared_ptr<DAGNode>>> assumptions;
    std::vector<std::shared_ptr<DAGNode>> soft_assertions;
    std::vector<std::shared_ptr<DAGNode>> soft_weights;
    // Number of explicit objectives preceding each soft assertion in the input.
    std::vector<size_t> soft_objective_positions;
    std::unordered_map<std::string, std::unordered_set<size_t>> soft_assertion_groups;
    std::vector<std::shared_ptr<DAGNode>> split_lemmas;

    std::vector<std::shared_ptr<DAGNode>> getAssertions() const;
    std::unordered_map<std::string, std::unordered_set<size_t>> getGroupedAssertions() const;
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> getNamedAssertions() const;
    std::vector<std::vector<std::shared_ptr<DAGNode>>> getAssumptions() const;
    std::vector<std::shared_ptr<DAGNode>> getSoftAssertions() const;
    std::vector<std::shared_ptr<DAGNode>> getSoftWeights() const;
    std::unordered_map<std::string, std::unordered_set<size_t>> getGroupedSoftAssertions() const;
    std::vector<std::shared_ptr<Objective>> getObjectives() const;
    std::vector<std::shared_ptr<DAGNode>> getSplitLemmas() const;

    // --- Incremental push/pop scope stack ---
    std::vector<ScopeFrame> scope_stack_;

    void pushScope(size_t n = 1);
    void popScope(size_t n = 1);
    void resetAssertions();
    void resetAll();

    // --- Named assertions (:named, for unsat cores and for dumpSMT2) ---
    /**
     * Bind `name` to `node`, dropping whatever the bijection forces out, and
     * record the change in the current scope. The caller reports the returned
     * displacements as warnings; this class does no I/O.
     */
    NameAssertionOutcome nameAssertion(const std::string& name, const std::shared_ptr<DAGNode>& node);
    /** The name bound to `node`, or nullptr. Valid until named_assertions changes. */
    const std::string* getAssertionName(const std::shared_ptr<DAGNode>& node) const;

    // Declaration helpers do not record global declarations for removal by pop.
    void registerVarInScope(const std::string& name);
    void registerFunInScope(const std::string& name);
    void registerSortInScope(const std::string& name);
    void registerNamedAssertionInScope(const std::string& name);
    void registerAssertionGroupInScope(const std::string& name);
    void registerSoftAssertionGroupInScope(const std::string& name);

private:
    // Inverse of named_assertions. Keeps "does this assertion already have a
    // name?" O(1) on the parse path and lets dumpSMT2 look a name up per
    // assertion. The shared_ptr key keeps the node alive alongside the forward map.
    std::unordered_map<std::shared_ptr<DAGNode>, std::string> assertion_names_;
};

} // namespace SOMTParser

#endif
