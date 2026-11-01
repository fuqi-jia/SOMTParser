/* -*- Source -*-
 * SymbolManager implementation
 */

#include "somtparser/frontend/symbol_manager.h"
#include "somtparser/core/asserting.h"
#include <algorithm>

namespace SOMTParser {

SymbolManager::SymbolManager() = default;

void SymbolManager::clear() {
    let_key_map_.clear();
    let_scope_backup_.clear();
    let_scope_checkpoints_.clear();
    fun_key_map_.clear();
    recursive_definitions_.clear();
    fun_var_map_.clear();
    sort_key_map_.clear();
    quant_var_map_.clear();
    var_names_.clear();
    temp_var_counter_ = 0;
    temp_var_names_.clear();
    placeholder_var_names_.clear();
    function_names_.clear();
    function_names_seen_.clear();
    rec_fun_groups_.clear();
    rec_fun_group_of_.clear();
    static_functions_.clear();
    sort_order_.clear();
    var_order_.clear();
    temp_var_order_.clear();
}

void SymbolManager::reserve(size_t capacity) {
    let_key_map_.reserve(capacity);
    let_scope_backup_.reserve(capacity);
    let_scope_checkpoints_.reserve(capacity);
    fun_key_map_.reserve(capacity);
    fun_var_map_.reserve(capacity);
    sort_key_map_.reserve(capacity);
    quant_var_map_.reserve(capacity);
    var_names_.reserve(capacity);
    temp_var_names_.reserve(capacity);
    placeholder_var_names_.reserve(capacity);
    function_names_.reserve(capacity);
    static_functions_.reserve(capacity);
}

namespace {

/**
 * A lookup that treats `foo` and `|foo|` as the same key.
 *
 * SMT-LIB 2.6 §3.1: enclosing a simple symbol in vertical bars **does not
 * produce a new symbol** -- `abc` and `|abc|` are the same symbol, following the
 * Common Lisp convention. The bars widen which characters a symbol may contain;
 * they are not part of its identity.
 *
 * Declaring a predicate quoted and applying it unquoted is ordinary --
 *
 *     (declare-fun |inv| ( Int Int ) Bool)
 *     ...
 *     (inv B A)
 *
 * -- and it failed with `Unknown or unexpected symbol "inv"`.
 *
 * The equivalence was already implemented for var_names_ and for nothing else,
 * which is why a quoted VARIABLE worked and a quoted FUNCTION did not: a
 * zero-argument declare-fun goes through mkVar into var_names_, one with
 * arguments through mkFuncDec into fun_key_map_. One helper, used by every map,
 * is what keeps the two from drifting apart again.
 */
template <typename Map>
typename Map::mapped_type findEitherSpelling(const Map& m, const std::string& name) {
    auto it = m.find(name);
    if (it != m.end()) { return it->second; }
    if (name.size() > 2 && name.front() == '|' && name.back() == '|') {
        it = m.find(name.substr(1, name.size() - 2));
    } else {
        it = m.find('|' + name + '|');
    }
    return it != m.end() ? it->second : nullptr;
}

std::string bindingName(const std::string& name) {
    return name.size() >= 2 && name.front() == '|' && name.back() == '|'
        ? name.substr(1, name.size() - 2) : name;
}

}  // namespace

std::shared_ptr<DAGNode> SymbolManager::resolveSymbol(const std::string& name, const ResolveScope& scope) const {
    if (auto n = findEitherSpelling(placeholder_var_names_, name)) { return n; }
    if (auto n = findEitherSpelling(let_key_map_, name)) {
        // Quantifiers/patterns also push this stack. Their lexical scope can
        // be active without the parser being in a let expression.
        if (scope.check_let || n->isQuantVar()) { return n; }
    }
    if (scope.in_quantifier_scope) {
        if (auto n = getQuantVar(name)) return n;
    }
    if (auto n = findEitherSpelling(fun_var_map_, name)) return n;
    if (auto n = findEitherSpelling(fun_key_map_, name)) return n;
    if (auto n = findEitherSpelling(var_names_, name)) return n;
    return nullptr;
}

std::shared_ptr<DAGNode> SymbolManager::resolveTerm(const std::string& name, const ResolveScope& scope) const {
    if (auto n = findEitherSpelling(placeholder_var_names_, name)) { return n; }
    if (auto n = findEitherSpelling(let_key_map_, name)) {
        if (scope.check_let || n->isQuantVar()) { return n; }
    }
    // Function parameters (fun_var) are term bindings inside function bodies
    if (scope.in_quantifier_scope) {
        if (auto n = getQuantVar(name)) return n;
    }
    if (auto n = findEitherSpelling(fun_var_map_, name)) return n;
    if (auto n = findEitherSpelling(var_names_, name)) return n;
    return nullptr;
}

std::shared_ptr<DAGNode> SymbolManager::resolveFun(const std::string& name) const {
    // This is the path an APPLICATION takes -- `(inv B A)` reaches here, not
    // resolveSymbol -- and it is where a quoted declaration failed.
    if (auto n = findEitherSpelling(fun_key_map_, name)) { return n; }
    if (auto n = findEitherSpelling(fun_var_map_, name)) { return n; }
    return nullptr;
}

std::shared_ptr<Sort> SymbolManager::resolveSort(const std::string& name) const {
    // Sorts too: `(declare-sort |S| 0)` then `(declare-fun x () S)` is the same
    // rule, and leaving one map out is how this defect survived in the first
    // place.
    return findEitherSpelling(sort_key_map_, name);
}

void SymbolManager::pushLetScope() {
    let_scope_checkpoints_.push_back(let_scope_backup_.size());
}

void SymbolManager::popLetScope() {
    // condAssert, not assert: the library is compiled with -DNDEBUG in the
    // default Release build, where assert() is a no-op -- and the two lines
    // below would then read and pop an empty vector, which is undefined
    // behaviour. condAssert throws unconditionally, so an unbalanced pop
    // surfaces as a diagnosable error in every configuration.
    condAssert(!let_scope_checkpoints_.empty(), "popLetScope: no checkpoint to pop");
    size_t checkpoint = let_scope_checkpoints_.back();
    let_scope_checkpoints_.pop_back();
    // Restore from the end of backup list back to checkpoint
    for (size_t i = let_scope_backup_.size(); i > checkpoint; --i) {
        const LetBackup& backup = let_scope_backup_[i - 1];
        if (backup.hadOld) {
            let_key_map_[backup.name] = backup.oldNode;
        } else {
            let_key_map_.erase(backup.name);
        }
    }
    let_scope_backup_.resize(checkpoint);
}

void SymbolManager::popLetScope(const std::vector<std::string>& keys) {
    for (const auto& k : keys) let_key_map_.erase(bindingName(k));
}

void SymbolManager::registerLet(const std::string& name, const std::shared_ptr<DAGNode>& node) {
    LetBackup backup;
    const std::string key = bindingName(name);
    backup.name = key;
    auto it = let_key_map_.find(key);
    if (it != let_key_map_.end()) {
        backup.oldNode = it->second;
        backup.hadOld = true;
    } else {
        backup.hadOld = false;
    }
    let_scope_backup_.push_back(std::move(backup));
    let_key_map_[key] = node;
}

bool SymbolManager::hasLet(const std::string& name) const {
    return let_key_map_.find(bindingName(name)) != let_key_map_.end();
}

void SymbolManager::registerFun(const std::string& name, const std::shared_ptr<DAGNode>& node) {
    fun_key_map_[name] = node;
}

std::shared_ptr<DAGNode> SymbolManager::getFun(const std::string& name) const {
    return findEitherSpelling(fun_key_map_, name);
}

bool SymbolManager::hasFun(const std::string& name) const {
    return findEitherSpelling(fun_key_map_, name) != nullptr;
}

void SymbolManager::registerRecursiveDefinition(const std::shared_ptr<DAGNode>& symbol,
                                                const std::shared_ptr<DAGNode>& definition) {
    recursive_definitions_[symbol->getName()] = {symbol, definition};
    registerFun(symbol->getName(), definition);
}

std::shared_ptr<DAGNode> SymbolManager::getRecursiveSymbol(const std::shared_ptr<DAGNode>& function) const {
    const auto it = recursive_definitions_.find(function->getName());
    if (it != recursive_definitions_.end() && it->second.definition == function)
        return it->second.symbol;
    // Also used while parsing a recursive group, before bodies exist.
    return function;
}

std::vector<SymbolManager::RecursiveDefinition> SymbolManager::getRecursiveDefinitions() const {
    std::vector<RecursiveDefinition> result;
    for (const auto& name : function_names_) {
        auto it = recursive_definitions_.find(name);
        if (it != recursive_definitions_.end()) result.push_back(it->second);
    }
    return result;
}

void SymbolManager::registerFunVar(const std::string& name, const std::shared_ptr<DAGNode>& node) {
    fun_var_map_[name] = node;
}

void SymbolManager::eraseFunVar(const std::string& key) {
    fun_var_map_.erase(key);
}

bool SymbolManager::hasFunVar(const std::string& name) const {
    return fun_var_map_.find(name) != fun_var_map_.end();
}

void SymbolManager::registerSort(const std::string& name, const std::shared_ptr<Sort>& sort) {
    if (sort_key_map_.find(name) == sort_key_map_.end()) sort_order_.push_back(name);
    sort_key_map_[name] = sort;
}

std::shared_ptr<Sort> SymbolManager::bindTemporarySort(
    const std::string& name, const std::shared_ptr<Sort>& sort) {
    const auto prior = sort_key_map_.find(name);
    const std::shared_ptr<Sort> previous =
        prior == sort_key_map_.end() ? nullptr : prior->second;
    sort_key_map_[name] = sort;
    return previous;
}

void SymbolManager::restoreTemporarySort(
    const std::string& name, const std::shared_ptr<Sort>& previous) {
    if (previous) { sort_key_map_[name] = previous; }
    else { sort_key_map_.erase(name); }
}

bool SymbolManager::hasSort(const std::string& name) const {
    return sort_key_map_.find(name) != sort_key_map_.end();
}

void SymbolManager::removeSort(const std::string& name) {
    sort_key_map_.erase(name);
}

void SymbolManager::registerQuantVar(const std::string& name, const std::shared_ptr<DAGNode>& node) {
    quant_var_map_[bindingName(name)].push_back(node);
}

std::shared_ptr<DAGNode> SymbolManager::getQuantVar(const std::string& name) const {
    auto it = quant_var_map_.find(bindingName(name));
    return it != quant_var_map_.end() ? it->second.back() : nullptr;
}

void SymbolManager::popQuantScope(const std::vector<std::string>& keys) {
    for (auto key = keys.rbegin(); key != keys.rend(); ++key) {
        auto it = quant_var_map_.find(bindingName(*key));
        if (it == quant_var_map_.end()) continue;
        it->second.pop_back();
        if (it->second.empty()) quant_var_map_.erase(it);
    }
}

bool SymbolManager::hasQuantVar(const std::string& name) const {
    return getQuantVar(name) != nullptr;
}

void SymbolManager::registerVar(const std::string& name, const std::shared_ptr<DAGNode>& node) {
    if (var_names_.find(name) == var_names_.end()) var_order_.push_back(name);
    var_names_[name] = node;
}

std::shared_ptr<DAGNode> SymbolManager::getVar(const std::string& name) const {
    return findEitherSpelling(var_names_, name);
}

bool SymbolManager::hasVar(const std::string& name) const {
    return findEitherSpelling(var_names_, name) != nullptr;
}

void SymbolManager::removeVar(const std::string& name) {
    var_names_.erase(name);
}

void SymbolManager::renameVar(const std::string& old_name, const std::string& new_name) {
    auto it = var_names_.find(old_name);
    if (it != var_names_.end()) {
        auto node = it->second;
        var_names_.erase(it);
        var_names_[new_name] = node;
    }
}

const std::unordered_map<std::string, std::shared_ptr<DAGNode>>& SymbolManager::getVarNames() const {
    return var_names_;
}

size_t SymbolManager::nextTempVarCounter() {
    return temp_var_counter_++;
}

void SymbolManager::registerTempVar(const std::string& name, const std::shared_ptr<DAGNode>& node) {
    if (temp_var_names_.find(name) == temp_var_names_.end()) temp_var_order_.push_back(name);
    temp_var_names_[name] = node;
}

std::shared_ptr<DAGNode> SymbolManager::getTempVar(const std::string& name) const {
    auto it = temp_var_names_.find(name);
    return it != temp_var_names_.end() ? it->second : nullptr;
}

bool SymbolManager::hasTempVar(const std::string& name) const {
    return temp_var_names_.find(name) != temp_var_names_.end();
}

void SymbolManager::renameTempVar(const std::string& old_name, const std::string& new_name) {
    auto it = temp_var_names_.find(old_name);
    if (it != temp_var_names_.end()) {
        auto node = it->second;
        temp_var_names_.erase(it);
        temp_var_names_[new_name] = node;
    }
}

const std::unordered_map<std::string, std::shared_ptr<DAGNode>>& SymbolManager::getTempVarNames() const {
    return temp_var_names_;
}

void SymbolManager::registerPlaceholderVar(const std::string& name, const std::shared_ptr<DAGNode>& node) {
    placeholder_var_names_[name] = node;
}

std::shared_ptr<DAGNode> SymbolManager::getPlaceholderVar(const std::string& name) const {
    auto it = placeholder_var_names_.find(name);
    return it != placeholder_var_names_.end() ? it->second : nullptr;
}

bool SymbolManager::hasPlaceholderVar(const std::string& name) const {
    return placeholder_var_names_.find(name) != placeholder_var_names_.end();
}

void SymbolManager::addFunctionName(const std::string& name) {
    // Idempotent, like registerSort. Parser::mkFuncDec now records the name
    // itself, and the (declare-fun ...) command path also calls this after it,
    // so the same name arrives twice on that path; two entries would emit two
    // declare-fun lines for one function.
    if (!function_names_seen_.insert(name).second) { return; }
    function_names_.emplace_back(name);
}

const std::vector<std::string>& SymbolManager::getFunctionNames() const {
    return function_names_;
}

std::shared_ptr<DAGNode> SymbolManager::getFunctionByRecordedName(
    const std::string& name) const {
    const auto it = fun_key_map_.find(name);
    return it != fun_key_map_.end() ? it->second : nullptr;
}

std::vector<std::shared_ptr<DAGNode>> SymbolManager::getFunctions() const {
    std::vector<std::shared_ptr<DAGNode>> result;
    result.reserve(function_names_.size());
    for (const auto& name : function_names_) {
        auto it = fun_key_map_.find(name);
        result.push_back(it != fun_key_map_.end() ? it->second : nullptr);
    }
    return result;
}

bool SymbolManager::hasFunctionName(const std::string& name) const {
    return function_names_seen_.find(name) != function_names_seen_.end();
}

void SymbolManager::addRecFunGroup(const std::vector<std::string>& names) {
    if (names.empty()) return;
    const size_t index = rec_fun_groups_.size();
    rec_fun_groups_.emplace_back(names);
    for (const auto& name : names) {
        rec_fun_group_of_[name] = index;
    }
}

const std::vector<std::string>* SymbolManager::getRecFunGroup(const std::string& name) const {
    auto it = rec_fun_group_of_.find(name);
    if (it == rec_fun_group_of_.end()) return nullptr;
    condAssert(it->second < rec_fun_groups_.size(), "getRecFunGroup: dangling group index");
    return &rec_fun_groups_[it->second];
}

void SymbolManager::removeFunctionName(const std::string& name) {
    function_names_seen_.erase(name);
    auto it = std::find(function_names_.begin(), function_names_.end(), name);
    if (it != function_names_.end()) function_names_.erase(it);
}

void SymbolManager::addStaticFunction(const std::shared_ptr<DAGNode>& node) {
    static_functions_.emplace_back(node);
}

const std::vector<std::shared_ptr<DAGNode>>& SymbolManager::getStaticFunctions() const {
    return static_functions_;
}

const std::vector<std::string>& SymbolManager::getSortOrder() const {
    return sort_order_;
}

const std::vector<std::string>& SymbolManager::getVarOrder() const {
    return var_order_;
}

const std::vector<std::string>& SymbolManager::getTempVarOrder() const {
    return temp_var_order_;
}

const std::unordered_map<std::string, std::shared_ptr<Sort>>& SymbolManager::getSortKeyMap() const {
    return sort_key_map_;
}

void SymbolManager::removeFun(const std::string& name) {
    fun_key_map_.erase(name);
    recursive_definitions_.erase(name);
    removeFunctionName(name);
    rec_fun_group_of_.erase(name);
}

} // namespace SOMTParser
