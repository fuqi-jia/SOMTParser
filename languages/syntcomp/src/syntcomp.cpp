/* -*- Source -*-
 * SYNTCOMP TLSF finite-LTL and infinite one-step safety-game frontend.
 *
 * Complete symbolic monitors preserve the source Mealy/Moore move order.
 * Finite words use reachability; standard infinite safety contracts use Buchi
 * acceptance so that later assumption failure can rescue guarantee failure.
 * Stateless input-only assumptions retain the exact response-table fast path.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/syntcomp.h"

#include <algorithm>
#include <cctype>
#include <filesystem>
#include <fstream>
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
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

constexpr std::size_t INPUT_LIMIT = 16;

struct Token {
    enum Kind { WORD, STRING, SYMBOL } kind = WORD;
    std::string text;
};

class Lexer {
public:
    explicit Lexer(const std::string& source) : source_(source) {}

    bool read(std::vector<Token>& result, std::string& error) {
        while (skip(error)) {
            if (at_ == source_.size()) { return true; }
            const char c = source_[at_];
            if (source_.compare(at_, 4, "X[!]") == 0) {
                result.push_back({Token::WORD, "X!"});
                at_ += 4;
                continue;
            }
            if (c == '"') {
                if (!quoted(result, error)) { return false; }
                continue;
            }
            if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
                const std::size_t begin = at_++;
                while (at_ < source_.size()
                       && (std::isalnum(static_cast<unsigned char>(source_[at_]))
                           || source_[at_] == '_' || source_[at_] == '\''
                           || source_[at_] == '@')) {
                    ++at_;
                }
                result.push_back({Token::WORD, source_.substr(begin, at_ - begin)});
                continue;
            }
            static const std::vector<std::string> multi = {"<->", "->", "&&", "||"};
            bool matched = false;
            for (const std::string& symbol : multi) {
                if (source_.compare(at_, symbol.size(), symbol) == 0) {
                    result.push_back({Token::SYMBOL, symbol});
                    at_ += symbol.size();
                    matched = true;
                    break;
                }
            }
            if (matched) { continue; }
            if (std::string("{}():;!,").find(c) != std::string::npos) {
                result.push_back({Token::SYMBOL, std::string(1, c)});
                ++at_;
                continue;
            }
            error = std::string("unsupported TLSF character '") + c + "'";
            return false;
        }
        return false;
    }

private:
    bool skip(std::string& error) {
        for (;;) {
            while (at_ < source_.size()
                   && std::isspace(static_cast<unsigned char>(source_[at_]))) {
                ++at_;
            }
            if (source_.compare(at_, 2, "//") == 0) {
                while (at_ < source_.size() && source_[at_] != '\n') { ++at_; }
                continue;
            }
            if (source_.compare(at_, 2, "/*") == 0) {
                const std::size_t end = source_.find("*/", at_ + 2);
                if (end == std::string::npos) {
                    error = "unterminated TLSF block comment";
                    return false;
                }
                at_ = end + 2;
                continue;
            }
            return true;
        }
    }

    bool quoted(std::vector<Token>& result, std::string& error) {
        std::string value;
        ++at_;
        while (at_ < source_.size() && source_[at_] != '"') {
            if (source_[at_] == '\\') {
                if (++at_ == source_.size()) {
                    error = "unterminated escape in TLSF string";
                    return false;
                }
            }
            value.push_back(source_[at_++]);
        }
        if (at_ == source_.size()) {
            error = "unterminated TLSF string";
            return false;
        }
        ++at_;
        result.push_back({Token::STRING, std::move(value)});
        return true;
    }

    const std::string& source_;
    std::size_t at_ = 0;
};

struct Formula {
    enum Kind {
        VARIABLE, TRUE_VALUE, FALSE_VALUE, NOT, AND, OR, IMPLIES, IFF,
        NEXT_WEAK, NEXT_STRONG, GLOBALLY, EVENTUALLY, UNTIL, RELEASE, WEAK_UNTIL,
    };
    std::size_t id = 0;
    Kind kind = TRUE_VALUE;
    std::string variable;
    std::shared_ptr<Formula> left;
    std::shared_ptr<Formula> right;
};

using FormulaPtr = std::shared_ptr<Formula>;

class FormulaFactory {
public:
    FormulaPtr make(Formula::Kind kind, FormulaPtr left = {}, FormulaPtr right = {},
                    std::string variable = {}) {
        if (kind == Formula::IMPLIES) {
            return make(Formula::OR, make(Formula::NOT, std::move(left)),
                        std::move(right));
        }
        if (kind == Formula::IFF) {
            FormulaPtr a = left;
            FormulaPtr b = right;
            return make(Formula::AND, make(Formula::IMPLIES, a, b),
                        make(Formula::IMPLIES, b, a));
        }
        if (kind == Formula::NOT || kind == Formula::AND || kind == Formula::OR) {
            const std::size_t lhs = left ? booleanFunction(left) : 0;
            const std::size_t rhs = right ? booleanFunction(right) : 0;
            const std::size_t root = kind == Formula::NOT
                ? negate(lhs)
                : apply(kind == Formula::AND, lhs, rhs);
            return materialize(root);
        }
        return intern(kind, std::move(variable), std::move(left), std::move(right));
    }
    FormulaPtr atom(const std::string& name) {
        return intern(Formula::VARIABLE, name, {}, {});
    }
    FormulaPtr boolean(bool value) {
        return intern(value ? Formula::TRUE_VALUE : Formula::FALSE_VALUE, {}, {}, {});
    }
    FormulaPtr byId(std::size_t id) const { return formulas_.at(id); }
    bool propositionallyImplies(const FormulaPtr& premise,
                                const FormulaPtr& conclusion) {
        const std::size_t required = booleanFunction(conclusion);
        const std::size_t counterexample = apply(
            true, booleanFunction(premise), negate(required));
        return counterexample == 0;
    }
    bool positiveConjuncts(const FormulaPtr& formula, std::vector<FormulaPtr>& atoms) {
        // Inspect the Boolean quotient itself: materialize() may retain dead
        // Shannon branches, so its OR/AND syntax is not a conjunction test.
        // A positive conjunction has low=false at each ordered BDD node and
        // follows its high branch to true. Constants are admitted separately.
        atoms.clear();
        std::size_t root = booleanFunction(formula);
        if (root <= 1) { return true; }
        while (root > 1) {
            const BoolNode node = bool_nodes_.at(root);
            if (node.low != 0) { return false; }
            atoms.push_back(formulas_.at(node.variable));
            root = node.high;
        }
        return root == 1;
    }

private:
    struct BoolNode {
        std::size_t variable;
        std::size_t low;
        std::size_t high;
    };

    std::size_t booleanFunction(const FormulaPtr& formula) {
        const auto known = formula_to_bdd_.find(formula->id);
        if (known != formula_to_bdd_.end()) { return known->second; }
        std::size_t result;
        switch (formula->kind) {
        case Formula::TRUE_VALUE: result = 1; break;
        case Formula::FALSE_VALUE: result = 0; break;
        case Formula::NOT: result = negate(booleanFunction(formula->left)); break;
        case Formula::AND:
            result = apply(true, booleanFunction(formula->left),
                           booleanFunction(formula->right));
            break;
        case Formula::OR:
            result = apply(false, booleanFunction(formula->left),
                           booleanFunction(formula->right));
            break;
        default: result = makeNode(formula->id, 0, 1); break;
        }
        formula_to_bdd_.emplace(formula->id, result);
        return result;
    }

    std::size_t makeNode(std::size_t variable, std::size_t low, std::size_t high) {
        if (low == high) { return low; }
        const auto key = std::make_tuple(variable, low, high);
        const auto known = unique_.find(key);
        if (known != unique_.end()) { return known->second; }
        const std::size_t id = bool_nodes_.size();
        bool_nodes_.push_back({variable, low, high});
        unique_.emplace(key, id);
        return id;
    }

    std::size_t negate(std::size_t value) {
        const auto known = negated_.find(value);
        if (known != negated_.end()) { return known->second; }
        const BoolNode node = bool_nodes_.at(value);
        const std::size_t result = makeNode(node.variable, negate(node.low),
                                            negate(node.high));
        negated_.emplace(value, result);
        negated_.emplace(result, value);
        return result;
    }

    std::size_t apply(bool is_and, std::size_t lhs, std::size_t rhs) {
        if (lhs > rhs) { std::swap(lhs, rhs); }
        if (is_and) {
            if (lhs == 0 || rhs == 0) { return 0; }
            if (lhs == 1) { return rhs; }
            if (rhs == 1 || lhs == rhs) { return lhs; }
        } else {
            if (lhs == 1 || rhs == 1) { return 1; }
            if (lhs == 0) { return rhs; }
            if (rhs == 0 || lhs == rhs) { return lhs; }
        }
        const auto key = std::make_tuple(is_and, lhs, rhs);
        const auto known = applied_.find(key);
        if (known != applied_.end()) { return known->second; }
        const std::size_t lhs_var = bool_nodes_[lhs].variable;
        const std::size_t rhs_var = bool_nodes_[rhs].variable;
        const std::size_t top = std::min(lhs_var, rhs_var);
        const std::size_t lhs_low = lhs_var == top ? bool_nodes_[lhs].low : lhs;
        const std::size_t lhs_high = lhs_var == top ? bool_nodes_[lhs].high : lhs;
        const std::size_t rhs_low = rhs_var == top ? bool_nodes_[rhs].low : rhs;
        const std::size_t rhs_high = rhs_var == top ? bool_nodes_[rhs].high : rhs;
        const std::size_t result = makeNode(
            top, apply(is_and, lhs_low, rhs_low), apply(is_and, lhs_high, rhs_high));
        applied_.emplace(key, result);
        return result;
    }

    FormulaPtr materialize(std::size_t id) {
        const auto known = bdd_to_formula_.find(id);
        if (known != bdd_to_formula_.end()) { return known->second; }
        if (id == 0) { return boolean(false); }
        if (id == 1) { return boolean(true); }
        const BoolNode node = bool_nodes_.at(id);
        const FormulaPtr atom = byId(node.variable);
        if (node.low == 0 && node.high == 1) {
            bdd_to_formula_.emplace(id, atom);
            return atom;
        }
        if (node.low == 1 && node.high == 0) {
            const FormulaPtr result = intern(Formula::NOT, {}, atom, {});
            bdd_to_formula_.emplace(id, result);
            return result;
        }
        const FormulaPtr low = materialize(node.low);
        const FormulaPtr high = materialize(node.high);
        const FormulaPtr not_atom = intern(Formula::NOT, {}, atom, {});
        const FormulaPtr low_branch = intern(Formula::AND, {}, not_atom, low);
        const FormulaPtr high_branch = intern(Formula::AND, {}, atom, high);
        const FormulaPtr result = intern(Formula::OR, {}, low_branch, high_branch);
        bdd_to_formula_.emplace(id, result);
        return result;
    }

    FormulaPtr intern(Formula::Kind kind, std::string variable,
                      FormulaPtr left, FormulaPtr right) {
        const auto key = std::make_tuple(static_cast<int>(kind), variable,
                                         left ? left->id : 0, right ? right->id : 0);
        const auto found = interned_.find(key);
        if (found != interned_.end()) { return formulas_[found->second]; }
        auto formula = std::make_shared<Formula>();
        formula->kind = kind;
        formula->variable = std::move(variable);
        formula->left = std::move(left);
        formula->right = std::move(right);
        formula->id = formulas_.size();
        interned_.emplace(key, formula->id);
        formulas_.push_back(formula);
        return formula;
    }
    std::vector<BoolNode> bool_nodes_{{0, 0, 0}, {0, 1, 1}};
    std::map<std::tuple<std::size_t, std::size_t, std::size_t>, std::size_t> unique_;
    std::map<std::tuple<bool, std::size_t, std::size_t>, std::size_t> applied_;
    std::map<std::size_t, std::size_t> negated_{{0, 1}, {1, 0}};
    std::map<std::size_t, std::size_t> formula_to_bdd_;
    std::map<std::size_t, FormulaPtr> bdd_to_formula_;
    std::map<std::tuple<int, std::string, std::size_t, std::size_t>, std::size_t> interned_;
    std::vector<FormulaPtr> formulas_{nullptr};
};

class FormulaParser {
public:
    FormulaParser(std::vector<Token> tokens, const std::set<std::string>& signals,
                  FormulaFactory& formulas)
        : tokens_(std::move(tokens)), signals_(signals), formulas_(formulas) {}

    FormulaPtr parse(Uir::Diagnostics& diagnostics) {
        FormulaPtr result = iff(diagnostics);
        if (!result || at_ != tokens_.size()) {
            if (!diagnostics.hasErrors()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "trailing token in TLSF invariant formula");
            }
            return nullptr;
        }
        return result;
    }

private:
    bool take(const std::string& text) {
        if (at_ < tokens_.size() && tokens_[at_].text == text) {
            ++at_;
            return true;
        }
        return false;
    }

    FormulaPtr make(Formula::Kind kind, FormulaPtr left = {}, FormulaPtr right = {}) {
        return formulas_.make(kind, std::move(left), std::move(right));
    }

    FormulaPtr iff(Uir::Diagnostics& diagnostics) {
        FormulaPtr result = implies(diagnostics);
        while (result && take("<->")) {
            FormulaPtr rhs = implies(diagnostics);
            if (!rhs) { return nullptr; }
            result = make(Formula::IFF, result, rhs);
        }
        return result;
    }

    FormulaPtr implies(Uir::Diagnostics& diagnostics) {
        FormulaPtr lhs = disjunction(diagnostics);
        if (!lhs || !take("->")) { return lhs; }
        FormulaPtr rhs = implies(diagnostics);
        return rhs ? make(Formula::IMPLIES, lhs, rhs) : nullptr;
    }

    FormulaPtr disjunction(Uir::Diagnostics& diagnostics) {
        FormulaPtr result = conjunction(diagnostics);
        while (result && take("||")) {
            FormulaPtr rhs = conjunction(diagnostics);
            if (!rhs) { return nullptr; }
            result = make(Formula::OR, result, rhs);
        }
        return result;
    }

    FormulaPtr conjunction(Uir::Diagnostics& diagnostics) {
        FormulaPtr result = temporal(diagnostics);
        while (result && take("&&")) {
            FormulaPtr rhs = temporal(diagnostics);
            if (!rhs) { return nullptr; }
            result = make(Formula::AND, result, rhs);
        }
        return result;
    }

    FormulaPtr temporal(Uir::Diagnostics& diagnostics) {
        FormulaPtr lhs = unary(diagnostics);
        if (!lhs || at_ == tokens_.size()) { return lhs; }
        Formula::Kind kind;
        const std::string& token = tokens_[at_].text;
        if (token == "U") { kind = Formula::UNTIL; }
        else if (token == "R") { kind = Formula::RELEASE; }
        else if (token == "W") { kind = Formula::WEAK_UNTIL; }
        else { return lhs; }
        ++at_;
        FormulaPtr rhs = temporal(diagnostics);
        return rhs ? make(kind, lhs, rhs) : nullptr;
    }

    FormulaPtr unary(Uir::Diagnostics& diagnostics) {
        if (take("!") || take("not")) {
            FormulaPtr child = unary(diagnostics);
            return child ? make(Formula::NOT, child) : nullptr;
        }
        if (take("(")) {
            FormulaPtr result = iff(diagnostics);
            if (!result || !take(")")) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "unbalanced parentheses in TLSF invariant");
                return nullptr;
            }
            return result;
        }
        if (take("G")) {
            FormulaPtr child = unary(diagnostics);
            return child ? make(Formula::GLOBALLY, child) : nullptr;
        }
        if (take("F")) {
            FormulaPtr child = unary(diagnostics);
            return child ? make(Formula::EVENTUALLY, child) : nullptr;
        }
        if (take("X")) {
            FormulaPtr child = unary(diagnostics);
            return child ? make(Formula::NEXT_WEAK, child) : nullptr;
        }
        if (take("X!")) {
            FormulaPtr child = unary(diagnostics);
            return child ? make(Formula::NEXT_STRONG, child) : nullptr;
        }
        if (at_ == tokens_.size() || tokens_[at_].kind != Token::WORD) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "expected signal or Boolean literal in TLSF invariant");
            return nullptr;
        }
        const std::string name = tokens_[at_++].text;
        if (name == "true" || name == "TRUE") { return make(Formula::TRUE_VALUE); }
        if (name == "false" || name == "FALSE") { return make(Formula::FALSE_VALUE); }
        if (signals_.count(name) == 0) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "TLSF formula references undeclared signal '" + name + "'");
            return nullptr;
        }
        return formulas_.atom(name);
    }

    std::vector<Token> tokens_;
    const std::set<std::string>& signals_;
    FormulaFactory& formulas_;
    std::size_t at_ = 0;
};

class BddManager {
public:
    using Id = std::size_t;
    struct Node { std::size_t variable; Id low; Id high; };

    explicit BddManager(std::vector<std::string> variables)
        : variables_(std::move(variables)), nodes_{{0, 0, 0}, {0, 1, 1}} {
        negated_.emplace(0, 1);
        negated_.emplace(1, 0);
        for (std::size_t i = 0; i < variables_.size(); ++i) {
            variable_index_.emplace(variables_[i], i);
        }
    }
    Id variable(const std::string& name) {
        const auto found = variable_index_.find(name);
        if (found == variable_index_.end()) { throw std::logic_error("unknown BDD atom"); }
        return node(found->second, 0, 1);
    }
    Id negate(Id value) {
        const auto found = negated_.find(value);
        if (found != negated_.end()) { return found->second; }
        const Node item = nodes_.at(value);
        const Id result = node(item.variable, negate(item.low), negate(item.high));
        negated_.emplace(value, result);
        negated_.emplace(result, value);
        return result;
    }
    Id conjunction(Id lhs, Id rhs) { return apply(true, lhs, rhs); }
    Id disjunction(Id lhs, Id rhs) { return apply(false, lhs, rhs); }
    const Node& get(Id id) const { return nodes_.at(id); }
    const std::string& variableName(std::size_t index) const {
        return variables_.at(index);
    }
    Id existentiallyQuantify(Id value, const std::set<std::string>& variables) {
        std::set<std::size_t> indices;
        for (const std::string& name : variables) {
            const auto found = variable_index_.find(name);
            if (found == variable_index_.end()) {
                throw std::logic_error("unknown BDD variable in quantifier");
            }
            indices.insert(found->second);
        }
        std::map<Id, Id> cache;
        return quantify(value, indices, cache);
    }
    Id universallyQuantify(Id value, const std::set<std::string>& variables) {
        return negate(existentiallyQuantify(negate(value), variables));
    }
    std::size_t size() const { return nodes_.size(); }

private:
    Id node(std::size_t variable, Id low, Id high) {
        if (low == high) { return low; }
        const auto key = std::make_tuple(variable, low, high);
        const auto found = unique_.find(key);
        if (found != unique_.end()) { return found->second; }
        const Id result = nodes_.size();
        nodes_.push_back({variable, low, high});
        unique_.emplace(key, result);
        return result;
    }
    Id quantify(Id value, const std::set<std::size_t>& variables,
                std::map<Id, Id>& cache) {
        if (value < 2) { return value; }
        const auto found = cache.find(value);
        if (found != cache.end()) { return found->second; }
        const Node current = nodes_.at(value);
        const Id low = quantify(current.low, variables, cache);
        const Id high = quantify(current.high, variables, cache);
        const Id result = variables.count(current.variable)
            ? disjunction(low, high) : node(current.variable, low, high);
        cache.emplace(value, result);
        return result;
    }
    Id apply(bool is_and, Id lhs, Id rhs) {
        if (lhs > rhs) { std::swap(lhs, rhs); }
        if (is_and) {
            if (lhs == 0 || rhs == 0) { return 0; }
            if (lhs == 1) { return rhs; }
            if (rhs == 1 || lhs == rhs) { return lhs; }
        } else {
            if (lhs == 1 || rhs == 1) { return 1; }
            if (lhs == 0) { return rhs; }
            if (rhs == 0 || lhs == rhs) { return lhs; }
        }
        const auto key = std::make_tuple(is_and, lhs, rhs);
        const auto found = applied_.find(key);
        if (found != applied_.end()) { return found->second; }
        const std::size_t lhs_var = nodes_[lhs].variable;
        const std::size_t rhs_var = nodes_[rhs].variable;
        const std::size_t top = std::min(lhs_var, rhs_var);
        const Id lhs_low = lhs_var == top ? nodes_[lhs].low : lhs;
        const Id lhs_high = lhs_var == top ? nodes_[lhs].high : lhs;
        const Id rhs_low = rhs_var == top ? nodes_[rhs].low : rhs;
        const Id rhs_high = rhs_var == top ? nodes_[rhs].high : rhs;
        const Id result = node(top, apply(is_and, lhs_low, rhs_low),
                               apply(is_and, lhs_high, rhs_high));
        applied_.emplace(key, result);
        return result;
    }

    std::vector<std::string> variables_;
    std::map<std::string, std::size_t> variable_index_;
    std::vector<Node> nodes_;
    std::map<std::tuple<std::size_t, Id, Id>, Id> unique_;
    std::map<std::tuple<bool, Id, Id>, Id> applied_;
    std::map<Id, Id> negated_;
};

struct AutomatonState {
    std::size_t residual = 0;
    bool accepting = false;
    bool operator<(const AutomatonState& other) const {
        return std::tie(residual, accepting) < std::tie(other.residual, other.accepting);
    }
};

struct SymbolicAutomaton {
    std::vector<AutomatonState> states;
    // Each source state maps to target states and exact letter-condition BDDs.
    std::vector<std::map<std::size_t, BddManager::Id>> edges;
    std::size_t initial = 0;
};

class LtlProgression {
public:
    LtlProgression(FormulaFactory& formulas, BddManager& bdds)
        : formulas_(formulas), bdds_(bdds) {}

    std::map<std::size_t, BddManager::Id> progress(std::size_t formula_id) {
        const FormulaPtr formula = formulas_.byId(formula_id);
        std::map<std::size_t, BddManager::Id> result;
        switch (formula->kind) {
        case Formula::TRUE_VALUE:
        case Formula::FALSE_VALUE:
            return {{formula_id, 1}};
        case Formula::VARIABLE: {
            const BddManager::Id atom = bdds_.variable(formula->variable);
            merge(result, formulas_.boolean(true)->id, atom);
            merge(result, formulas_.boolean(false)->id, bdds_.negate(atom));
            return result;
        }
        case Formula::NOT: {
            for (const auto& [residual, condition] : progress(formula->left->id)) {
                merge(result, formulas_.make(Formula::NOT, formulas_.byId(residual))->id,
                      condition);
            }
            return result;
        }
        case Formula::AND:
        case Formula::OR: {
            const bool is_and = formula->kind == Formula::AND;
            const auto lhs = progress(formula->left->id);
            const auto rhs = progress(formula->right->id);
            for (const auto& [left_residual, left_condition] : lhs) {
                for (const auto& [right_residual, right_condition] : rhs) {
                    const auto condition = bdds_.conjunction(left_condition, right_condition);
                    // No input letter takes this pair; do not intern its residual.
                    if (condition == 0) { continue; }
                    const auto residual = formulas_.make(
                        formula->kind, formulas_.byId(left_residual),
                        formulas_.byId(right_residual));
                    merge(result, residual->id, condition);
                }
            }
            (void)is_and;
            return result;
        }
        case Formula::NEXT_WEAK:
        case Formula::NEXT_STRONG:
            return {{formula->left->id, 1}};
        case Formula::GLOBALLY:
        case Formula::EVENTUALLY: {
            const bool is_globally = formula->kind == Formula::GLOBALLY;
            for (const auto& [child_residual, condition] : progress(formula->left->id)) {
                FormulaPtr residual = formulas_.make(
                    is_globally ? Formula::AND : Formula::OR,
                    formulas_.byId(child_residual), formula);
                merge(result, residual->id, condition);
            }
            return result;
        }
        case Formula::UNTIL:
        case Formula::WEAK_UNTIL:
        case Formula::RELEASE: {
            const auto lhs = progress(formula->left->id);
            const auto rhs = progress(formula->right->id);
            for (const auto& [left_residual, left_condition] : lhs) {
                for (const auto& [right_residual, right_condition] : rhs) {
                    const auto condition = bdds_.conjunction(left_condition, right_condition);
                    // No input letter takes this pair; do not intern its residual.
                    if (condition == 0) { continue; }
                    FormulaPtr residual;
                    if (formula->kind == Formula::RELEASE) {
                        residual = formulas_.make(Formula::AND,
                            formulas_.byId(right_residual),
                            formulas_.make(Formula::OR,
                                formulas_.byId(left_residual), formula));
                    } else {
                        residual = formulas_.make(Formula::OR,
                            formulas_.byId(right_residual),
                            formulas_.make(Formula::AND,
                                formulas_.byId(left_residual), formula));
                    }
                    merge(result, residual->id, condition);
                }
            }
            return result;
        }
        case Formula::IMPLIES:
        case Formula::IFF:
            throw std::logic_error("FormulaFactory must normalize Boolean sugar");
        }
        throw std::logic_error("unknown LTL formula kind");
    }

    BddManager::Id terminal(std::size_t formula_id) {
        const FormulaPtr formula = formulas_.byId(formula_id);
        switch (formula->kind) {
        case Formula::TRUE_VALUE: return 1;
        case Formula::FALSE_VALUE: return 0;
        case Formula::VARIABLE: return bdds_.variable(formula->variable);
        case Formula::NOT: return bdds_.negate(terminal(formula->left->id));
        case Formula::AND:
            return bdds_.conjunction(terminal(formula->left->id),
                                     terminal(formula->right->id));
        case Formula::OR:
            return bdds_.disjunction(terminal(formula->left->id),
                                     terminal(formula->right->id));
        case Formula::NEXT_WEAK: return 1;
        case Formula::NEXT_STRONG: return 0;
        case Formula::GLOBALLY:
        case Formula::EVENTUALLY: return terminal(formula->left->id);
        case Formula::UNTIL:
        case Formula::RELEASE: return terminal(formula->right->id);
        case Formula::WEAK_UNTIL:
            return bdds_.disjunction(terminal(formula->left->id),
                                     terminal(formula->right->id));
        case Formula::IMPLIES:
        case Formula::IFF:
            throw std::logic_error("FormulaFactory must normalize Boolean sugar");
        }
        throw std::logic_error("unknown LTL formula kind");
    }

    SymbolicAutomaton automaton(std::size_t formula_id) {
        SymbolicAutomaton result;
        const AutomatonState initial{formula_id, false}; // TLSF rejects epsilon.
        std::map<AutomatonState, std::size_t> indices{{initial, 0}};
        std::vector<AutomatonState> pending{initial};
        result.states.push_back(initial);
        for (std::size_t cursor = 0; cursor < pending.size(); ++cursor) {
            const AutomatonState source = pending[cursor];
            const auto derivative = progress(source.residual);
            const auto accepting_letters = terminal(source.residual);
            std::map<std::size_t, BddManager::Id> row;
            for (const auto& [residual, condition] : derivative) {
                for (bool accepting : {false, true}) {
                    const auto accept_condition = accepting
                        ? accepting_letters : bdds_.negate(accepting_letters);
                    const auto combined = bdds_.conjunction(condition, accept_condition);
                    if (combined == 0) { continue; }
                    const AutomatonState target{residual, accepting};
                    auto found = indices.find(target);
                    if (found == indices.end()) {
                        const std::size_t id = pending.size();
                        indices.emplace(target, id);
                        pending.push_back(target);
                        result.states.push_back(target);
                        found = indices.find(target);
                    }
                    const std::size_t target_id = found->second;
                    auto previous = row.find(target_id);
                    row[target_id] = previous == row.end()
                        ? combined : bdds_.disjunction(previous->second, combined);
                }
            }
            result.edges.push_back(std::move(row));
        }
        result.initial = 0;
        return result;
    }

private:
    void merge(std::map<std::size_t, BddManager::Id>& result,
               std::size_t residual, BddManager::Id condition) {
        if (condition == 0) { return; }
        auto found = result.find(residual);
        result[residual] = found == result.end()
            ? condition : bdds_.disjunction(found->second, condition);
    }
    FormulaFactory& formulas_;
    BddManager& bdds_;
};

// Standard implication between safety contracts is a Buchi objective, not a
// stepwise safety implication: a later environment failure may rescue an
// earlier system failure. This monitor keeps both exact derivatives.
class InfiniteSafetyMonitor {
public:
    InfiniteSafetyMonitor(FormulaFactory& formulas, BddManager& bdds)
        : formulas_(formulas), bdds_(bdds), progression_(formulas, bdds) {}

    SymbolicAutomaton automaton(const FormulaPtr& initially, const FormulaPtr& preset,
                                const FormulaPtr& environment, const FormulaPtr& system) {
        struct State {
            enum Phase { INITIAL, NORMAL, WIN, LOSE } phase;
            std::size_t environment;
            std::size_t system;
            bool operator<(const State& other) const {
                return std::tie(phase, environment, system)
                    < std::tie(other.phase, other.environment, other.system);
            }
        };
        const State initial{State::INITIAL, environment->id, system->id};
        const State won{State::WIN, 0, 0};
        const State lost{State::LOSE, 0, 0};
        const std::size_t yes = formulas_.boolean(true)->id;
        const std::size_t no = formulas_.boolean(false)->id;
        std::map<State, std::size_t> indices;
        std::vector<State> pending;
        SymbolicAutomaton result;
        auto intern = [&](const State& state) {
            const auto found = indices.find(state);
            if (found != indices.end()) { return found->second; }
            const std::size_t id = pending.size();
            indices.emplace(state, id);
            pending.push_back(state);
            const bool accepting = state.phase == State::WIN
                || state.phase == State::INITIAL
                || (state.phase == State::NORMAL && state.system != no);
            result.states.push_back({id, accepting});
            return id;
        };
        result.initial = intern(initial);
        const auto initial_condition = progression_.terminal(initially->id);
        const auto preset_condition = progression_.terminal(preset->id);
        for (std::size_t cursor = 0; cursor < pending.size(); ++cursor) {
            const State source = pending[cursor];
            std::map<std::size_t, BddManager::Id> row;
            auto edge = [&](const State& state, BddManager::Id condition) {
                if (condition == 0) { return; }
                const std::size_t target = intern(state);
                const auto previous = row.find(target);
                row[target] = previous == row.end() ? condition
                    : bdds_.disjunction(previous->second, condition);
            };
            if (source.phase == State::WIN || source.phase == State::LOSE) {
                edge(source, 1);
            } else {
                BddManager::Id active = 1;
                if (source.phase == State::INITIAL) {
                    edge(won, bdds_.negate(initial_condition));
                    edge(lost, bdds_.conjunction(initial_condition,
                                               bdds_.negate(preset_condition)));
                    active = bdds_.conjunction(initial_condition, preset_condition);
                }
                if (active != 0) {
                    const auto environments = progression_.progress(source.environment);
                    const auto systems = progression_.progress(source.system);
                    for (const auto& [a, a_condition] : environments) {
                        for (const auto& [b, b_condition] : systems) {
                            const auto condition = bdds_.conjunction(active,
                                bdds_.conjunction(a_condition, b_condition));
                            if (a == no || b == yes) { edge(won, condition); }
                            else if (a == yes && b == no) { edge(lost, condition); }
                            else { edge({State::NORMAL, a, b}, condition); }
                        }
                    }
                }
            }
            result.edges.push_back(std::move(row));
        }
        return result;
    }

private:
    FormulaFactory& formulas_;
    BddManager& bdds_;
    LtlProgression progression_;
};

#ifndef SOMT_LTLF_CORE_TEST_ONLY
class TlsfParser {
public:
    TlsfParser(std::string source, std::string file)
        : source_(std::move(source)), file_(std::move(file)) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diagnostics,
                                Uir::TranslationReport& report) {
        std::string error;
        Lexer lexer(source_);
        if (!lexer.read(tokens_, error)) {
            diagnostics.error(ErrorCode::E_PARSE, "TLSF parse error: " + error);
            return nullptr;
        }
        if (!structure(diagnostics) || !formulas(diagnostics)) { return nullptr; }
        return build(diagnostics, report);
    }

    S::ModelProjection projection() const { return projection_; }
    S::Signature sourceSignature() const { return source_signature_; }
    std::vector<S::SymbolMapping> symbolMap() const { return symbol_map_; }

private:
    bool expect(const std::string& text, Uir::Diagnostics& diagnostics) {
        if (at_ < tokens_.size() && tokens_[at_].text == text) {
            ++at_;
            return true;
        }
        diagnostics.error(ErrorCode::E_PARSE,
                          "expected '" + text + "' in TLSF structure");
        return false;
    }

    bool block(std::vector<Token>& result, Uir::Diagnostics& diagnostics) {
        if (!expect("{", diagnostics)) { return false; }
        unsigned depth = 1;
        while (at_ < tokens_.size() && depth != 0) {
            const Token token = tokens_[at_++];
            if (token.text == "{") {
                ++depth;
            } else if (token.text == "}") {
                --depth;
                if (depth == 0) { break; }
            }
            result.push_back(token);
        }
        if (depth != 0) {
            diagnostics.error(ErrorCode::E_PARSE, "unterminated TLSF block");
            return false;
        }
        return true;
    }

    bool info(const std::vector<Token>& content, Uir::Diagnostics& diagnostics) {
        for (std::size_t i = 0; i < content.size();) {
            if (content[i].kind != Token::WORD || i + 2 >= content.size()
                || content[i + 1].text != ":") {
                diagnostics.error(ErrorCode::E_PARSE, "malformed TLSF INFO field");
                return false;
            }
            const std::string key = content[i].text;
            const Token value = content[i + 2];
            i += 3;
            if (key == "TAGS") {
                if (value.kind != Token::STRING) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "TLSF INFO TAGS values must be string literals");
                    return false;
                }
                while (i < content.size() && content[i].text == ",") {
                    if (i + 1 >= content.size()
                        || content[i + 1].kind != Token::STRING) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "malformed TLSF INFO TAGS list");
                        return false;
                    }
                    i += 2;
                }
            }
            if (key == "SEMANTICS" && i + 1 < content.size()
                && content[i].text == ",") {
                const std::string second = content[i + 1].text;
                i += 2;
                if (value.text == "Finite") {
                    finite_ = true;
                    semantics_ = second;
                } else if (second == "Finite") {
                    finite_ = true;
                    semantics_ = value.text;
                } else {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "unsupported TLSF SEMANTICS qualifier pair");
                    return false;
                }
            }
            if (i < content.size() && content[i].text == ";") { ++i; }
            if (key == "SEMANTICS" && !finite_) { semantics_ = value.text; }
            else if (key == "TARGET") { target_ = value.text; }
        }
        if (semantics_ != "Mealy" && semantics_ != "Moore") {
            diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "TLSF requires Mealy or Moore semantics (optionally with Finite)");
            return false;
        }
        if (target_.empty()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "the accepted TLSF invariant game requires a TARGET field");
            return false;
        }
        if (!target_.empty() && target_ != semantics_) {
            diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "different TLSF SEMANTICS/TARGET values require a causal strategy "
                "conversion that this adapter does not silently apply");
            return false;
        }
        return true;
    }

    bool signalList(const std::vector<Token>& content, std::vector<std::string>& result,
                    const std::string& section, Uir::Diagnostics& diagnostics) {
        for (std::size_t i = 0; i < content.size();) {
            // SyFCo's MAIN parser discards empty semicolon-delimited items.
            // Keep that compatibility while still rejecting non-separator junk.
            if (content[i].text == ";") {
                ++i;
                continue;
            }
            if (content[i].kind != Token::WORD) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "expected signal name in " + section);
                return false;
            }
            result.push_back(content[i++].text);
            if (i == content.size() || content[i].text != ";") {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "signal declarations in " + section + " require ';'");
                return false;
            }
            ++i;
        }
        return true;
    }

    bool formulaList(const std::vector<Token>& content,
                     std::vector<std::vector<Token>>& result,
                     const std::string& section, Uir::Diagnostics& diagnostics) {
        std::vector<Token> current;
        for (const Token& token : content) {
            if (token.text == ";") {
                if (current.empty()) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "empty formula in TLSF " + section);
                    return false;
                }
                result.push_back(std::move(current));
                current.clear();
            } else {
                current.push_back(token);
            }
        }
        if (!current.empty()) { result.push_back(std::move(current)); }
        return true;
    }

    bool main(const std::vector<Token>& content, Uir::Diagnostics& diagnostics) {
        std::size_t at = 0;
        std::set<std::string> seen;
        while (at < content.size()) {
            if (content[at].kind != Token::WORD || at + 1 >= content.size()
                || content[at + 1].text != "{") {
                diagnostics.error(ErrorCode::E_PARSE, "malformed TLSF MAIN section");
                return false;
            }
            const std::string name = content[at++].text;
            if (!seen.insert(name).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate TLSF MAIN section '" + name + "'");
                return false;
            }
            ++at;
            unsigned depth = 1;
            std::vector<Token> body;
            while (at < content.size() && depth != 0) {
                const Token token = content[at++];
                if (token.text == "{") {
                    ++depth;
                } else if (token.text == "}") {
                    --depth;
                    if (depth == 0) { break; }
                }
                body.push_back(token);
            }
            if (depth != 0) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "unterminated TLSF MAIN subsection '" + name + "'");
                return false;
            }
            if (name == "INPUTS") {
                if (!signalList(body, inputs_, name, diagnostics)) { return false; }
            } else if (name == "OUTPUTS") {
                if (!signalList(body, outputs_, name, diagnostics)) { return false; }
            } else if (name == "INITIALLY") {
                if (!formulaList(body, initially_tokens_, name, diagnostics)) { return false; }
            } else if (name == "PRESET") {
                if (!formulaList(body, preset_tokens_, name, diagnostics)) { return false; }
            } else if (name == "REQUIRE") {
                if (!formulaList(body, require_tokens_, name, diagnostics)) { return false; }
            } else if (name == "ASSERT" || name == "INVARIANTS") {
                if (!formulaList(body, assert_tokens_, name, diagnostics)) { return false; }
            } else if (name == "ASSUMPTIONS" || name == "ASSUME") {
                if (!formulaList(body, assumption_tokens_, name, diagnostics)) {
                    return false;
                }
            } else if (name == "GUARANTEES" || name == "GUARANTEE") {
                if (!formulaList(body, guarantee_tokens_, name, diagnostics)) {
                    return false;
                }
            } else {
                diagnostics.error(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "TLSF MAIN section '" + name
                        + "' needs high-level elaboration or temporal game semantics");
                return false;
            }
        }
        return true;
    }

    bool structure(Uir::Diagnostics& diagnostics) {
        if (!expect("INFO", diagnostics)) { return false; }
        std::vector<Token> info_content;
        if (!block(info_content, diagnostics) || !info(info_content, diagnostics)) {
            return false;
        }
        if (!expect("MAIN", diagnostics)) { return false; }
        std::vector<Token> main_content;
        if (!block(main_content, diagnostics) || !main(main_content, diagnostics)) {
            return false;
        }
        if (at_ != tokens_.size()) {
            diagnostics.error(ErrorCode::E_PARSE, "trailing tokens after TLSF MAIN block");
            return false;
        }
        std::set<std::string> names;
        for (const std::string& input : inputs_) {
            if (!names.insert(input).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate TLSF signal '" + input + "'");
                return false;
            }
        }
        for (const std::string& output : outputs_) {
            if (!names.insert(output).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate or input/output-overlapping TLSF signal '"
                                      + output + "'");
                return false;
            }
        }
        signals_ = std::move(names);
        return true;
    }

    static void variables(const FormulaPtr& formula, std::set<std::string>& result) {
        if (!formula) { return; }
        if (formula->kind == Formula::VARIABLE) { result.insert(formula->variable); }
        variables(formula->left, result);
        variables(formula->right, result);
    }

    bool formulas(Uir::Diagnostics& diagnostics) {
        auto parse_section = [&](const std::vector<std::vector<Token>>& source,
                                 std::vector<FormulaPtr>& destination) {
            for (const auto& tokens : source) {
                FormulaParser parser(tokens, signals_, formulas_);
                FormulaPtr formula = parser.parse(diagnostics);
                if (!formula) { return false; }
                destination.push_back(std::move(formula));
            }
            return true;
        };
        if (!parse_section(initially_tokens_, initially_)
            || !parse_section(preset_tokens_, preset_)
            || !parse_section(require_tokens_, require_)
            || !parse_section(assert_tokens_, assert_)
            || !parse_section(assumption_tokens_, assumptions_)
            || !parse_section(guarantee_tokens_, guarantees_)) {
            return false;
        }

        const auto is_temporal = [&](const auto& self, const FormulaPtr& formula) -> bool {
            if (!formula) { return false; }
            switch (formula->kind) {
            case Formula::NEXT_WEAK:
            case Formula::NEXT_STRONG:
            case Formula::GLOBALLY:
            case Formula::EVENTUALLY:
            case Formula::UNTIL:
            case Formula::RELEASE:
            case Formula::WEAK_UNTIL: return true;
            default: return self(self, formula->left) || self(self, formula->right);
            }
        };
        const auto is_stateless_invariant = [&](const FormulaPtr& formula) {
            return formula && formula->kind == Formula::GLOBALLY
                && !is_temporal(is_temporal, formula->left);
        };
        invariant_fragment_ = initially_.empty() && preset_.empty()
            && require_.empty() && assert_.empty() && !guarantees_.empty();
        for (const FormulaPtr& formula : assumptions_) {
            invariant_fragment_ = invariant_fragment_ && is_stateless_invariant(formula);
        }
        for (const FormulaPtr& formula : guarantees_) {
            invariant_fragment_ = invariant_fragment_ && is_stateless_invariant(formula);
        }
        if (finite_ && inputs_.size() > INPUT_LIMIT) { invariant_fragment_ = false; }
        if (invariant_fragment_) {
            bool output_dependent_assumption = false;
            for (const FormulaPtr& formula : assumptions_) {
                std::set<std::string> used;
                variables(formula, used);
                for (const std::string& variable : used) {
                    if (std::find(outputs_.begin(), outputs_.end(), variable)
                        != outputs_.end()) {
                        output_dependent_assumption = true;
                        break;
                    }
                }
                if (output_dependent_assumption) { break; }
            }
            if (output_dependent_assumption) { invariant_fragment_ = false; }
            if (invariant_fragment_ && inputs_.size() > INPUT_LIMIT) {
                invariant_fragment_ = false;
            }
        }
        if (!finite_ && !invariant_fragment_ && !isInfiniteSafetyFragment()) {
            diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "this formula needs LTL-to-automaton/parity-game lowering beyond the "
                "supported infinite one-step safety fragment; applying the finite-LTLf "
                "automaton/reachability-game adapter is not reactive realizability "
                "for this infinite-word formula");
            return false;
        }
        return true;
    }

    enum class SafetySyntax { PROPOSITIONAL, ONE_STEP };

    static bool hasSafetySyntax(const FormulaPtr& formula, SafetySyntax syntax) {
        // Boolean quotienting shares subgraphs. Check each node/context once
        // instead of recursively revisiting the same DAG through every parent.
        std::vector<std::pair<FormulaPtr, SafetySyntax>> pending{{formula, syntax}};
        std::set<std::pair<std::size_t, SafetySyntax>> seen;
        while (!pending.empty()) {
            const auto [current, context] = pending.back();
            pending.pop_back();
            if (!current || !seen.emplace(current->id, context).second) { continue; }
            if (current->kind == Formula::TRUE_VALUE
                || current->kind == Formula::FALSE_VALUE) { continue; }
            switch (current->kind) {
            case Formula::VARIABLE: break;
            case Formula::NOT: pending.emplace_back(current->left, context); break;
            case Formula::AND:
            case Formula::OR:
                pending.emplace_back(current->left, context);
                pending.emplace_back(current->right, context);
                break;
            case Formula::NEXT_WEAK:
                if (context != SafetySyntax::ONE_STEP) { return false; }
                pending.emplace_back(current->left, SafetySyntax::PROPOSITIONAL);
                break;
            default: return false;
            }
        }
        return true;
    }

    static bool isPropositional(const FormulaPtr& formula) {
        return hasSafetySyntax(formula, SafetySyntax::PROPOSITIONAL);
    }
    static bool isOneStep(const FormulaPtr& formula) {
        return hasSafetySyntax(formula, SafetySyntax::ONE_STEP);
    }
    bool isGlobalOneStep(const FormulaPtr& formula) {
        std::vector<FormulaPtr> atoms;
        if (!formulas_.positiveConjuncts(formula, atoms)) { return false; }
        return std::all_of(atoms.begin(), atoms.end(), [](const FormulaPtr& atom) {
            return atom->kind == Formula::GLOBALLY && isOneStep(atom->left);
        });
    }

    bool isInfiniteSafetyFragment() {
        return std::all_of(initially_.begin(), initially_.end(), isPropositional)
            && std::all_of(preset_.begin(), preset_.end(), isPropositional)
            && std::all_of(require_.begin(), require_.end(), isOneStep)
            && std::all_of(assert_.begin(), assert_.end(), isOneStep)
            && std::all_of(assumptions_.begin(), assumptions_.end(),
                           [this](const FormulaPtr& formula) { return isGlobalOneStep(formula); })
            && std::all_of(guarantees_.begin(), guarantees_.end(),
                           [this](const FormulaPtr& formula) { return isGlobalOneStep(formula); });
    }

    FormulaPtr conjunction(const std::vector<FormulaPtr>& formulas) {
        FormulaPtr result = formulas_.boolean(true);
        for (const FormulaPtr& formula : formulas) {
            result = formulas_.make(Formula::AND, result, formula);
        }
        return result;
    }

    FormulaPtr finiteSpecification() {
        FormulaPtr initial = conjunction(initially_);
        FormulaPtr preset = conjunction(preset_);
        std::vector<FormulaPtr> environment_invariants;
        for (const FormulaPtr& formula : require_) {
            environment_invariants.push_back(formulas_.make(Formula::GLOBALLY, formula));
        }
        environment_invariants.insert(environment_invariants.end(),
                                      assumptions_.begin(), assumptions_.end());
        std::vector<FormulaPtr> system_invariants;
        for (const FormulaPtr& formula : assert_) {
            system_invariants.push_back(formulas_.make(Formula::GLOBALLY, formula));
        }
        system_invariants.insert(system_invariants.end(), guarantees_.begin(),
                                 guarantees_.end());
        FormulaPtr implication = formulas_.make(
            Formula::IMPLIES, conjunction(environment_invariants),
            conjunction(system_invariants));
        return formulas_.make(Formula::IMPLIES, initial,
            formulas_.make(Formula::AND, preset, implication));
    }

    static H::ExprPtr conjunction(std::vector<H::ExprPtr> terms) {
        if (terms.empty()) { return H::mkBool(true); }
        H::ExprPtr result = std::move(terms.front());
        for (std::size_t i = 1; i < terms.size(); ++i) {
            result = H::mkOp(H::Op::AND, {result, terms[i]});
        }
        return result;
    }

    H::ExprPtr expression(const FormulaPtr& formula,
                          const std::map<std::string, bool>& environment,
                          const std::map<std::string, std::string>& controller) const {
        switch (formula->kind) {
        case Formula::VARIABLE: {
            const auto input = environment.find(formula->variable);
            if (input != environment.end()) { return H::mkBool(input->second); }
            return H::mkIdent(controller.at(formula->variable), H::Sort::boolean());
        }
        case Formula::TRUE_VALUE: return H::mkBool(true);
        case Formula::FALSE_VALUE: return H::mkBool(false);
        case Formula::NOT:
            return H::mkOp(H::Op::NOT,
                           {expression(formula->left, environment, controller)});
        case Formula::AND:
            return H::mkOp(H::Op::AND,
                           {expression(formula->left, environment, controller),
                            expression(formula->right, environment, controller)});
        case Formula::OR:
            return H::mkOp(H::Op::OR,
                           {expression(formula->left, environment, controller),
                            expression(formula->right, environment, controller)});
        case Formula::IMPLIES:
            return H::mkOp(H::Op::IMPLIES,
                           {expression(formula->left, environment, controller),
                            expression(formula->right, environment, controller)});
        case Formula::IFF:
            return H::mkOp(H::Op::EQ,
                           {expression(formula->left, environment, controller),
                            expression(formula->right, environment, controller)});
        case Formula::GLOBALLY:
            return expression(formula->left, environment, controller);
        case Formula::NEXT_WEAK:
        case Formula::NEXT_STRONG:
        case Formula::EVENTUALLY:
        case Formula::UNTIL:
        case Formula::RELEASE:
        case Formula::WEAK_UNTIL:
            throw std::logic_error("temporal formula reached the invariant reducer");
        }
        return H::mkBool(false);
    }

    static H::ExprPtr andExpr(H::ExprPtr lhs, H::ExprPtr rhs) {
        return H::mkOp(H::Op::AND, {std::move(lhs), std::move(rhs)});
    }
    static H::ExprPtr orExpr(H::ExprPtr lhs, H::ExprPtr rhs) {
        return H::mkOp(H::Op::OR, {std::move(lhs), std::move(rhs)});
    }
    static H::ExprPtr impliesExpr(H::ExprPtr lhs, H::ExprPtr rhs) {
        return H::mkOp(H::Op::IMPLIES, {std::move(lhs), std::move(rhs)});
    }

    H::ExprPtr bddExpression(BddManager::Id id, const BddManager& bdds,
                             const std::map<std::string, H::ExprPtr>& atoms,
                             std::map<BddManager::Id, H::ExprPtr>& cache) const {
        if (id == 0) { return H::mkBool(false); }
        if (id == 1) { return H::mkBool(true); }
        const auto cached = cache.find(id);
        if (cached != cache.end()) { return cached->second; }
        const BddManager::Node node = bdds.get(id);
        const H::ExprPtr atom = atoms.at(bdds.variableName(node.variable));
        H::ExprPtr result;
        if (node.low == 0 && node.high == 1) {
            result = atom;
        } else if (node.low == 1 && node.high == 0) {
            result = H::mkOp(H::Op::NOT, {atom});
        } else if (node.low == 0) {
            result = andExpr(atom, bddExpression(node.high, bdds, atoms, cache));
        } else if (node.high == 0) {
            result = andExpr(H::mkOp(H::Op::NOT, {atom}),
                             bddExpression(node.low, bdds, atoms, cache));
        } else {
            H::ExprPtr low = andExpr(H::mkOp(H::Op::NOT, {atom}),
                                     bddExpression(node.low, bdds, atoms, cache));
            H::ExprPtr high = andExpr(atom,
                                      bddExpression(node.high, bdds, atoms, cache));
            result = orExpr(std::move(low), std::move(high));
        }
        cache.emplace(id, result);
        return result;
    }

    H::ConstraintModelPtr buildOneStepRealizable(Uir::TranslationReport& report) {
        auto model = std::make_shared<H::ConstraintModel>();
        H::Constraint constraint;
        constraint.formula = H::mkBool(true);
        model->constraints.push_back(std::move(constraint));

        Uir::EncodingChoice choice;
        choice.site = file_;
        choice.unified_op = "reactive-realizability";
        choice.strategy = "finite-one-step-game-witness";
        choice.fidelity = Uir::Fidelity::exact();
        choice.rationale =
            "the finite specification has a causal winning strategy on its first "
            "non-empty position, proven by exact Boolean quantifier elimination "
            "over Moore or Mealy moves; that one-position play is a witness for "
            "finite realizability, so constructing the full progression DFA is "
            "unnecessary";
        report.addChoice(std::move(choice));
        return model;
    }

    H::ConstraintModelPtr buildFiniteGame(Uir::TranslationReport& report) {
        const FormulaPtr specification = finiteSpecification();
        std::vector<std::string> proposition_order(signals_.begin(), signals_.end());
        BddManager bdds(proposition_order);
        LtlProgression progression(formulas_, bdds);
        const BddManager::Id one_step = progression.terminal(specification->id);
        const std::set<std::string> input_variables(inputs_.begin(), inputs_.end());
        const std::set<std::string> output_variables(outputs_.begin(), outputs_.end());
        const BddManager::Id one_step_winning = semantics_ == "Moore"
            ? bdds.existentiallyQuantify(
                  bdds.universallyQuantify(one_step, input_variables), output_variables)
            : bdds.universallyQuantify(
                  bdds.existentiallyQuantify(one_step, output_variables), input_variables);
        if (one_step_winning == 1) { return buildOneStepRealizable(report); }
        const SymbolicAutomaton automaton = progression.automaton(specification->id);
        return buildAutomatonGame(automaton, bdds, true, report);
    }

    H::ConstraintModelPtr buildInfiniteSafetyGame(Uir::TranslationReport& report) {
        std::vector<FormulaPtr> environment = assumptions_;
        std::vector<FormulaPtr> system = guarantees_;
        for (const auto& formula : require_) {
            environment.push_back(formulas_.make(Formula::GLOBALLY, formula));
        }
        for (const auto& formula : assert_) {
            system.push_back(formulas_.make(Formula::GLOBALLY, formula));
        }
        std::vector<std::string> proposition_order(signals_.begin(), signals_.end());
        BddManager bdds(proposition_order);
        InfiniteSafetyMonitor monitor(formulas_, bdds);
        const auto automaton = monitor.automaton(conjunction(initially_), conjunction(preset_),
                                               conjunction(environment), conjunction(system));
        return buildAutomatonGame(automaton, bdds, false, report);
    }

    H::ConstraintModelPtr buildAutomatonGame(const SymbolicAutomaton& automaton,
                                            const BddManager& bdds, bool finite_word,
                                            Uir::TranslationReport& report) {
        auto model = std::make_shared<H::ConstraintModel>();
        std::string prefix = finite_word ? "__somt_syntcomp_ltl_" : "__somt_syntcomp_buchi_";
        while (source_.find(prefix) != std::string::npos) { prefix += "x"; }

        std::vector<std::string> winning_names(automaton.states.size());
        std::vector<std::string> rank_names(automaton.states.size());
        for (std::size_t q = 0; q < automaton.states.size(); ++q) {
            winning_names[q] = prefix + "win_" + std::to_string(q);
            rank_names[q] = prefix + "rank_" + std::to_string(q);
            H::VarDecl win;
            win.name = winning_names[q];
            win.sort = H::Sort::boolean();
            win.auxiliary = true;
            model->decls.push_back(std::move(win));
            H::VarDecl rank;
            rank.name = rank_names[q];
            rank.sort = H::Sort::integer();
            rank.auxiliary = true;
            model->decls.push_back(std::move(rank));
        }
        auto identifier = [](const std::string& name, H::Sort sort) {
            return H::mkIdent(name, std::move(sort));
        };
        auto addConstraint = [&](H::ExprPtr formula) {
            H::Constraint constraint;
            constraint.formula = std::move(formula);
            model->constraints.push_back(std::move(constraint));
        };
        addConstraint(identifier(winning_names.at(automaton.initial), H::Sort::boolean()));

        std::vector<H::Binder> input_binders;
        std::vector<H::ExprPtr> input_terms;
        for (std::size_t i = 0; i < inputs_.size(); ++i) {
            const std::string name = prefix + "input_" + std::to_string(i);
            input_binders.push_back({name, H::Sort::boolean()});
            input_terms.push_back(H::mkBoundVar(name, H::Sort::boolean()));
        }

        std::vector<std::vector<H::ExprPtr>> output_by_state(
            automaton.states.size(), std::vector<H::ExprPtr>(outputs_.size()));
        for (std::size_t q = 0; q < automaton.states.size(); ++q) {
            // Only finite-word acceptance permits termination. Every infinite
            // accepting state still needs a causal, input-complete next move.
            if (finite_word && automaton.states[q].accepting) { continue; }
            for (std::size_t o = 0; o < outputs_.size(); ++o) {
                if (semantics_ == "Moore" || input_terms.empty()) {
                    const std::string name = prefix + "output_" + std::to_string(q)
                                           + "_" + std::to_string(o);
                    H::VarDecl output;
                    output.name = name;
                    output.sort = H::Sort::boolean();
                    output.auxiliary = true;
                    model->decls.push_back(std::move(output));
                    output_by_state[q][o] = identifier(name, H::Sort::boolean());
                } else {
                    const std::string name = prefix + "output_" + std::to_string(q)
                                           + "_" + std::to_string(o);
                    // Existential strategy witnesses are values, not defined
                    // auxiliary functions. Nested Boolean-indexed arrays denote
                    // every possible response to the current input tuple without
                    // enumerating its valuations or relaxing HIR's definition
                    // requirement for auxiliary FunDecls.
                    H::Sort strategy_sort = H::Sort::boolean();
                    for (std::size_t i = 0; i < input_terms.size(); ++i) {
                        strategy_sort = H::Sort::array(
                            H::Sort::boolean(), std::move(strategy_sort));
                    }
                    H::VarDecl strategy;
                    strategy.name = name;
                    strategy.sort = strategy_sort;
                    strategy.auxiliary = true;
                    model->decls.push_back(std::move(strategy));
                    H::ExprPtr response = identifier(name, strategy_sort);
                    for (const auto& input : input_terms) {
                        response = H::mkOp(H::Op::SELECT, {response, input});
                    }
                    output_by_state[q][o] = std::move(response);
                }
            }
        }

        for (std::size_t q = 0; q < automaton.states.size(); ++q) {
            const H::ExprPtr win_q = identifier(winning_names[q], H::Sort::boolean());
            const H::ExprPtr rank_q = identifier(rank_names[q], H::Sort::integer());
            addConstraint(impliesExpr(win_q,
                H::mkOp(H::Op::AND, {
                    H::mkOp(H::Op::LE, {H::mkInt(0), rank_q}),
                    H::mkOp(H::Op::LT, {rank_q,
                        H::mkInt(std::to_string(automaton.states.size()))})
                })));
            if (automaton.states[q].accepting) {
                addConstraint(impliesExpr(win_q,
                    H::mkOp(H::Op::EQ, {rank_q, H::mkInt(0)})));
                if (finite_word) { continue; }
            } else {
                addConstraint(impliesExpr(win_q,
                    H::mkOp(H::Op::GT, {rank_q, H::mkInt(0)})));
            }

            std::map<std::string, H::ExprPtr> atom_terms;
            for (std::size_t i = 0; i < inputs_.size(); ++i) {
                atom_terms.emplace(inputs_[i], input_terms[i]);
            }
            for (std::size_t o = 0; o < outputs_.size(); ++o) {
                atom_terms.emplace(outputs_[o], output_by_state[q][o]);
            }
            std::map<BddManager::Id, H::ExprPtr> bdd_cache;
            std::vector<H::ExprPtr> moves;
            for (const auto& [target, condition] : automaton.edges[q]) {
                H::ExprPtr edge = bddExpression(condition, bdds, atom_terms, bdd_cache);
                H::ExprPtr winning_next = identifier(
                    winning_names[target], H::Sort::boolean());
                H::ExprPtr lower_rank = H::mkOp(H::Op::LT, {
                    identifier(rank_names[target], H::Sort::integer()), rank_q});
                H::ExprPtr next = std::move(winning_next);
                if (finite_word || !automaton.states[q].accepting) {
                    next = andExpr(std::move(next), std::move(lower_rank));
                }
                moves.push_back(andExpr(std::move(edge), std::move(next)));
            }
            H::ExprPtr some_move = H::mkBool(false);
            if (moves.size() == 1) {
                some_move = std::move(moves.front());
            } else if (!moves.empty()) {
                some_move = H::mkOp(H::Op::OR, std::move(moves));
            }
            H::ExprPtr progress = impliesExpr(win_q, std::move(some_move));
            if (!input_binders.empty()) {
                progress = H::mkForall(input_binders, std::move(progress));
            }
            addConstraint(std::move(progress));
        }

        Uir::EncodingChoice choice;
        choice.site = file_;
        choice.unified_op = "reactive-realizability";
        choice.strategy = finite_word ? "finite-ltlf-symbolic-dfa-reachability-game"
                                      : "infinite-one-step-safety-contract-buchi-game";
        choice.fidelity = Uir::Fidelity::exact();
        choice.rationale = finite_word ?
            "TLSF finite semantics is reduced to reachability in the complete "
            "progression DFA. A symbolic ROBDD partitions the letter alphabet; "
            "Mealy strategy arrays and Moore choices use the source move order, and a "
            "rank-decreasing witness bounded by the reachable DFA state count "
            "characterizes termination without a play horizon" :
            "The complete symbolic safety-monitor product preserves standard TLSF "
            "initial/preset obligations and whole-trace assumption implication. "
            "A Buchi strategy certificate closes every winning state and decreases "
            "rank only while the guarantee has failed without an assumption failure. "
            "Positional determinacy makes the reachable-monitor rank bound exact; "
            "Mealy responses observe current inputs, Moore responses do not. "
            "No play horizon or source-controller memory bound is selected";
        report.addChoice(std::move(choice));
        return model;
    }

    std::string valuationLabel(std::size_t value) const {
        std::string result;
        for (std::size_t i = 0; i < inputs_.size(); ++i) {
            if (i != 0) { result += ","; }
            result += inputs_[i] + "=" + (((value >> i) & 1U) ? "true" : "false");
        }
        return result;
    }

    bool hasUnavoidableInputInvariant() {
        // In a non-empty finite trace, an unconstrained environment controls its
        // first input letter. If the system guarantee propositionally entails
        // G(input), the environment can falsify that input at position zero and
        // defeat every controller before any future-eventuality obligations
        // need to be expanded into the exponentially large progression DFA.
        if (!finite_ || !initially_.empty() || !require_.empty()
            || !assumptions_.empty() || guarantees_.empty()) {
            return false;
        }
        FormulaPtr system = conjunction(guarantees_);
        for (const std::string& input : inputs_) {
            const FormulaPtr invariant = formulas_.make(
                Formula::GLOBALLY, formulas_.atom(input));
            if (formulas_.propositionallyImplies(system, invariant)) { return true; }
        }
        return false;
    }

    H::ConstraintModelPtr buildUnrealizableFinite(Uir::TranslationReport& report) {
        auto model = std::make_shared<H::ConstraintModel>();
        H::Constraint constraint;
        constraint.formula = H::mkBool(false);
        model->constraints.push_back(std::move(constraint));

        Uir::EncodingChoice choice;
        choice.site = file_;
        choice.unified_op = "reactive-realizability";
        choice.strategy = "finite-unavoidable-environment-invariant";
        choice.fidelity = Uir::Fidelity::exact();
        choice.rationale =
            "with no initial condition or environment restrictions, every finite "
            "play has a first position where the environment may choose any input. "
            "The system guarantee propositionally entails G(input), so choosing that "
            "input false at the first position defeats every strategy; an exact false "
            "constraint avoids materializing the full progression DFA";
        report.addChoice(std::move(choice));
        return model;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics&, Uir::TranslationReport& report) {
        if (hasUnavoidableInputInvariant()) {
            return buildUnrealizableFinite(report);
        }
        if (!finite_ && !invariant_fragment_) { return buildInfiniteSafetyGame(report); }
        if (!invariant_fragment_) { return buildFiniteGame(report); }
        auto model = std::make_shared<H::ConstraintModel>();
        std::string prefix = "__somt_syntcomp_";
        while (source_.find(prefix) != std::string::npos) { prefix += "x"; }
        std::set<std::string> declared;
        const std::size_t valuations = std::size_t{1} << inputs_.size();

        std::vector<std::map<std::string, std::string>> controller_by_valuation;
        for (std::size_t value = 0; value < valuations; ++value) {
            std::map<std::string, std::string> controller;
            for (std::size_t output = 0; output < outputs_.size(); ++output) {
                const std::size_t coordinate = semantics_ == "Mealy" ? value : 0;
                const std::string target = prefix + "output_" + std::to_string(output)
                                         + "_env_" + std::to_string(coordinate);
                controller.emplace(outputs_[output], target);
                if (declared.insert(target).second) {
                    H::VarDecl declaration;
                    declaration.name = target;
                    declaration.sort = H::Sort::boolean();
                    declaration.auxiliary = true;
                    model->decls.push_back(std::move(declaration));

                    const std::string source_name =
                        semantics_ == "Mealy"
                            ? "controller[" + outputs_[output] + "](" + valuationLabel(value)
                                  + ")"
                            : "controller[" + outputs_[output] + "]";
                    projection_.observables.push_back(
                        {source_name, target, S::ProjectionKind::DIRECT});
                    source_signature_.symbols.push_back(
                        {source_name, S::SymbolKind::CONSTANT, {}, H::Sort::boolean()});
                    symbol_map_.push_back({source_name, target});
                }
            }
            controller_by_valuation.push_back(std::move(controller));
        }

        for (std::size_t value = 0; value < valuations; ++value) {
            std::map<std::string, bool> environment;
            for (std::size_t i = 0; i < inputs_.size(); ++i) {
                environment.emplace(inputs_[i], ((value >> i) & 1U) != 0);
            }
            std::vector<H::ExprPtr> assumptions;
            for (const FormulaPtr& formula : assumptions_) {
                assumptions.push_back(expression(formula, environment,
                                                 controller_by_valuation[value]));
            }
            std::vector<H::ExprPtr> guarantees;
            for (const FormulaPtr& formula : guarantees_) {
                guarantees.push_back(expression(formula, environment,
                                                controller_by_valuation[value]));
            }
            H::Constraint constraint;
            constraint.formula = H::mkOp(
                H::Op::IMPLIES,
                {conjunction(std::move(assumptions)),
                 conjunction(std::move(guarantees))});
            model->constraints.push_back(std::move(constraint));
        }

        Uir::EncodingChoice choice;
        choice.site = file_;
        choice.unified_op = "reactive-realizability";
        choice.strategy = semantics_ == "Mealy"
                              ? "complete-mealy-invariant-truth-table"
                              : "complete-moore-invariant-truth-table";
        choice.fidelity = Uir::Fidelity::exact();
        choice.rationale =
            "every Boolean environment valuation is expanded and the complete "
            + semantics_
            + " response table is existentially represented; for stateless G(phi) "
              "games this strategy space is complete, so both SAT and UNSAT preserve "
              "global reactive realizability without a play-horizon bound";
        report.addChoice(std::move(choice));
        return model;
    }

    std::string source_;
    std::string file_;
    FormulaFactory formulas_;
    std::vector<Token> tokens_;
    std::size_t at_ = 0;
    std::string semantics_;
    std::string target_;
    bool finite_ = false;
    bool invariant_fragment_ = false;
    std::vector<std::string> inputs_;
    std::vector<std::string> outputs_;
    std::set<std::string> signals_;
    std::vector<std::vector<Token>> assumption_tokens_;
    std::vector<std::vector<Token>> guarantee_tokens_;
    std::vector<std::vector<Token>> initially_tokens_;
    std::vector<std::vector<Token>> preset_tokens_;
    std::vector<std::vector<Token>> require_tokens_;
    std::vector<std::vector<Token>> assert_tokens_;
    std::vector<FormulaPtr> initially_;
    std::vector<FormulaPtr> preset_;
    std::vector<FormulaPtr> require_;
    std::vector<FormulaPtr> assert_;
    std::vector<FormulaPtr> assumptions_;
    std::vector<FormulaPtr> guarantees_;
    S::ModelProjection projection_;
    S::Signature source_signature_;
    std::vector<S::SymbolMapping> symbol_map_;
};

class SyntcompLanguage : public Language {
public:
    SyntcompLanguage() {
        coverage_.total = 3;
        coverage_.supported = 1;
        coverage_.missing = {
            "general infinite-word TLSF LTL synthesis and extended GLOBAL/functions/buses",
            "extended AIGER safety and HOA parity-game controller synthesis",
        };
    }

    std::string id() const override { return "syntcomp"; }
    std::string displayName() const override {
        return "SYNTCOMP (exact finite LTL and infinite one-step safety games)";
    }
    std::string version() const override { return "TLSF 1.2 finite-LTL and one-step safety subsets"; }
    std::vector<std::string> extensions() const override { return {".tlsf"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    double sniff(std::string_view head) const override {
        return head.find("INFO {") != std::string_view::npos
                   || head.find("ASSUME") != std::string_view::npos
                   || head.find("GUARANTEE") != std::string_view::npos
               ? 0.9 : 0.0;
    }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions&) override {
        ParseOutcome result;
        std::string source = unit.inline_source;
        if (source.empty()) {
            std::error_code error;
            if (std::filesystem::is_directory(unit.main_path, error)) {
                result.diagnostics.error(ErrorCode::E_IO,
                                         "'" + unit.main_path + "' is a directory");
                return result;
            }
            std::ifstream input(unit.main_path, std::ios::binary);
            if (!input) {
                result.diagnostics.error(ErrorCode::E_IO,
                                         "cannot open '" + unit.main_path + "'");
                return result;
            }
            std::ostringstream buffer;
            buffer << input.rdbuf();
            source = buffer.str();
        }
        if (source.find("INFO") == std::string::npos
            && source.find("GUARANTEE") == std::string::npos) {
            result.diagnostics.error(ErrorCode::E_PARSE,
                                     "no INFO or GUARANTEE section: this is not a TLSF file");
            return result;
        }
        const std::string name = unit.main_path.empty() ? unit.display_name
                                                         : unit.main_path;
        try {
            TlsfParser parser(source, name);
            result.model = parser.parse(result.diagnostics, result.report);
            if (result.model) {
                result.semantics.add(S::syntcompToRelationalContract(
                    *result.model, result.report.fidelity(), parser.projection(),
                    parser.sourceSignature(), parser.symbolMap()));
            }
        } catch (const std::bad_alloc&) {
            result.model.reset();
            result.diagnostics.error(ErrorCode::E_RESOURCE,
                                     "TLSF automaton construction exhausted memory");
        } catch (const std::exception& error) {
            result.model.reset();
            result.diagnostics.error(ErrorCode::E_INTERNAL,
                                     std::string("syntcomp frontend: ") + error.what());
        }
        return result;
    }

private:
    OpCoverage coverage_;
};
#endif // SOMT_LTLF_CORE_TEST_ONLY

} // namespace

#ifndef SOMT_LTLF_CORE_TEST_ONLY
LanguagePtr mkSyntcompLanguage() { return std::make_shared<SyntcompLanguage>(); }
#endif

} // namespace SOMTParser::Lang
