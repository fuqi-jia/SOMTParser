#include "somtparser/lowering/optimathsat_array_lowering.h"
#include "somtparser/frontend/parser.h"

#include <algorithm>
#include <cctype>
#include <stdexcept>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace SOMTParser::Lower {
namespace {

using Id = std::size_t;
constexpr Id OTHER = 0;
constexpr Id BOOLEAN = 1;

// Flat arenas avoid both recursive traversal and recursive destruction.
struct Node {
    std::string_view atom;
    std::vector<Id> children;
    bool list = false;
    bool quoted = false;
    bool literal = false;
    Id type = OTHER;
    std::string prefix, suffix, replacement;
};
struct Type { bool array = false; Id index = OTHER, element = OTHER; };
struct Binding { Id type = OTHER; std::string emitted; };

class Rewriter {
public:
    explicit Rewriter(const std::string& input) : input_(input), types_(2) {
        parse();
        for (Id id = 0; id < nodes_.size(); ++id)
            if (!nodes_[id].list && !nodes_[id].literal) used_names_.insert(identity(id));
    }

    std::string run() {
        for (const auto root : roots_) command(root);
        if (!changed_) return input_;
        // BV1 was introduced into the original logic. ALL also preserves
        // mixed array/arithmetic inputs without guessing a narrower logic.
        for (const auto root : roots_) {
            const auto& children = nodes_[root].children;
            if (head(root, "set-logic") && children.size() == 2)
                nodes_[children[1]].replacement = "ALL";
        }
        return render();
    }

private:
    const std::string& input_;
    std::vector<Node> nodes_;
    std::vector<Id> roots_;
    std::vector<Type> types_;
    std::unordered_map<Id, Id> sort_types_;
    std::unordered_map<std::string, Id> aliases_;
    std::unordered_map<std::string, std::vector<Binding>> symbols_;
    std::unordered_set<std::string> used_names_;
    Id next_name_ = 0;
    std::vector<std::vector<std::string>> declaration_scopes_{1};
    bool changed_ = false;

    [[noreturn]] static void fail(const std::string& reason) {
        throw std::runtime_error("OptiMathSAT Boolean-array lowering: " + reason);
    }

    std::string identity(Id id) const {
        const auto& n = nodes_[id];
        if (n.quoted) return std::string(n.atom.substr(1, n.atom.size() - 2));
        return std::string(n.atom);
    }
    bool word(Id id, std::string_view text) const {
        const auto& n = nodes_[id];
        return !n.list && !n.literal && !n.quoted && n.atom == text;
    }
    bool head(Id id, std::string_view text) const {
        const auto& n = nodes_[id];
        return n.list && !n.children.empty() && word(n.children[0], text);
    }

    void parse() {
        std::vector<Id> pending;
        for (Id i = 0; i < input_.size();) {
            const auto c = static_cast<unsigned char>(input_[i]);
            if (std::isspace(c)) { ++i; continue; }
            if (input_[i] == ';') {
                while (i < input_.size() && input_[i] != '\n') ++i;
                continue;
            }
            if (input_[i] == ')') {
                if (pending.empty()) fail("unmatched closing parenthesis");
                pending.pop_back(); ++i; continue;
            }
            const Id id = nodes_.size();
            nodes_.emplace_back();
            if (pending.empty()) roots_.push_back(id);
            else nodes_[pending.back()].children.push_back(id);
            if (input_[i] == '(') {
                nodes_[id].list = true; pending.push_back(id); ++i; continue;
            }
            const auto begin = i;
            if (input_[i] == '|' || input_[i] == '"') {
                const char quote = input_[i++];
                nodes_[id].quoted = quote == '|';
                nodes_[id].literal = quote == '"';
                bool closed = false;
                while (i < input_.size()) {
                    if (input_[i++] != quote) continue;
                    if (quote == '"' && i < input_.size() && input_[i] == '"') {
                        ++i; continue;
                    }
                    closed = true; break;
                }
                if (!closed) fail("unterminated quoted atom");
            } else {
                while (i < input_.size() && !std::isspace(static_cast<unsigned char>(input_[i]))
                       && input_[i] != '(' && input_[i] != ')' && input_[i] != ';') ++i;
            }
            nodes_[id].atom = std::string_view(input_).substr(begin, i - begin);
            if (!nodes_[id].quoted && !nodes_[id].atom.empty()
                && (std::isdigit(static_cast<unsigned char>(nodes_[id].atom.front()))
                    || nodes_[id].atom.front() == '#')) nodes_[id].literal = true;
        }
        if (!pending.empty()) fail("unterminated list");
    }

    Id arrayType(Id index, Id element) {
        types_.push_back({true, index, element});
        return types_.size() - 1;
    }

    Id sort(Id root) {
        const auto cached = sort_types_.find(root);
        if (cached != sort_types_.end()) return cached->second;
        std::vector<std::pair<Id, bool>> pending{{root, false}};
        while (!pending.empty()) {
            const auto [id, done] = pending.back(); pending.pop_back();
            if (sort_types_.count(id)) continue;
            const auto& n = nodes_[id];
            if (head(id, "Array")) {
                if (n.children.size() != 3) fail("Array sort needs two arguments");
                if (!done) {
                    pending.push_back({id, true});
                    pending.push_back({n.children[2], false});
                    pending.push_back({n.children[1], false});
                    continue;
                }
                const auto index = sort_types_.at(n.children[1]);
                const auto element = sort_types_.at(n.children[2]);
                for (Id at = 1; at <= 2; ++at) {
                    if (sort_types_.at(n.children[at]) == BOOLEAN) {
                        nodes_[n.children[at]].replacement = "(_ BitVec 1)";
                        changed_ = true;
                    }
                }
                sort_types_[id] = arrayType(index, element);
            } else if (word(id, "Bool")) sort_types_[id] = BOOLEAN;
            else if (!n.list) {
                const auto alias = aliases_.find(identity(id));
                sort_types_[id] = alias == aliases_.end() ? OTHER : alias->second;
            } else sort_types_[id] = OTHER;
        }
        return sort_types_.at(root);
    }

    Id lookup(Id symbol) const {
        const auto found = symbols_.find(identity(symbol));
        return found == symbols_.end() || found->second.empty() ? OTHER : found->second.back().type;
    }
    void bind(Id symbol, Id type, bool declaration = false) {
        const auto name = identity(symbol);
        std::string emitted;
        if (!declaration) {
            // OptiMathSAT rejects a bound name that shadows a declaration or
            // an enclosing binder. Fresh names are chosen against EVERY source
            // symbol, not merely those visible at this position. The original
            // spelling remains the lookup key, so simultaneous let RHSs and
            // lexical shadowing keep their source meaning.
            do { emitted = "__somt_oms_bound_" + std::to_string(next_name_++); }
            while (!used_names_.insert(emitted).second);
            nodes_[symbol].replacement = emitted;
        }
        symbols_[name].push_back({type, std::move(emitted)});
        if (declaration) declaration_scopes_.back().push_back(name);
    }
    void unbind(const std::string& name) {
        auto found = symbols_.find(name);
        if (found == symbols_.end() || found->second.empty()) fail("unbalanced symbol scope");
        found->second.pop_back();
        if (found->second.empty()) symbols_.erase(found);
    }
    void encode(Id id) {
        auto& n = nodes_[id];
        if (word(id, "true") || word(id, "false")) {
            n.replacement = word(id, "true") ? "#b1" : "#b0";
            return;
        }
        n.prefix = "(ite " + n.prefix;
        n.suffix += " #b1 #b0)";
    }
    void decode(Id id) {
        auto& n = nodes_[id];
        n.prefix = "(= " + n.prefix;
        n.suffix += " #b1)";
    }

    void term(Id root) {
        enum class Action { ENTER, FINISH, BIND_LET, UNBIND, LET_RESULT, QUANTIFIER_RESULT };
        struct Work { Action action; Id id; };
        std::vector<Work> pending{{Action::ENTER, root}};
        while (!pending.empty()) {
            const auto work = pending.back(); pending.pop_back();
            const auto id = work.id;
            auto& n = nodes_[id];
            const auto& ch = n.children;
            if (work.action == Action::UNBIND) {
                for (auto it = ch.rbegin(); it != ch.rend(); ++it) {
                    const auto& binding = nodes_[*it].children;
                    if (binding.size() != 2) fail("invalid binder");
                    unbind(identity(binding[0]));
                }
                continue;
            }
            if (work.action == Action::BIND_LET) {
                for (const auto binding_id : ch) {
                    const auto& binding = nodes_[binding_id].children;
                    bind(binding[0], nodes_[binding[1]].type);
                }
                continue;
            }
            if (work.action == Action::LET_RESULT) { n.type = nodes_[ch[2]].type; continue; }
            if (work.action == Action::QUANTIFIER_RESULT) { n.type = BOOLEAN; continue; }
            if (work.action == Action::ENTER) {
                if (!n.list) {
                    if (n.literal) { n.type = OTHER; continue; }
                    n.type = word(id, "true") || word(id, "false") ? BOOLEAN : lookup(id);
                    const auto found = symbols_.find(identity(id));
                    if (found != symbols_.end() && !found->second.empty()
                        && !found->second.back().emitted.empty())
                        n.replacement = found->second.back().emitted;
                    continue;
                }
                if (ch.empty()) continue;
                if (head(id, "let")) {
                    if (ch.size() != 3 || !nodes_[ch[1]].list) fail("invalid let");
                    // SMT-LIB let is simultaneous: bind names only after ALL
                    // right-hand sides were visited in the outer environment.
                    pending.push_back({Action::LET_RESULT, id});
                    pending.push_back({Action::UNBIND, ch[1]});
                    pending.push_back({Action::ENTER, ch[2]});
                    pending.push_back({Action::BIND_LET, ch[1]});
                    for (auto it = nodes_[ch[1]].children.rbegin(); it != nodes_[ch[1]].children.rend(); ++it) {
                        const auto& binding = nodes_[*it].children;
                        if (binding.size() != 2) fail("invalid let binding");
                        pending.push_back({Action::ENTER, binding[1]});
                    }
                    continue;
                }
                if (head(id, "forall") || head(id, "exists")) {
                    if (ch.size() != 3 || !nodes_[ch[1]].list) fail("invalid quantifier");
                    for (const auto binding_id : nodes_[ch[1]].children) {
                        const auto& binding = nodes_[binding_id].children;
                        if (binding.size() != 2) fail("invalid quantified binder");
                        bind(binding[0], sort(binding[1]));
                    }
                    pending.push_back({Action::QUANTIFIER_RESULT, id});
                    pending.push_back({Action::UNBIND, ch[1]});
                    pending.push_back({Action::ENTER, ch[2]});
                    continue;
                }
                if (head(ch[0], "as")) {
                    const auto& qualified = nodes_[ch[0]].children;
                    if (qualified.size() != 3) fail("invalid qualified identifier");
                    n.type = sort(qualified[2]);
                } else if (head(id, "as")) {
                    if (ch.size() != 3) fail("invalid sort annotation");
                    n.type = sort(ch[2]); continue;
                }
                pending.push_back({Action::FINISH, id});
                // Annotation values and indexed operator parameters are syntax,
                // not argument terms. Never look up :named identifiers as vars.
                const auto count = head(id, "!") ? std::min<Id>(ch.size(), 2) : ch.size();
                for (Id at = count; at > 1; --at)
                    pending.push_back({Action::ENTER, ch[at - 1]});
                continue;
            }
            if (ch.empty()) continue;
            if (head(id, "select")) {
                if (ch.size() != 3) fail("select needs two arguments");
                const auto type = nodes_[ch[1]].type;
                if (!types_[type].array) fail("cannot determine select's array sort");
                const auto array = types_[type];
                if (array.index == BOOLEAN) encode(ch[2]);
                n.type = array.element;
                if (n.type == BOOLEAN) decode(id);
            } else if (head(id, "store")) {
                if (ch.size() != 4) fail("store needs three arguments");
                const auto type = nodes_[ch[1]].type;
                if (!types_[type].array) fail("cannot determine store's array sort");
                const auto array = types_[type];
                if (array.index == BOOLEAN) encode(ch[2]);
                if (array.element == BOOLEAN) encode(ch[3]);
                n.type = type;
            } else if (head(ch[0], "as") && word(nodes_[ch[0]].children[1], "const")) {
                if (ch.size() != 2 || !types_[n.type].array) fail("invalid constant array");
                if (types_[n.type].element == BOOLEAN) encode(ch[1]);
            } else if (head(id, "ite")) {
                if (ch.size() != 4) fail("ite needs three arguments");
                n.type = nodes_[ch[2]].type;
            } else if (head(id, "!")) {
                if (ch.size() < 2) fail("invalid annotated term");
                n.type = nodes_[ch[1]].type;
            } else if (head(ch[0], "_")) {
                const auto& indexed = nodes_[ch[0]].children;
                if (indexed.size() >= 2 && word(indexed[1], "map"))
                    fail("array map requires finite-domain lowering before OptiMathSAT export");
            } else {
                n.type = lookup(ch[0]);
                if (head(id, "=") || head(id, "distinct") || head(id, "and") || head(id, "or")
                    || head(id, "not") || head(id, "xor") || head(id, "=>") || head(id, "<")
                    || head(id, "<=") || head(id, ">") || head(id, ">=")) n.type = BOOLEAN;
            }
        }
    }

    void definition(Id name, Id bindings, Id result, Id body) {
        bind(name, sort(result), true);
        for (const auto b : nodes_[bindings].children) {
            const auto& binding = nodes_[b].children;
            if (binding.size() != 2) fail("invalid function parameter");
            bind(binding[0], sort(binding[1]));
        }
        term(body);
        for (auto it = nodes_[bindings].children.rbegin(); it != nodes_[bindings].children.rend(); ++it)
            unbind(identity(nodes_[*it].children[0]));
    }

    void command(Id root) {
        const auto& ch = nodes_[root].children;
        if (!nodes_[root].list || ch.empty()) fail("expected command");
        if (head(root, "declare-const")) {
            if (ch.size() != 3) fail("invalid declare-const");
            bind(ch[1], sort(ch[2]), true);
        } else if (head(root, "declare-fun")) {
            if (ch.size() != 4) fail("invalid declare-fun");
            for (const auto arg : nodes_[ch[2]].children) (void)sort(arg);
            bind(ch[1], sort(ch[3]), true);
        } else if (head(root, "define-fun") || head(root, "define-fun-rec")) {
            if (ch.size() != 5) fail("invalid function definition");
            if (head(root, "define-fun-rec")) {
                // HIR retains large acyclic macros as recursive definitions to
                // prevent eager expansion. OMS only accepts ordinary macros.
                // Conservatively reject any occurrence of the defined name;
                // never erase a real recursive dependency or unroll it finitely.
                std::vector<Id> pending{ch[4]};
                const auto name = identity(ch[1]);
                while (!pending.empty()) {
                    const auto id = pending.back(); pending.pop_back();
                    const auto& node = nodes_[id];
                    if (!node.list && !node.literal && identity(id) == name)
                        fail("recursive function '" + name + "' requires a supported recursive backend");
                    for (const auto child : node.children) pending.push_back(child);
                }
                nodes_[ch[0]].replacement = "define-fun";
                changed_ = true;
            }
            definition(ch[1], ch[2], ch[3], ch[4]);
        } else if (head(root, "define-sort")) {
            if (ch.size() != 4 || !nodes_[ch[2]].children.empty())
                fail("parameterized sort aliases must be resolved before export");
            aliases_[identity(ch[1])] = sort(ch[3]);
        } else if (head(root, "get-value") || head(root, "check-sat-assuming")) {
            if (ch.size() != 2) fail("invalid term-list query");
            for (const auto arg : nodes_[ch[1]].children) term(arg);
        } else if (head(root, "assert") || head(root, "assert-soft")
                   || head(root, "minimize") || head(root, "maximize")) {
            if (ch.size() < 2) fail("missing constraint or objective");
            term(ch[1]);
        } else if (head(root, "push") || head(root, "pop")) {
            if (ch.size() != 2) fail("invalid scope command");
            const auto count = std::stoull(identity(ch[1]));
            for (unsigned long long i = 0; i < count; ++i) {
                if (head(root, "push")) declaration_scopes_.emplace_back();
                else {
                    if (declaration_scopes_.size() == 1) fail("pop underflow");
                    for (auto it = declaration_scopes_.back().rbegin(); it != declaration_scopes_.back().rend(); ++it)
                        unbind(*it);
                    declaration_scopes_.pop_back();
                }
            }
        } else if (head(root, "reset")) {
            symbols_.clear(); aliases_.clear(); declaration_scopes_.assign(1, {});
        } else if (head(root, "declare-datatype") || head(root, "declare-datatypes")
                   || head(root, "define-funs-rec")) {
            fail("datatype and mutually recursive declarations require prior lowering");
        }
    }

    std::string render() const {
        struct Work { Id id; bool close; bool space = false; };
        std::string output;
        output.reserve(input_.size());
        for (const auto root : roots_) {
            std::vector<Work> pending{{root, false}};
            while (!pending.empty()) {
                const auto [id, close, space] = pending.back(); pending.pop_back();
                const auto& n = nodes_[id];
                if (space) output += ' ';
                if (close) {
                    if (n.list) output += ')';
                    output += n.suffix;
                    continue;
                }
                output += n.prefix;
                if (!n.replacement.empty()) { output += n.replacement; output += n.suffix; continue; }
                if (!n.list) { output.append(n.atom); output += n.suffix; continue; }
                output += '(';
                pending.push_back({id, true});
                for (Id i = n.children.size(); i > 0; --i)
                    pending.push_back({n.children[i - 1], false, i > 1});
            }
            output += '\n';
        }
        return output;
    }
};
} // namespace

bool needsOptiMathSatArrayLowering(const Parser& parser) {
    const auto manager = parser.getSortManager();
    for (Id i = 0; i < manager->size(); ++i) {
        const auto sort = manager->getSort(i);
        if (sort && sort->isArray() && (sort->getIndexSort()->isBool() || sort->getElemSort()->isBool()))
            return true;
    }
    return false;
}

bool needsOptiMathSatDefinitionLowering(const Parser& parser) {
    for (const auto& function : parser.getFunctions())
        if (function && function->isFuncRec()) return true;
    return false;
}

bool needsOptiMathSatSetLowering(const Parser& parser) {
    const auto manager = parser.getSortManager();
    for (Id i = 0; i < manager->size(); ++i) {
        const auto sort = manager->getSort(i);
        if (sort && sort->isSet()) return true;
    }
    return false;
}

std::string lowerBooleanArraysForOptiMathSat(const std::string& smt2) {
    return Rewriter(smt2).run();
}
} // namespace SOMTParser::Lower
