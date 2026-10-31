/* -*- Source -*-
 * QCIR-G14 frontend.
 *
 * The format is docs/languages/qcir.md; that document was written from the
 * standard before any of this existed, and its `implicit-constraints` block is
 * the specification this file implements. Each obligation is marked below with
 * the section it comes from, and each has a fixture in
 * languages/qcir/instances.
 *
 * QCIR leaves unquantified non-gate variables free. QDIMACS instead binds
 * unquantified matrix variables existentially at the outermost level. Both
 * accept such inputs, but their HIR binding structures differ.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/qcir.h"

#include <algorithm>
#include <cctype>
#include <filesystem>
#include <fstream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

/** A literal: a variable or gate name, possibly negated. */
struct Lit {
    std::string name;
    bool        negated = false;
};

struct Gate {
    std::string      name;
    std::string      type;        // and, or, xor, ite, exists, forall
    std::vector<Lit> inputs;
    std::vector<std::string> bound;   // quantifier gates only
    int              line = 0;
};

/** A prefix quantifier block, in file order. */
struct Block {
    bool                     forall = false;
    std::vector<std::string> vars;
    int                      line = 0;
};

struct GateScope {
    std::size_t gate;
    std::size_t scope;
    bool operator==(const GateScope& other) const {
        return gate == other.gate && scope == other.scope;
    }
};

struct GateScopeHash {
    std::size_t operator()(const GateScope& key) const {
        return key.gate ^ (key.scope + 0x9e3779b9U + (key.gate << 6)
                           + (key.gate >> 2));
    }
};

std::string lower(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return s;
}

class QcirParser {
public:
    QcirParser(std::string src, std::string file, bool allowMissingHeader)
        : src_(std::move(src)), file_(std::move(file)),
          allow_missing_header_(allowMissingHeader) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags) {
        if (!tokenize(diags)) { return nullptr; }
        if (!readHeader(diags)) { return nullptr; }
        if (!readBody(diags)) { return nullptr; }
        return build(diags);
    }

private:
    // ---- source handling -------------------------------------------------

    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = line;
        l.column = 1;
        return l;
    }

    /** Split into logical lines, dropping comments.
     *
     *  §2.1: any line beginning with `#` is a comment -- *including*, as a
     *  matter of syntax, the format-id line, which is why line 1 is taken
     *  before this runs rather than skipped with the rest. Whitespace is free,
     *  so a statement may be spread over several physical lines; they are
     *  joined on the parenthesis balance. */
    bool tokenize(Uir::Diagnostics& diags) {
        std::istringstream in(src_);
        std::string raw;
        int lineno = 0;
        std::string pending;
        int pending_line = 0;
        int depth = 0;
        while (std::getline(in, raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            std::string trimmed = raw;
            trimmed.erase(0, trimmed.find_first_not_of(" \t"));
            if (lineno == 1) {
                first_line_ = trimmed;
                // Do not discard a quantifier/output on the first line of
                // an explicitly admitted headerless competition input.
                if (!allow_missing_header_ || trimmed.rfind("#", 0) == 0) {
                    continue;
                }
            }
            if (!trimmed.empty() && trimmed[0] == '#') { continue; }
            if (trimmed.find_first_not_of(" \t") == std::string::npos) { continue; }
            if (pending.empty()) { pending_line = lineno; }
            pending += trimmed;
            for (char c : trimmed) {
                if (c == '(') { ++depth; }
                else if (c == ')') { --depth; }
            }
            if (depth <= 0) {
                lines_.push_back({pending, pending_line});
                pending.clear();
                depth = 0;
            }
        }
        if (!pending.empty()) {
            diags.error(ErrorCode::E_PARSE, "unbalanced parentheses at end of file",
                        at(pending_line));
            return false;
        }
        return true;
    }

    /** §4.5: `#QCIR-G14` or `#QCIR-G14 n`, where n is a *checkable claim* --
     *  the file says it is cleansed and uses integer names <= n. */
    bool readHeader(Uir::Diagnostics& diags) {
        if (first_line_.rfind("#QCIR-G14", 0) != 0
            && first_line_.rfind("#qcir-g14", 0) != 0) {
            if (allow_missing_header_ && lower(first_line_).rfind("#qcir", 0) != 0) {
                diags.warn(ErrorCode::E_PARSE,
                           "missing QCIR-G14 format identifier; interpreting the body as "
                           "general QCIR because allow_missing_header is enabled", at(1));
                return true;
            }
            diags.error(ErrorCode::E_PARSE,
                        "first line is not a QCIR-G14 format identifier", at(1));
            return false;
        }
        std::string rest = first_line_.substr(9);
        if (!rest.empty() && rest.front() != ' ' && rest.front() != '\t') {
            diags.error(ErrorCode::E_PARSE, "invalid QCIR-G14 format identifier", at(1));
            return false;
        }
        rest = trim(rest);
        if (!rest.empty()) {
            try {
                if (rest.find_first_not_of("0123456789") != std::string::npos) {
                    throw std::invalid_argument("invalid count");
                }
                declared_vars_ = std::stoul(rest);
                cleansed_ = true;
            } catch (const std::exception&) {
                diags.error(ErrorCode::E_PARSE,
                            "the format identifier's variable count is not a number",
                            at(1));
                return false;
            }
        }
        return true;
    }

    // ---- statements -------------------------------------------------------

    static bool split(const std::string& line, std::string& head, std::string& body) {
        const std::size_t lp = line.find('(');
        if (lp == std::string::npos || line.back() != ')') { return false; }
        head = lower(line.substr(0, lp));
        head.erase(std::remove_if(head.begin(), head.end(),
                                  [](unsigned char c) { return std::isspace(c); }),
                   head.end());
        body = line.substr(lp + 1, line.size() - lp - 2);
        return true;
    }

    static std::vector<std::string> commas(const std::string& s) {
        std::vector<std::string> out;
        std::string cur;
        for (char c : s) {
            if (c == ',') { out.push_back(trim(cur)); cur.clear(); }
            else { cur += c; }
        }
        if (!trim(cur).empty() || !out.empty()) { out.push_back(trim(cur)); }
        if (out.size() == 1 && out[0].empty()) { out.clear(); }
        return out;
    }

    static std::string trim(std::string s) {
        const std::size_t a = s.find_first_not_of(" \t");
        if (a == std::string::npos) { return ""; }
        const std::size_t b = s.find_last_not_of(" \t");
        return s.substr(a, b - a + 1);
    }

    static Lit toLit(const std::string& s) {
        Lit l;
        if (!s.empty() && s[0] == '-') { l.negated = true; l.name = s.substr(1); }
        else { l.name = s; }
        return l;
    }

    bool readBody(Uir::Diagnostics& diags) {
        for (const auto& [text, line] : lines_) {
            std::string head, body;
            if (!split(text, head, body)) {
                diags.error(ErrorCode::E_PARSE, "expected `name(...)`", at(line));
                return false;
            }
            if (head == "free" || head == "exists" || head == "forall") {
                if (!output_.name.empty() || !gates_.empty()) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + head + "' must appear before the output statement",
                                at(line));
                    return false;
                }
                if (head == "free") {
                    for (const auto& v : commas(body)) { free_.push_back(v); }
                } else {
                    blocks_.push_back({head == "forall", commas(body), line});
                }
                continue;
            }
            if (head == "output") {
                const auto lits = commas(body);
                if (lits.size() != 1) {
                    diags.error(ErrorCode::E_PARSE, "output takes one literal", at(line));
                    return false;
                }
                if (!output_.name.empty()) {
                    diags.error(ErrorCode::E_PARSE, "more than one output statement",
                                at(line));
                    return false;
                }
                output_ = toLit(lits[0]);
                output_line_ = line;
                continue;
            }
            // A gate statement: `gvar = type(...)`.
            const std::size_t eq = text.find('=');
            if (eq == std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "expected a gate definition", at(line));
                return false;
            }
            Gate g;
            g.line = line;
            g.name = trim(text.substr(0, eq));
            std::string rhs = trim(text.substr(eq + 1));
            std::string gtype, gbody;
            if (!split(rhs, gtype, gbody)) {
                diags.error(ErrorCode::E_PARSE, "expected `type(...)`", at(line));
                return false;
            }
            g.type = gtype;
            const std::size_t semi = gbody.find(';');
            if (g.type == "exists" || g.type == "forall") {
                if (semi == std::string::npos) {
                    diags.error(ErrorCode::E_PARSE,
                                "a quantifier gate is `" + g.type
                                    + "(vars; literal)`", at(line));
                    return false;
                }
                g.bound = commas(gbody.substr(0, semi));
                const auto rest = commas(gbody.substr(semi + 1));
                if (rest.size() != 1) {
                    diags.error(ErrorCode::E_PARSE,
                                "a quantifier gate binds one subformula", at(line));
                    return false;
                }
                g.inputs.push_back(toLit(rest[0]));
            } else {
                for (const auto& s : commas(gbody)) { g.inputs.push_back(toLit(s)); }
            }
            // §4.4: a gate variable occurs exactly once on the left of `=`, and
            // gate and input variables are disjoint namespaces. Keeping them in
            // one table lets a redefinition pass as a constraint.
            if (gate_index_.count(g.name) != 0) {
                diags.error(ErrorCode::E_PARSE,
                            "gate '" + g.name + "' is defined more than once", at(line));
                return false;
            }
            gate_index_[g.name] = gates_.size();
            gates_.push_back(std::move(g));
        }
        if (output_.name.empty()) {
            diags.error(ErrorCode::E_PARSE, "the file has no output statement", at(1));
            return false;
        }
        return true;
    }

    // ---- model construction ----------------------------------------------

    H::ConstraintModelPtr build(Uir::Diagnostics& diags) {
        auto model = std::make_shared<H::ConstraintModel>();

        // Reserve every source name, including names in unreachable gates.
        // Alpha-renaming must not capture a free variable discovered later.
        reserved_names_.insert(output_.name);
        for (const auto& v : free_) { reserved_names_.insert(v); }
        for (const auto& b : blocks_) {
            reserved_names_.insert(b.vars.begin(), b.vars.end());
        }
        for (const auto& g : gates_) {
            reserved_names_.insert(g.name);
            reserved_names_.insert(g.bound.begin(), g.bound.end());
            for (const auto& in : g.inputs) { reserved_names_.insert(in.name); }
        }
        if (cleansed_ && !checkCleansedBindings(diags)) { return nullptr; }

        // Prefix and free block, in file order.
        std::unordered_set<std::string> quantified;
        std::vector<std::vector<H::Binder>> prefixBinders;
        for (const auto& v : free_) {
            if (!declare(*model, v, diags, at(1))) { return nullptr; }
        }
        for (const auto& b : blocks_) {
            std::vector<H::Binder> binders;
            for (const auto& v : b.vars) {
                if (gate_index_.count(v) != 0) {
                    // §4.4: a gate variable may not be quantified.
                    diags.error(ErrorCode::E_PARSE,
                                "'" + v + "' is a gate and cannot be quantified",
                                at(b.line));
                    return nullptr;
                }
                if (!quantified.insert(v).second && cleansed_) {
                    diags.error(ErrorCode::E_PARSE,
                                "variable '" + v + "' is quantified more than once",
                                at(b.line));
                    return nullptr;
                }
                const auto renamed = freshBinder();
                bindings_[v] = renamed;
                binders.push_back(H::Binder{renamed, H::Sort::boolean()});
            }
            prefixBinders.push_back(std::move(binders));
        }
        for (const auto& v : free_) {
            if (cleansed_ && quantified.count(v) != 0) {
                diags.error(ErrorCode::E_PARSE,
                            "'" + v + "' is both free and quantified", at(1));
                return nullptr;
            }
        }

        // The body, rooted at the output. §4.3: gates unreachable from the
        // output are IGNORED by the semantics, so the traversal starts here and
        // not at the gate list -- emitting every definition would add
        // constraints the formula does not have and change the reported size.
        H::ExprPtr body = lit(output_, diags, *model);
        if (!body) { return nullptr; }

        // The prefix scopes over the whole body, innermost block first.
        for (std::size_t i = blocks_.size(); i-- > 0;) {
            const auto& b = blocks_[i];
            const auto& binders = prefixBinders[i];
            if (binders.empty()) { continue; }
            body = b.forall ? H::mkForall(binders, body, at(b.line))
                            : H::mkExists(binders, body, at(b.line));
        }

        H::Constraint c;
        c.loc = at(output_line_);
        c.formula = body;
        model->constraints.push_back(c);

        // §4.5: the declared count is a claim about the file, and checking it is
        // four lines. A mismatch means the producer and the consumer disagree
        // about which dialect this is.
        if (cleansed_) {
            const std::size_t used = declared_names_.size() + gates_.size();
            if (used > declared_vars_) {
                diags.warn(ErrorCode::E_PARSE, "the format identifier declares "
                                  + std::to_string(declared_vars_)
                                  + " variables but the file uses "
                                  + std::to_string(used),
                              at(1));
            }
        }
        return model;
    }

    std::string freshBinder() {
        std::string name;
        do {
            name = "__qcir_bound_" + std::to_string(next_binder_++);
        } while (!reserved_names_.insert(name).second);
        return name;
    }

    bool checkCleansedBindings(Uir::Diagnostics& diags) {
        auto add = [&](const std::string& name, int line) {
            if (cleansed_quantified_.insert(name).second) { return true; }
            diags.error(ErrorCode::E_PARSE,
                        "variable '" + name + "' is quantified more than once "
                        "in a cleansed formula", at(line));
            return false;
        };
        for (const auto& b : blocks_) {
            for (const auto& v : b.vars) {
                if (!add(v, b.line)) { return false; }
            }
        }
        // Count source binders once per reachable gate, independently of the
        // number of paths that later expand it. Dead gates have no semantics.
        std::vector<std::size_t> pending;
        const auto root = gate_index_.find(output_.name);
        if (root != gate_index_.end()) { pending.push_back(root->second); }
        std::unordered_set<std::size_t> seen;
        while (!pending.empty()) {
            const auto index = pending.back();
            pending.pop_back();
            if (!seen.insert(index).second) { continue; }
            const auto& g = gates_[index];
            for (const auto& v : g.bound) {
                if (!add(v, g.line)) { return false; }
            }
            for (const auto& in : g.inputs) {
                const auto child = gate_index_.find(in.name);
                if (child != gate_index_.end()) { pending.push_back(child->second); }
            }
        }
        return true;
    }

    bool declare(H::ConstraintModel& model, const std::string& name,
                 Uir::Diagnostics& diags, const Uir::SourceLoc& loc) {
        if (cleansed_ && cleansed_quantified_.count(name) != 0) {
            diags.error(ErrorCode::E_PARSE,
                        "'" + name + "' is both free and quantified in a cleansed formula",
                        loc);
            return false;
        }
        if (gate_index_.count(name) != 0) {
            diags.error(ErrorCode::E_PARSE,
                        "'" + name + "' is a gate and cannot also be a variable", loc);
            return false;
        }
        if (!declared_names_.insert(name).second) { return true; }
        H::VarDecl d;
        d.name = name;
        d.sort = H::Sort::boolean();
        d.loc = loc;
        model.decls.push_back(d);
        return true;
    }

    /** Resolve a literal: a gate reference, a bound variable, or a free one. */
    H::ExprPtr lit(const Lit& l, Uir::Diagnostics& diags, H::ConstraintModel& model) {
        H::ExprPtr e = named(l.name, diags, model);
        if (!e) { return nullptr; }
        return l.negated ? H::mkOp(H::Op::NOT, {e}) : e;
    }

    H::ExprPtr named(const std::string& name, Uir::Diagnostics& diags,
                     H::ConstraintModel& model) {
        const auto g = gate_index_.find(name);
        if (g != gate_index_.end()) { return gate(g->second, diags, model); }
        const auto binding = bindings_.find(name);
        if (binding != bindings_.end()) {
            return H::mkBoundVar(binding->second, H::Sort::boolean());
        }
        // QCIR keeps unquantified non-gate variables free. QDIMACS instead
        // represents its implicit outer existential closure with bound vars.
        if (!declare(model, name, diags, at(1))) { return nullptr; }
        return H::mkIdent(name, H::Sort::boolean());
    }

    H::ExprPtr gate(std::size_t index, Uir::Diagnostics& diags,
                    H::ConstraintModel& model) {
        // §4.4: gates must be defined before use, which makes the circuit
        // acyclic by construction -- for *conforming* files. A frontend meets
        // non-conforming ones, and an unchecked use-before-def turns this
        // bottom-up walk into unbounded recursion, so the cycle is detected
        // rather than assumed away.
        if (visiting_.count(index) != 0) {
            diags.error(ErrorCode::E_PARSE,
                        "gate '" + gates_[index].name + "' is defined in terms of "
                        "itself; QCIR requires a gate to be defined before it is used",
                        at(gates_[index].line));
            return nullptr;
        }
        const GateScope key{index, scope_epoch_};
        const auto memo = memo_.find(key);
        if (memo != memo_.end()) { return memo->second; }
        visiting_.insert(index);

        const Gate& g = gates_[index];
        H::ExprPtr result;
        if (g.type == "and" || g.type == "or") {
            std::vector<H::ExprPtr> args;
            for (const auto& in : g.inputs) {
                H::ExprPtr a = lit(in, diags, model);
                if (!a) { visiting_.erase(index); return nullptr; }
                args.push_back(std::move(a));
            }
            if (args.empty()) {
                // §4.2: an `and` gate with zero inputs is TRUE and an `or` gate
                // with zero inputs is FALSE. Both are legal -- lit-list derives
                // epsilon -- and mkOp throws on an empty argument list rather
                // than inventing an identity, which is why this is a branch and
                // not an accident.
                result = H::mkBool(g.type == "and", at(g.line));
            } else if (args.size() == 1) {
                result = args.front();
            } else {
                result = H::mkOp(g.type == "and" ? H::Op::AND : H::Op::OR,
                                 std::move(args), at(g.line));
            }
        } else if (g.type == "xor" || g.type == "ite") {
            const std::size_t want = (g.type == "xor") ? 2 : 3;
            if (g.inputs.size() != want) {
                diags.error(ErrorCode::E_PARSE,
                            "'" + g.type + "' takes " + std::to_string(want)
                                + " inputs, not " + std::to_string(g.inputs.size()),
                            at(g.line));
                visiting_.erase(index);
                return nullptr;
            }
            if (cleansed_) {
                // §4.5: a cleansed formula contains no xor and no ite gates at
                // all. The file said it was cleansed; believing the header over
                // the body would let a mislabelled file through silently.
                diags.error(ErrorCode::E_PARSE,
                            "'" + g.type + "' gates are not allowed in a cleansed "
                            "formula, which the format identifier declares this to be",
                            at(g.line));
                visiting_.erase(index);
                return nullptr;
            }
            std::vector<H::ExprPtr> args;
            for (const auto& in : g.inputs) {
                H::ExprPtr a = lit(in, diags, model);
                if (!a) { visiting_.erase(index); return nullptr; }
                args.push_back(std::move(a));
            }
            result = H::mkOp(g.type == "xor" ? H::Op::XOR : H::Op::ITE,
                             std::move(args), at(g.line));
        } else if (g.type == "exists" || g.type == "forall") {
            // §2.2: a quantifier gate binds its variables ONLY inside its
            // subformula, at whatever position in the circuit it occupies. This
            // is what "non-prenex" means concretely, and it is why scope is
            // determined by the path from the output rather than by the gate a
            // name appears in.
            std::vector<H::Binder> binders;
            for (const auto& v : g.bound) {
                if (gate_index_.count(v) != 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + v + "' is a gate and cannot be quantified",
                                at(g.line));
                    visiting_.erase(index);
                    return nullptr;
                }
            }
            std::vector<std::pair<std::string, std::string>> previous;
            for (const auto& v : g.bound) {
                const auto old = bindings_.find(v);
                previous.emplace_back(v, old == bindings_.end() ? "" : old->second);
                const auto renamed = freshBinder();
                bindings_[v] = renamed;
                binders.push_back(H::Binder{renamed, H::Sort::boolean()});
            }
            const auto outerScope = scope_epoch_;
            scope_epoch_ = ++next_scope_epoch_;
            H::ExprPtr inner = lit(g.inputs.front(), diags, model);
            scope_epoch_ = outerScope;
            // Reverse order also restores repeated names within one block.
            for (auto it = previous.rbegin(); it != previous.rend(); ++it) {
                if (it->second.empty()) { bindings_.erase(it->first); }
                else { bindings_[it->first] = it->second; }
            }
            if (!inner) { visiting_.erase(index); return nullptr; }
            result = g.type == "exists" ? H::mkExists(binders, inner, at(g.line))
                                        : H::mkForall(binders, inner, at(g.line));
        } else {
            diags.error(ErrorCode::E_PARSE, "unknown gate type '" + g.type + "'",
                        at(g.line));
            visiting_.erase(index);
            return nullptr;
        }
        visiting_.erase(index);
        // A gate can be reached with different bindings, including free versus
        // bound occurrences of the same source variable. Cache only within the
        // same lexical environment. Quantifier gates allocate fresh binders.
        if (g.type != "exists" && g.type != "forall") { memo_[key] = result; }
        return result;
    }

    std::string src_;
    std::string file_;
    std::string first_line_;
    bool allow_missing_header_ = false;
    std::vector<std::pair<std::string, int>> lines_;

    bool        cleansed_ = false;
    std::size_t declared_vars_ = 0;

    std::vector<std::string> free_;
    std::vector<Block>       blocks_;
    std::vector<Gate>        gates_;
    std::unordered_map<std::string, std::size_t> gate_index_;
    Lit  output_;
    int  output_line_ = 1;

    std::unordered_map<std::string, std::string> bindings_;
    std::unordered_set<std::string> reserved_names_;
    std::unordered_set<std::string> cleansed_quantified_;
    std::size_t next_binder_ = 0;
    std::size_t scope_epoch_ = 0;
    std::size_t next_scope_epoch_ = 0;
    std::unordered_set<std::string> declared_names_;
    std::unordered_map<GateScope, H::ExprPtr, GateScopeHash> memo_;
    std::unordered_set<std::size_t>              visiting_;
};

class QcirLanguage : public Language {
public:
    QcirLanguage() {
        // and, or, xor, ite, quantifier gates, the prefix, free, output -- the
        // whole grammar. There is no fragment of QCIR this refuses.
        coverage_.total = 8;
        coverage_.supported = 8;
    }

    std::string id() const override { return "qcir"; }
    std::string displayName() const override { return "QCIR-G14"; }
    std::string version() const override { return "G14"; }
    std::vector<std::string> extensions() const override { return {".qcir"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& options) override {
        ParseOutcome out;
        const auto compatibility = options.options.find("allow_missing_header");
        const bool allow_missing_header = compatibility != options.options.end()
            && (compatibility->second == "1" || compatibility->second == "true");
        if (compatibility != options.options.end() && !allow_missing_header
            && compatibility->second != "0" && compatibility->second != "false") {
            out.diagnostics.error(ErrorCode::E_PARSE,
                                  "allow_missing_header must be true, false, 1 or 0");
            return out;
        }
        std::string src = unit.inline_source;
        if (src.empty()) {
            std::error_code ec;
            if (std::filesystem::is_directory(unit.main_path, ec)) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "'" + unit.main_path + "' is a directory");
                return out;
            }
            std::ifstream in(unit.main_path, std::ios::binary);
            if (!in) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "cannot open '" + unit.main_path + "'");
                return out;
            }
            std::ostringstream ss;
            ss << in.rdbuf();
            src = ss.str();
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            QcirParser p(src, name, allow_missing_header);
            out.model = p.parse(out.diagnostics);
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "qcir", out.report.fidelity()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("qcir frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkQcirLanguage() { return std::make_shared<QcirLanguage>(); }

} // namespace SOMTParser::Lang
