/* -*- Source -*-
 * MoXI frontend — bounded model checking of a MoXI transition system.
 *
 * The format is docs/languages/moxi.md; its `implicit-constraints` block is the
 * specification this file implements, and each entry has a fixture in
 * languages/moxi/instances.
 *
 * MoXI is the reverse of VMT-LIB: it keeps SMT-LIB's TERM language and replaces
 * its commands. So the term parsing is reused -- the sections' formulas go
 * through the engine's parser and Lower::ParserToHir -- and the command grammar
 * is read here.
 *
 * The obligations that are wrong answers rather than missing features:
 *
 *   * **Several reachability conditions are several eventualities.** A query
 *     containing r1 and r2 means `eventually r1 AND eventually r2`; the two
 *     witnesses may occur at different steps. One OR across every condition
 *     answers the weaker "does any one occur?" question.
 *   * **`:current C` replaces the system's initial predicate.** It does not hold
 *     at every step. Treating it as an invariant can remove real traces.
 *   * **A property not named by a `:query` is not checked.** Translating every
 *     condition regardless produces queries the file did not ask for -- harmless
 *     if reported separately, misleading once aggregated. This one was written
 *     down in `moxi.md` §2.4 and not met for several commits, and no corpus
 *     could have shown it: meeting it and not meeting it produce the same output
 *     on a file that asks about all of its conditions.
 *   * **A `check-system` restates the interface under names of its own**, and
 *     `:input ((i ...))` against the system's `:input ((in ...))` IDENTIFIES the
 *     two positionally. One variable, not two joined by an equation -- the trap
 *     §4.2 records for a subsystem's argument list, one level up.
 *   * **A condition carries a name**: `:reachable (rch (= o #x0a))`, and a
 *     query selects conditions by those names. `:invariant` and keyword query
 *     references are not part of the published MoXI grammar.
 *   * **`n'` is the next-step copy of `n`**, and the primed name is not a
 *     variable of its own.
 *
 * `:subsys` is flattened by identifying each child's interface with parent
 * variables, conjoining the child's predicates, and assigning fresh names to
 * every instance's locals. Two instances sharing locals form a smaller system
 * that still answers, so instance freshness is a correctness condition.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/moxi.h"
#include "somtparser/translation/module.h"

#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/frontend/parser.h"

#include <cerrno>
#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <memory>
#include <limits>
#include <optional>
#include <sstream>
#include <string>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

/** The index just past the s-expression starting at @p open. */
std::size_t matchParen(const std::string& s, std::size_t open) {
    int depth = 0;
    bool in_string = false, in_bar = false;
    for (std::size_t i = open; i < s.size(); ++i) {
        const char c = s[i];
        if (in_string) {
            if (c == '"' && i + 1 < s.size() && s[i + 1] == '"') { ++i; continue; }
            if (c == '"') { in_string = false; }
            continue;
        }
        if (in_bar) { if (c == '|') { in_bar = false; } continue; }
        if (c == '"') { in_string = true; continue; }
        if (c == '|') { in_bar = true; continue; }
        if (c == ';') { while (i < s.size() && s[i] != '\n') { ++i; } continue; }
        if (c == '(') { ++depth; }
        else if (c == ')') {
            --depth;
            if (depth == 0) { return i + 1; }
        }
    }
    return std::string::npos;
}

std::string blankComments(std::string s) {
    bool in_string = false, in_bar = false;
    for (std::size_t i = 0; i < s.size(); ++i) {
        const char c = s[i];
        if (in_string) {
            if (c == '"' && i + 1 < s.size() && s[i + 1] == '"') { ++i; continue; }
            if (c == '"') { in_string = false; }
            continue;
        }
        if (in_bar) { if (c == '|') { in_bar = false; } continue; }
        if (c == '"') { in_string = true; continue; }
        if (c == '|') { in_bar = true; continue; }
        if (s[i] == ';') {
            while (i < s.size() && s[i] != '\n') { s[i] = ' '; ++i; }
        }
    }
    return s;
}

struct VarDeclText {
    std::string name, sort;
};

void skipSpace(const std::string& s, std::size_t& p, std::size_t stop) {
    while (p < stop && std::isspace(static_cast<unsigned char>(s[p]))) { ++p; }
}

std::size_t scanAtom(const std::string& s, std::size_t p, std::size_t stop) {
    if (p >= stop) { return std::string::npos; }
    if (s[p] == '|') {
        for (std::size_t i = p + 1; i < stop; ++i) {
            if (s[i] == '|') {
                // MoXI permits the prime convention immediately after a
                // quoted current-state symbol: |out value|'.
                return i + 1 < stop && s[i + 1] == '\'' ? i + 2 : i + 1;
            }
        }
        return std::string::npos;
    }
    if (s[p] == '"') {
        for (std::size_t i = p + 1; i < stop; ++i) {
            if (s[i] != '"') { continue; }
            if (i + 1 < stop && s[i + 1] == '"') { ++i; continue; }
            return i + 1;
        }
        return std::string::npos;
    }
    std::size_t i = p;
    while (i < stop && !std::isspace(static_cast<unsigned char>(s[i]))
           && s[i] != '(' && s[i] != ')') {
        ++i;
    }
    return i == p ? std::string::npos : i;
}

std::size_t scanExpr(const std::string& s, std::size_t p, std::size_t stop) {
    if (p >= stop) { return std::string::npos; }
    if (s[p] == '(') {
        const std::size_t end = matchParen(s, p);
        return end != std::string::npos && end <= stop ? end : std::string::npos;
    }
    return scanAtom(s, p, stop);
}

/** The top-level items inside one complete parenthesized expression. */
bool splitSExpr(const std::string& s, std::vector<std::string>& out) {
    std::size_t open = 0;
    skipSpace(s, open, s.size());
    if (open >= s.size() || s[open] != '(') { return false; }
    const std::size_t close = matchParen(s, open);
    if (close == std::string::npos) { return false; }
    std::size_t trailing = close;
    skipSpace(s, trailing, s.size());
    if (trailing != s.size()) { return false; }
    std::size_t p = open + 1;
    const std::size_t stop = close - 1;
    while (true) {
        skipSpace(s, p, stop);
        if (p == stop) { return true; }
        const std::size_t end = scanExpr(s, p, stop);
        if (end == std::string::npos) { return false; }
        out.push_back(s.substr(p, end - p));
        p = end;
    }
}

std::vector<std::string> sexprItems(const std::string& s) {
    std::vector<std::string> out;
    if (!splitSExpr(s, out)) { out.clear(); }
    return out;
}

bool isSimpleSymbol(const std::string& s) {
    if (s.empty()) { return false; }
    const auto initial = [](char c) {
        return std::isalpha(static_cast<unsigned char>(c))
            || std::string("~!@$%^&*_-+=<>.?/").find(c) != std::string::npos;
    };
    if (!initial(s.front())) { return false; }
    for (std::size_t i = 1; i < s.size(); ++i) {
        if (!initial(s[i]) && !std::isdigit(static_cast<unsigned char>(s[i]))) {
            return false;
        }
    }
    return true;
}

std::string canonicalSymbol(const std::string& raw) {
    std::string value = raw;
    if (value.size() >= 2 && value.front() == '|' && value.back() == '|') {
        value = value.substr(1, value.size() - 2);
    }
    return value;
}

std::string symbolSpelling(const std::string& raw) {
    const std::string value = canonicalSymbol(raw);
    return isSimpleSymbol(value) ? value : "|" + value + "|";
}

std::string appendSymbolSuffix(const std::string& raw, const std::string& suffix) {
    return symbolSpelling(canonicalSymbol(raw) + suffix);
}

// An explicitly selected dialect admits constructor declarations directly
// after (par (<parameters>)). Only the list boundary changes; constructor and
// selector contents still pass through the ordinary SMT datatype checker.
std::string groupedDatatypeBody(const std::string& body) {
    const auto parts = sexprItems(body);
    if (parts.size() < 3 || parts[0] != "par") { return body; }
    std::vector<std::string> parameters;
    if (!splitSExpr(parts[1], parameters) || parameters.empty()) { return body; }
    for (std::size_t i = 2; i < parts.size(); ++i) {
        const auto ctor = sexprItems(parts[i]);
        if (ctor.empty() || ctor[0].empty() || ctor[0].front() == '(') { return body; }
        for (std::size_t j = 1; j < ctor.size(); ++j) {
            if (sexprItems(ctor[j]).size() != 2) { return body; }
        }
    }
    std::string result = "(par " + parts[1] + " (";
    for (std::size_t i = 2; i < parts.size(); ++i) {
        if (i != 2) { result += ' '; }
        result += parts[i];
    }
    return result + "))";
}

std::string groupedDatatypeCommand(const std::string& body) {
    const auto parts = sexprItems(body);
    if (parts.size() != 3) { return body; }
    if (parts[0] == "declare-datatype") {
        const auto grouped = groupedDatatypeBody(parts[2]);
        return grouped == parts[2] ? body : "(" + parts[0] + " " + parts[1] + " " + grouped + ")";
    }
    if (parts[0] != "declare-datatypes") { return body; }
    std::vector<std::string> definitions;
    if (!splitSExpr(parts[2], definitions)) { return body; }
    bool changed = false;
    std::string result = "(" + parts[0] + " " + parts[1] + " (";
    for (std::size_t i = 0; i < definitions.size(); ++i) {
        const auto grouped = groupedDatatypeBody(definitions[i]);
        changed = changed || grouped != definitions[i];
        if (i) { result += ' '; }
        result += grouped;
    }
    return changed ? result + "))" : body;
}

bool flatDatatypeOption(const ParseOptions& opts, bool& enabled, Uir::Diagnostics& diags) {
    const auto it = opts.options.find("flat_datatype_constructors");
    enabled = false;
    if (it == opts.options.end()) { return true; }
    if (it->second != "true" && it->second != "false") {
        diags.error(ErrorCode::E_PARSE, "flat_datatype_constructors must be true or false");
        return false;
    }
    enabled = it->second == "true";
    if (enabled && opts.strict) {
        diags.error(ErrorCode::E_PARSE, "flat_datatype_constructors conflicts with strict parsing");
        return false;
    }
    return true;
}

/** `((a Bool) (b Int))` -> the pairs, without guessing at nested sorts. */
bool parseVarList(const std::string& s, std::vector<VarDeclText>& out,
                  Uir::Diagnostics& diags, const std::string& where) {
    std::vector<std::string> entries;
    if (!splitSExpr(s, entries)) {
        diags.error(ErrorCode::E_PARSE, where + " must be a variable declaration list");
        return false;
    }
    for (const std::string& entry : entries) {
        std::vector<std::string> pair;
        if (!splitSExpr(entry, pair) || pair.size() != 2 || pair[0].empty()
            || pair[0].front() == '(' || pair[1].empty()) {
            diags.error(ErrorCode::E_PARSE,
                        where + " entries must have the form `(symbol sort)`");
            return false;
        }
        VarDeclText d;
        d.name = symbolSpelling(pair[0]);
        d.sort = pair[1];
        out.push_back(std::move(d));
    }
    return true;
}

/** The `:key value` pairs at the top level of an s-expression body. Nested
 *  formulas and query reference lists may contain tokens beginning with `:`,
 *  so attributes must be recognized by depth rather than raw text search. */
bool topLevelSections(const std::string& body,
                      std::vector<std::pair<std::string, std::string>>& out,
                      Uir::Diagnostics& diags, const std::string& command) {
    std::vector<std::string> items;
    if (!splitSExpr(body, items) || items.size() < 2) {
        diags.error(ErrorCode::E_PARSE, "malformed " + command + " command");
        return false;
    }
    for (std::size_t i = 2; i < items.size();) {
        if (items[i].size() < 2 || items[i].front() != ':') {
            diags.error(ErrorCode::E_PARSE,
                        command + " expected an attribute but found `" + items[i] + "`");
            return false;
        }
        if (i + 1 >= items.size() || (!items[i + 1].empty()
                                      && items[i + 1].front() == ':')) {
            diags.error(ErrorCode::E_PARSE,
                        command + " attribute `" + items[i] + "` has no value");
            return false;
        }
        out.emplace_back(items[i].substr(1), items[i + 1]);
        i += 2;
    }
    return true;
}

/** One `:subsys (inst (child args...))`. Arguments correspond positionally to
 *  the child's inputs followed by its outputs. Parenthesized input/output
 *  groups are accepted as a compatible spelling and flattened here. */
struct SubsysInst {
    std::string inst;
    std::string child;
    std::vector<std::string> args;   // inputs then outputs, already flattened
};

/** A `define-system`. The formulas stay as text until lifted, one parser per
 *  system, because two systems may use the same variable name for different
 *  sorts -- `:local` is scoped to its system (§2.2) -- and one shared script
 *  could not declare both. */
struct SystemDef {
    std::string name;
    std::vector<VarDeclText> inputs, outputs, locals;
    std::string init, trans, inv;
    std::vector<SubsysInst> subsys;

    // Filled by lift().
    H::ExprPtr init_e, trans_e, inv_e;
    std::unordered_map<std::string, H::Sort> sorts;   // own name -> sort

    /** Inputs then outputs: the interface an instantiation's arguments line up
     *  against. Locals are NOT part of it -- they are the instance's own state,
     *  which is why each instance needs a fresh copy of them. */
    std::vector<VarDeclText> interface() const {
        std::vector<VarDeclText> v = inputs;
        v.insert(v.end(), outputs.begin(), outputs.end());
        return v;
    }
    std::vector<VarDeclText> allVars() const {
        std::vector<VarDeclText> v = interface();
        v.insert(v.end(), locals.begin(), locals.end());
        return v;
    }
};

class MoxiParser {
public:
    MoxiParser(std::string src, std::string file, unsigned depth,
               std::string query_selector, std::optional<std::size_t> check_index,
               bool flat_datatype_constructors = false)
        : src_(std::move(src)), file_(std::move(file)), depth_(depth),
          query_selector_(query_selector.empty() ? std::string{}
                                                 : symbolSpelling(query_selector)),
          check_index_(check_index), flat_datatype_constructors_(flat_datatype_constructors) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        const std::string clean = blankComments(src_);
        if (!readCommands(clean, diags)) { return nullptr; }
        for (const auto& rewrite : source_rewrites_) {
            Uir::EncodingChoice choice;
            choice.site = file_ + ":" + std::to_string(rewrite.loc.line);
            choice.unified_op = "source-reader";
            choice.strategy = rewrite.rule;
            choice.fidelity = Uir::Fidelity::exact();
            choice.rationale = "Explicit MoXI dialect: " + rewrite.original + " => " + rewrite.replacement;
            report.addChoice(std::move(choice));
        }
        module_mode_ = check_bodies_.empty();
        if (!liftEnvironment(diags) || !readSystems(diags)) { return nullptr; }
        if (check_bodies_.empty()) {
            // Absence of a query is not evidence that the library is valid.
            // Validate every definition, including unused subsystem branches.
            if (!buildModule(diags)) { return nullptr; }
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "no `check-system`: the file defines a system and asks nothing "
                        "about it, and an unrolling with no property asserted is "
                        "trivially satisfiable");
            return nullptr;
        }
        if (!readCheck(diags)) { return nullptr; }
        return build(diags, report);
    }

    std::shared_ptr<SourceModule> parseModule(Uir::Diagnostics& diags) {
        module_mode_ = true;
        if (!readCommands(blankComments(src_), diags)
            || !liftEnvironment(diags) || !readSystems(diags)) { return nullptr; }
        if (!check_bodies_.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "module import requires a query-free library; use translate for check-system");
            return nullptr;
        }
        return buildModule(diags);
    }

private:
    std::shared_ptr<SourceModule> buildModule(Uir::Diagnostics& diags) {
        for (const auto& name : order_) {
            if (!lift(systems_.at(name), diags)) { return nullptr; }
        }
        auto module = std::make_shared<SourceModule>();
        module->language = "moxi";
        module->source_rewrites = source_rewrites_;
        for (const auto& name : order_) {
            flat_.clear(); flat_seen_.clear();
            flat_init_.clear(); flat_trans_.clear(); flat_inv_.clear();
            const auto& definition = systems_.at(name);
            std::unordered_map<std::string, std::string> binding;
            std::unordered_map<std::string, H::Sort> sorts;
            std::unordered_map<std::string, std::string> roles;
            for (const auto& v : definition.inputs) { roles[v.name] = "input"; }
            for (const auto& v : definition.outputs) { roles[v.name] = "output"; }
            for (const auto& v : definition.allVars()) {
                const auto& sort = definition.sorts.at(v.name);
                binding[v.name] = v.name;
                binding[primeName(v.name)] = primeName(v.name);
                sorts[v.name] = sort; sorts[primeName(v.name)] = sort;
                addFlat(v.name, sort);
            }
            std::vector<std::string> stack;
            if (!instantiate(name, binding, sorts, "", stack, diags)) { return nullptr; }
            TransitionSystem system;
            system.name = definition.name;
            system.context.decls = global_decls_;
            system.context.funs = global_funs_;
            system.context.datatypes = global_datatypes_;
            for (const auto& v : flat_) {
                system.variables.push_back({v.name, primeName(v.name),
                    roles.count(v.name) ? roles.at(v.name) : "local", v.sort});
                system.context.decls.push_back({v.name, v.sort, nullptr, nullptr, {}});
                system.context.decls.push_back({primeName(v.name), v.sort, nullptr, nullptr, {}});
            }
            const auto conjunction = [](const std::vector<H::ExprPtr>& parts) {
                if (parts.empty()) { return H::mkBool(true); }
                if (parts.size() == 1) { return parts.front(); }
                return H::mkOp(H::Op::AND, parts);
            };
            system.init = conjunction(flat_init_);
            system.trans = conjunction(flat_trans_);
            system.invariant = conjunction(flat_inv_);
            module->systems.push_back(std::move(system));
        }
        if (!validateModule(*module, diags)) { return nullptr; }
        return module;
    }

    bool readCommands(const std::string& s, Uir::Diagnostics& diags) {
        bool saw_system = false, saw_check = false, saw_exit = false;
        std::size_t p = 0;
        std::size_t location_cursor = 0, source_line = 1;
        while (true) {
            skipSpace(s, p, s.size());
            if (p == s.size()) { break; }
            if (saw_exit || s[p] != '(') {
                diags.error(ErrorCode::E_PARSE,
                            saw_exit ? "(exit) must be the final MoXI command"
                                     : "MoXI input contains text outside a command");
                return false;
            }
            const std::size_t end = matchParen(s, p);
            if (end == std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "unbalanced parentheses in MoXI input");
                return false;
            }
            const std::string body = s.substr(p, end - p);
            std::vector<std::string> items;
            if (!splitSExpr(body, items) || items.empty() || items[0].empty()
                || items[0].front() == '(') {
                diags.error(ErrorCode::E_PARSE, "malformed MoXI top-level command");
                return false;
            }
            const std::string head = items[0];
            const bool environment_command = head == "set-logic"
                || head == "declare-sort" || head == "define-sort"
                || head == "declare-const" || head == "declare-fun"
                || head == "define-fun" || head == "declare-enum-sort"
                || head == "declare-datatype" || head == "declare-datatypes";
            if (environment_command) {
                if (saw_system || saw_check) {
                    diags.error(ErrorCode::E_PARSE,
                                "global MoXI declarations must precede system commands");
                    return false;
                }
                if (head == "declare-enum-sort") {
                    std::vector<std::string> constructors;
                    if (items.size() != 3 || items[1].empty()
                        || !splitSExpr(items[2], constructors) || constructors.empty()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "declare-enum-sort needs a sort and non-empty value list");
                        return false;
                    }
                    std::unordered_set<std::string> seen;
                    std::ostringstream enum_decl;
                    enum_decl << "(declare-datatypes ((" << items[1] << " 0)) ((";
                    for (const std::string& ctor : constructors) {
                        if (ctor.empty() || ctor.front() == '('
                            || !seen.insert(canonicalSymbol(ctor)).second) {
                            diags.error(ErrorCode::E_PARSE,
                                        "declare-enum-sort values must be distinct symbols");
                            return false;
                        }
                        enum_decl << "(" << ctor << ")";
                    }
                    enum_decl << ")))";
                    environment_.push_back(enum_decl.str());
                } else {
                    const auto normalized = flat_datatype_constructors_
                        ? groupedDatatypeCommand(body) : body;
                    environment_.push_back(normalized);
                    if (normalized != body) {
                        Uir::SourceLoc loc;
                        loc.file = file_;
                        source_line += std::count(s.begin() + location_cursor, s.begin() + p, '\n');
                        location_cursor = p;
                        loc.line = source_line;
                        source_rewrites_.push_back({"explicit-flat-datatype-constructors", body, normalized, loc});
                        diags.note(ErrorCode::OK, "applied flat_datatype_constructors at datatype declaration", loc);
                    }
                }
                if (head == "define-fun" && items.size() >= 2) {
                    defined_functions_.insert(canonicalSymbol(items[1]));
                }
                if (head == "declare-sort" || head == "declare-const"
                    || head == "declare-fun") {
                    has_rigid_free_symbols_ = true;
                }
            } else if (head == "define-system") {
                saw_system = true;
                system_bodies_.push_back(body);
            } else if (head == "check-system") {
                saw_check = true;
                check_bodies_.push_back(body);
            } else if (head == "exit" && items.size() == 1) {
                saw_exit = true;
            } else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "top-level command `" + head + "` is not in the MoXI grammar");
                return false;
            }
            p = end;
        }
        return true;
    }

    bool liftEnvironment(Uir::Diagnostics& diags) {
        std::ostringstream script;
        for (const std::string& command : environment_) { script << command << "\n"; }
        ParserPtr engine = newParser();
        engine->getOptions()->setExpandFunctions(true);
        try {
            if (!engine->parseStr(script.str())) {
                diags.error(ErrorCode::E_PARSE,
                            "MoXI global sort/function declarations are not well formed");
                return false;
            }
        } catch (const std::exception& e) {
            diags.error(ErrorCode::E_PARSE,
                        std::string("MoXI global declarations did not parse: ") + e.what());
            return false;
        }
        H::ConstraintModel lifted;
        Lower::ParserToHir up(engine);
        if (!up.lift(lifted, diags)) { return false; }
        global_decls_ = lifted.decls;
        global_datatypes_ = lifted.datatypes;
        for (const H::FunDecl& f : lifted.funs) {
            if (defined_functions_.count(canonicalSymbol(f.name)) == 0) {
                global_funs_.push_back(f);
            }
        }
        return true;
    }

    bool readSystems(Uir::Diagnostics& diags) {
        if (system_bodies_.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "no `define-system`: this is not a MoXI file");
            return false;
        }
        for (const std::string& body : system_bodies_) {
            SystemDef d;
            // `(define-system NAME :input ...)` -- the name is the token after
            // the command, before the first keyword.
            {
                const std::vector<std::string> head = sexprItems(body);
                if (head.size() < 2 || head[1].empty() || head[1][0] == ':') {
                    diags.error(ErrorCode::E_PARSE, "a define-system with no name");
                    return false;
                }
                d.name = symbolSpelling(head[1]);
            }
            std::unordered_set<std::string> singleton_sections;
            std::vector<std::pair<std::string, std::string>> sections;
            if (!topLevelSections(body, sections, diags, "define-system")) { return false; }
            bool saw_formula = false;
            for (const auto& kv : sections) {
                const bool repeatable = kv.first == "subsys";
                const bool known = kv.first == "input" || kv.first == "output"
                    || kv.first == "local" || kv.first == "init"
                    || kv.first == "trans" || kv.first == "inv" || repeatable;
                if (!known) {
                    diags.error(ErrorCode::E_PARSE,
                                "unknown define-system attribute `:" + kv.first + "`");
                    return false;
                }
                if (!repeatable && !singleton_sections.insert(kv.first).second) {
                    diags.error(ErrorCode::E_PARSE,
                                "define-system `" + d.name + "` repeats `:" + kv.first
                                    + "`; this attribute may occur at most once");
                    return false;
                }
                if ((kv.first == "input" || kv.first == "output" || kv.first == "local")
                    && saw_formula) {
                    diags.error(ErrorCode::E_PARSE,
                                "define-system interfaces must precede init/trans/inv");
                    return false;
                }
                saw_formula = saw_formula || kv.first == "init" || kv.first == "trans"
                    || kv.first == "inv";
                if (kv.first == "input") {
                    if (!parseVarList(kv.second, d.inputs, diags,
                                      "define-system :input")) { return false; }
                } else if (kv.first == "output") {
                    if (!parseVarList(kv.second, d.outputs, diags,
                                      "define-system :output")) { return false; }
                } else if (kv.first == "local") {
                    if (!parseVarList(kv.second, d.locals, diags,
                                      "define-system :local")) { return false; }
                } else if (kv.first == "init")  { d.init  = kv.second; }
                else if (kv.first == "trans")   { d.trans = kv.second; }
                else if (kv.first == "inv")     { d.inv   = kv.second; }
                else if (kv.first == "subsys") {
                    SubsysInst si;
                    const std::vector<std::string> items = sexprItems(kv.second);
                    if (items.empty()) {
                        diags.error(ErrorCode::E_PARSE, "an empty `:subsys`");
                        return false;
                    }
                    si.inst = symbolSpelling(items[0]);
                    for (std::size_t i = 1; i < items.size(); ++i) {
                        const std::vector<std::string> group = sexprItems(items[i]);
                        for (std::size_t g = 0; g < group.size(); ++g) {
                            // The first token of the FIRST group is the child
                            // system's name; everything after it, across all
                            // groups, is an argument. That reads §2.3's
                            // two-list form and the corpus's one-list form
                            // identically.
                            if (i == 1 && g == 0) { si.child = symbolSpelling(group[g]); }
                            else { si.args.push_back(symbolSpelling(group[g])); }
                        }
                    }
                    if (si.inst.empty() || si.child.empty()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a `:subsys` without an instance name and a system name");
                        return false;
                    }
                    d.subsys.push_back(std::move(si));
                }
            }
            {
                std::unordered_set<std::string> names;
                for (const VarDeclText& v : d.allVars()) {
                    if (!names.insert(v.name).second) {
                        diags.error(ErrorCode::E_PARSE,
                                    "system `" + d.name + "` declares variable `" + v.name
                                        + "` more than once across input/output/local");
                        return false;
                    }
                }
                std::unordered_set<std::string> instances;
                for (const SubsysInst& si : d.subsys) {
                    if (!instances.insert(si.inst).second) {
                        diags.error(ErrorCode::E_PARSE,
                                    "system `" + d.name + "` repeats subsystem instance `"
                                        + si.inst + "`; instance names must be distinct");
                        return false;
                    }
                }
            }
            if (module_mode_) {
                // Keep every definition, in order. The reference resolves a
                // subsystem against definitions visible at that command, so
                // a later same-name definition must not rewrite an earlier
                // instance's meaning. Internal keys are separate from symbols.
                for (auto& subsystem : d.subsys) {
                    const auto prior = module_versions_.find(subsystem.child);
                    if (prior == module_versions_.end()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "subsystem '" + subsystem.child + "' is not defined before its use");
                        return false;
                    }
                    subsystem.child = prior->second;
                }
                const std::string key = "definition-" + std::to_string(order_.size());
                module_versions_[d.name] = key;
                order_.push_back(key);
                systems_[key] = std::move(d);
                continue;
            }
            if (systems_.count(d.name) != 0) {
                // Refused rather than resolved. Whether the later definition
                // shadows the earlier, or the file is simply ill-formed, is a
                // question about MoXI that this project's document does not
                // answer -- and picking one would silently translate a system
                // that may not be the one the file means.
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "system `" + d.name
                                + "` is defined twice, and which definition a later "
                                  "reference means is not something to guess");
                return false;
            }
            order_.push_back(d.name);
            systems_[d.name] = std::move(d);
        }
        return true;
    }

    /** The name out of a `(q1 (r1))` query entry, or empty if it has no shape.
     *
     *  Deliberately does NOT validate: this runs in a diagnostic, before the
     *  queries are parsed, and a message that failed because the thing it was
     *  describing was malformed would replace a useful refusal with a useless
     *  one. A malformed entry contributes nothing to the list and is reported
     *  properly a few lines later, by the parser that owns that check. */
    std::string queryName(const std::string& entry) const {
        const std::vector<std::string> items = sexprItems(entry);
        if (items.empty() || items[0].empty() || items[0][0] == ':') { return {}; }
        return symbolSpelling(items[0]);
    }

    bool readCheck(Uir::Diagnostics& diags) {
        if (check_bodies_.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "no `check-system`: the file defines a system and asks nothing "
                        "about it, and an unrolling with no property asserted is "
                        "trivially satisfiable");
            return false;
        }
        if (check_bodies_.size() > 1 && !check_index_) {
            // The COUNT, for the reason the query refusal names its queries:
            // a corpus sweep has to ask all of them, and `check_index` is
            // 0-based, so "2" alone does not say which values are legal.
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "the file contains multiple check-system commands; each asks "
                        "separate questions and a ConstraintModel carries one; pass "
                        "check_index=<n> to select one explicitly (check_index range: 0.."
                            + std::to_string(check_bodies_.size() - 1) + ")");
            return false;
        }
        const std::size_t check = check_index_.value_or(0);
        if (check >= check_bodies_.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "check_index=" + std::to_string(check)
                            + " is outside the " + std::to_string(check_bodies_.size())
                            + " check-system commands in the file");
            return false;
        }
        const std::string& body = check_bodies_[check];

        // `(check-system NAME ...)` picks which system is the ROOT. With a
        // hierarchy that is the whole question -- a file defining `Delay` and
        // `DoubleDelay` is asking about whichever one this names, and flattening
        // the other would answer about a system nobody asked about.
        {
            const std::vector<std::string> head = sexprItems(body);
            if (head.size() < 2 || head[1].empty() || head[1][0] == ':') {
                diags.error(ErrorCode::E_PARSE, "a check-system with no system name");
                return false;
            }
            root_ = symbolSpelling(head[1]);
            if (systems_.count(root_) == 0) {
                diags.error(ErrorCode::E_PARSE,
                            "`check-system " + root_
                                + "` names a system this file does not define");
                return false;
            }
        }

        // Conditions and queries are top-level attributes. Published MoXI uses
        // named conditions and queries select those names; `:invariant` and
        // keyword references are older project-local spellings, not a second
        // standard grammar.
        std::vector<std::pair<std::string, std::string>> raw;  // (keyword, value)
        std::unordered_set<std::string> interface_sections;
        std::vector<std::pair<std::string, std::string>> sections;
        if (!topLevelSections(body, sections, diags, "check-system")) { return false; }
        for (const auto& kv : sections) {
            if (kv.first == "reachable" || kv.first == "assumption"
                || kv.first == "fairness" || kv.first == "current") {
                raw.emplace_back(kv.first, kv.second);
            } else if (kv.first == "query") {
                queries_.push_back(kv.second);
            } else if (kv.first == "queries") {
                std::vector<std::string> grouped;
                if (!splitSExpr(kv.second, grouped)) {
                    diags.error(ErrorCode::E_PARSE,
                                "`:queries` must contain `(name (condition ...))` entries");
                    return false;
                }
                if (grouped.size() > 1) { has_multi_query_group_ = true; }
                queries_.insert(queries_.end(), grouped.begin(), grouped.end());
            } else if (kv.first == "invariant") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "`:invariant` is not a check-system condition in the published "
                            "MoXI grammar; express a violation query as a named "
                            "`:reachable` condition containing `(not P)`");
                return false;
            } else if (kv.first == "input" || kv.first == "output"
                       || kv.first == "local") {
                if (!interface_sections.insert(kv.first).second) {
                    diags.error(ErrorCode::E_PARSE,
                                "check-system repeats `:" + kv.first
                                    + "`; the interface is positional and may be stated once");
                    return false;
                }
                std::vector<VarDeclText>* into = kv.first == "input" ? &chk_inputs_
                    : kv.first == "output" ? &chk_outputs_ : &chk_locals_;
                if (!parseVarList(kv.second, *into, diags,
                                  "check-system :" + kv.first)) { return false; }
            } else {
                diags.error(ErrorCode::E_PARSE,
                            "unknown check-system attribute `:" + kv.first + "`");
                return false;
            }
        }

        if (queries_.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "the check-system defines no query, so it asks no question");
            return false;
        }
        if (queries_.size() > 1 && query_selector_.empty()) {
            // The NAMES, not just the count. A harness sweeping a corpus has to
            // ask every question a file asks -- answering one of two is a
            // smaller problem, not this one -- and it can only do that if the
            // refusal says what the alternatives are called. Without them the
            // only reading of this message is "refused", and four files that
            // translate perfectly once asked properly were counted as coverage
            // failures for it.
            std::string names;
            for (const std::string& q : queries_) {
                const std::string n = queryName(q);
                if (n.empty()) { continue; }
                names += (names.empty() ? "" : ", ") + n;
            }
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "this check-system asks " + std::to_string(queries_.size())
                            + " separate queries; each is its own question and a "
                              "ConstraintModel carries one, so translating them together "
                              "would answer a question the file did not ask; pass "
                              "query=<name> to select one explicitly (queries: "
                            + names + ")");
            return false;
        }
        if (has_multi_query_group_ && has_rigid_free_symbols_) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "queries in one `:queries` attribute must share one rigid "
                        "interpretation; selecting and solving one independently would "
                        "weaken that semantics, so grouped queries with free global "
                        "sorts/constants/functions require a multi-result model");
            return false;
        }

        std::unordered_map<std::string, std::size_t> named;
        std::unordered_set<std::string> condition_names;
        for (const auto& c : raw) {
            const std::vector<std::string> items = sexprItems(c.second);
            if (items.size() != 2 || items[0].empty() || items[0][0] == ':'
                || items[0][0] == '(' || items[1].empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "`:" + c.first
                                + "` must have the named form `(name Bool-term)`");
                return false;
            }
            const std::string condition_name = symbolSpelling(items[0]);
            if (!condition_names.insert(condition_name).second) {
                diags.error(ErrorCode::E_PARSE,
                            "check-system condition name `" + condition_name
                                + "` is ambiguous because it is declared more than once");
                return false;
            }
            conditions_.push_back(Condition{c.first, condition_name, items[1], false});
            named[condition_name] = conditions_.size() - 1;
        }

        struct Query { std::string name; std::vector<std::string> refs; };
        std::vector<Query> parsed_queries;
        std::unordered_set<std::string> query_names;
        for (const std::string& query : queries_) {
            const std::vector<std::string> items = sexprItems(query);
            if (items.size() != 2 || items[0].empty() || items[0][0] == ':'
                || items[1].empty() || items[1][0] != '(') {
                diags.error(ErrorCode::E_PARSE,
                            "`:query` must have the form `(query-name "
                            "(condition-name ...))`");
                return false;
            }
            Query parsed;
            parsed.name = symbolSpelling(items[0]);
            if (!query_names.insert(parsed.name).second) {
                diags.error(ErrorCode::E_PARSE,
                            "query name `" + parsed.name
                                + "` is declared more than once in this check-system");
                return false;
            }
            parsed.refs = sexprItems(items[1]);
            for (std::string& ref : parsed.refs) {
                if (!ref.empty() && ref[0] == ':') {
                    diags.error(ErrorCode::E_PARSE,
                                "query reference `" + ref
                                    + "` is a keyword; MoXI queries select named conditions");
                    return false;
                }
                ref = symbolSpelling(ref);
                if (named.count(ref) == 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "query `" + parsed.name
                                    + "` references unknown condition `" + ref + "`");
                    return false;
                }
            }
            parsed_queries.push_back(std::move(parsed));
        }

        const Query* selected_query = nullptr;
        if (query_selector_.empty()) {
            selected_query = &parsed_queries.front();
        } else {
            for (const Query& query : parsed_queries) {
                if (query.name == query_selector_) { selected_query = &query; break; }
            }
            if (selected_query == nullptr) {
                diags.error(ErrorCode::E_PARSE,
                            "query selector `" + query_selector_
                                + "` does not name a query in the selected check-system");
                return false;
            }
        }

        unsigned selected_current = 0;
        for (const std::string& ref : selected_query->refs) {
            const auto it = named.find(ref);
            Condition& selected = conditions_[it->second];
            const bool newly_selected = !selected.selected;
            selected.selected = true;
            if (newly_selected && selected.keyword == "current") { ++selected_current; }

        }
        if (selected_current > 1) {
            diags.error(ErrorCode::E_PARSE,
                        "a query may select at most one `:current` initiality condition");
            return false;
        }
        for (const Condition& c : conditions_) {
            if (c.selected) { continue; }
            diags.note(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                       "`:" + c.keyword + " " + c.name
                           + "` is not named by the query, so it is not checked and not "
                             "translated");
        }

        // The check-system RESTATES the system's interface, and the names it
        // uses need not be the system's: `:input ((i ...))` against the
        // system's `:input ((in ...))` identifies `i` WITH `in` positionally.
        // They are one variable, not two related by an equation -- the same
        // trap §4.2 records for a subsystem's argument list, one level up.
        // Undeclared, the condition's `i` surfaced as the engine's
        // `Unknown or unexpected symbol "i"`.
        const SystemDef& r = systems_.at(root_);
        {
            std::unordered_set<std::string> names;
            std::vector<VarDeclText> all = chk_inputs_;
            all.insert(all.end(), chk_outputs_.begin(), chk_outputs_.end());
            all.insert(all.end(), chk_locals_.begin(), chk_locals_.end());
            for (const VarDeclText& v : all) {
                if (!names.insert(v.name).second) {
                    diags.error(ErrorCode::E_PARSE,
                                "check-system declares renamed variable `" + v.name
                                    + "` more than once");
                    return false;
                }
            }
        }
        if (!identify(chk_inputs_,  r.inputs,  "input",  diags)) { return false; }
        if (!identify(chk_outputs_, r.outputs, "output", diags)) { return false; }
        if (!identify(chk_locals_,  r.locals,  "local",  diags)) { return false; }
        return true;
    }

    bool parseSortText(const std::string& text, H::Sort& out,
                       Uir::Diagnostics& diags) {
        const std::string probe = "|.moxi sort probe " + std::to_string(++sort_probe_) + "|";
        std::ostringstream script;
        for (const std::string& command : environment_) { script << command << "\n"; }
        script << "(declare-fun " << probe << " () " << text << ")\n";
        ParserPtr engine = newParser();
        engine->getOptions()->setExpandFunctions(true);
        try {
            if (!engine->parseStr(script.str())) {
                diags.error(ErrorCode::E_PARSE, "invalid MoXI sort `" + text + "`");
                return false;
            }
        } catch (const std::exception& e) {
            diags.error(ErrorCode::E_PARSE,
                        "invalid MoXI sort `" + text + "`: " + e.what());
            return false;
        }
        H::ConstraintModel lifted;
        Lower::ParserToHir up(engine);
        if (!up.lift(lifted, diags)) { return false; }
        for (const H::VarDecl& d : lifted.decls) {
            if (canonicalSymbol(d.name) == canonicalSymbol(probe)) {
                out = d.sort;
                return true;
            }
        }
        diags.error(ErrorCode::E_INTERNAL, "sort probe declaration was not lifted");
        return false;
    }

    /** Positionally identify a check-system variable list with the system's. */
    bool identify(const std::vector<VarDeclText>& chk,
                  const std::vector<VarDeclText>& sys,
                  const char* what, Uir::Diagnostics& diags) {
        if (chk.size() != sys.size()) {
            diags.error(ErrorCode::E_PARSE,
                        std::string("the check-system's `:") + what + "` lists "
                            + std::to_string(chk.size()) + " variable(s) and the system's "
                              "lists " + std::to_string(sys.size())
                            + "; the correspondence is positional, so it cannot be made");
            return false;
        }
        for (std::size_t i = 0; i < chk.size(); ++i) {
            H::Sort chk_sort, sys_sort;
            if (!parseSortText(chk[i].sort, chk_sort, diags)
                || !parseSortText(sys[i].sort, sys_sort, diags)) {
                return false;
            }
            if (!H::sameSort(chk_sort, sys_sort)) {
                diags.error(ErrorCode::E_TYPE,
                            "the check-system identifies `" + chk[i].name + "` of sort "
                                + chk[i].sort + " with the system's `" + sys[i].name
                                + "` of sort " + sys[i].sort
                                + "; identified variables are one variable and cannot have "
                                  "two sorts");
                return false;
            }
            if (chk[i].name != sys[i].name) {
                const SystemDef& root = systems_.at(root_);
                for (const VarDeclText& existing : root.allVars()) {
                    if (existing.name == chk[i].name && existing.name != sys[i].name) {
                        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                    "check-system renaming `" + chk[i].name
                                        + "` collides with a different system variable; "
                                          "the formula and system scopes cannot be merged "
                                          "without ambiguity");
                        return false;
                    }
                }
            }
            if (chk[i].name != sys[i].name) {
                alias_[chk[i].name] = sys[i].name;
                alias_sort_text_[chk[i].name] = chk[i].sort;
            }
        }
        return true;
    }

    static std::string primeName(const std::string& base) {
        return appendSymbolSuffix(base, kPrimeSuffix);
    }

    /** Rewrite MoXI's token-level prime convention without touching strings.
     *  Both `|quoted name|'` and the reference tool's `|quoted name'|` spelling
     *  denote the next copy of `|quoted name|`. */
    static std::string dePrime(const std::string& t) {
        std::string out;
        for (std::size_t i = 0; i < t.size();) {
            if (t[i] == '"') {
                const std::size_t end = scanAtom(t, i, t.size());
                if (end == std::string::npos) { return t; }
                out.append(t, i, end - i);
                i = end;
                continue;
            }
            if (t[i] == '|') {
                std::size_t close = i + 1;
                while (close < t.size() && t[close] != '|') { ++close; }
                if (close == t.size()) { return t; }
                std::string content = t.substr(i + 1, close - i - 1);
                bool primed = false;
                if (!content.empty() && content.back() == '\'') {
                    content.pop_back();
                    primed = true;
                } else if (close + 1 < t.size() && t[close + 1] == '\'') {
                    primed = true;
                    ++close;
                }
                out += primed ? primeName(symbolSpelling(content))
                              : symbolSpelling(content);
                i = close + 1;
                continue;
            }
            if (std::isspace(static_cast<unsigned char>(t[i])) || t[i] == '('
                || t[i] == ')') {
                out += t[i++];
                continue;
            }
            const std::size_t end = scanAtom(t, i, t.size());
            if (end == std::string::npos) { return t; }
            std::string atom = t.substr(i, end - i);
            if (atom.size() > 1 && atom.back() == '\'') {
                atom.pop_back();
                atom = primeName(symbolSpelling(atom));
            }
            out += atom;
            i = end;
        }
        return out;
    }

    static bool unprimeName(const std::string& name, std::string& base) {
        const std::string value = canonicalSymbol(name);
        const std::string suffix = kPrimeSuffix;
        if (value.size() < suffix.size()
            || value.compare(value.size() - suffix.size(), suffix.size(), suffix) != 0) {
            return false;
        }
        base = symbolSpelling(value.substr(0, value.size() - suffix.size()));
        return true;
    }

    static void primedNames(const H::ExprPtr& e, std::vector<std::string>& out) {
        if (!e) { return; }
        std::string base;
        if (e->kind == H::ExprKind::IDENT && unprimeName(e->name, base)) {
            out.push_back(base);
        }
        for (const H::ExprPtr& a : e->args) { primedNames(a, out); }
    }

    bool validateFormulaVariables(const SystemDef& d, Uir::Diagnostics& diags) const {
        const auto noPrime = [&](const H::ExprPtr& e, const char* where) {
            std::vector<std::string> primed;
            primedNames(e, primed);
            if (primed.empty()) { return true; }
            diags.error(ErrorCode::E_PARSE,
                        "system `" + d.name + "` `:" + where
                            + "` is a one-state formula but mentions primed variable `"
                            + primed.front() + "'`");
            return false;
        };
        if (!noPrime(d.init_e, "init") || !noPrime(d.inv_e, "inv")) { return false; }
        if (d.name != root_) { return true; }

        std::unordered_set<std::string> input_names;
        for (const VarDeclText& v : d.inputs) { input_names.insert(v.name); }
        for (const VarDeclText& v : chk_inputs_) { input_names.insert(v.name); }
        for (const Condition& c : conditions_) {
            if (!c.selected) { continue; }
            const auto ce = cond_e_.find(&c);
            if (ce == cond_e_.end()) { continue; }
            std::vector<std::string> primed;
            primedNames(ce->second, primed);
            if (c.keyword == "current" && !primed.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "`:current " + c.name
                                + "` is a one-state initiality condition but mentions `"
                                + primed.front() + "'`");
                return false;
            }
            if (c.keyword == "assumption" || c.keyword == "fairness") {
                for (const std::string& name : primed) {
                    if (input_names.count(name) == 0) {
                        diags.error(ErrorCode::E_PARSE,
                                    "`:" + c.keyword + " " + c.name
                                        + "` may prime only an input variable, but mentions `"
                                        + name + "'`");
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** Parse and lift ONE system's formulas, over its own variable names.
     *
     *  One parser per system, not one script for the file: `:local` is scoped to
     *  its system (§2.2), so two systems may use the same name for variables of
     *  different sorts and a shared script could not declare both. Flattening
     *  then happens in the HIR, where a substitution is a substitution rather
     *  than a search-and-replace over text. */
    bool lift(SystemDef& d, Uir::Diagnostics& diags) {
        std::ostringstream script;
        for (const std::string& command : environment_) { script << command << "\n"; }
        for (const VarDeclText& v : d.allVars()) {
            script << "(declare-fun " << v.name << " () " << v.sort << ")\n";
            script << "(declare-fun " << primeName(v.name) << " () " << v.sort << ")\n";
        }
        // The root system's script also carries the check-system's own names and
        // the conditions written over them.
        std::vector<const Condition*> conds;
        if (d.name == root_) {
            for (const auto& kv : alias_) {
                const auto sort = alias_sort_text_.find(kv.first);
                if (sort == alias_sort_text_.end()) { continue; }
                script << "(declare-fun " << kv.first << " () " << sort->second << ")\n";
                script << "(declare-fun " << primeName(kv.first) << " () " << sort->second
                       << ")\n";
            }
            for (const Condition& c : conditions_) {
                if (c.selected) { conds.push_back(&c); }
            }
        }

        std::vector<const std::string*> ordered;
        const std::string* slots[3] = {&d.init, &d.trans, &d.inv};
        for (const std::string* t : slots) {
            if (!t->empty()) { ordered.push_back(t); }
        }
        for (const Condition* c : conds) { ordered.push_back(&c->term); }
        for (const std::string* t : ordered) { script << "(assert " << dePrime(*t) << ")\n"; }

        ParserPtr engine = newParser();
        engine->getOptions()->setExpandFunctions(true);
        try {
            if (!engine->parseStr(script.str())) {
                diags.error(ErrorCode::E_PARSE,
                            "system `" + d.name
                                + "`: the formulas are not a well-formed SMT-LIB script");
                return false;
            }
        } catch (const std::exception& e) {
            diags.error(ErrorCode::E_PARSE,
                        "system `" + d.name + "`: the formulas did not parse: " + e.what());
            return false;
        }
        H::ConstraintModel lifted;
        Lower::ParserToHir up(engine);
        if (!up.lift(lifted, diags)) { return false; }
        if (lifted.constraints.size() < ordered.size()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "system `" + d.name + "`: formula count mismatch");
            return false;
        }
        for (const H::VarDecl& v : lifted.decls) { d.sorts[v.name] = v.sort; }

        std::size_t at = lifted.constraints.size() - ordered.size();
        if (!d.init.empty())  { d.init_e  = lifted.constraints[at++].formula; }
        if (!d.trans.empty()) { d.trans_e = lifted.constraints[at++].formula; }
        if (!d.inv.empty())   { d.inv_e   = lifted.constraints[at++].formula; }
        for (const Condition* c : conds) { cond_e_[c] = lifted.constraints[at++].formula; }
        return validateFormulaVariables(d, diags);
    }

    /** One system's variable, in the FLATTENED model. */
    struct Flat {
        std::string name;
        H::Sort     sort;
    };

    /** Instantiate @p sys under @p binding, conjoining its init, trans and inv
     *  into the flattened ones, then do the same for each of its subsystems.
     *
     *  @p binding maps the system's OWN variable names -- and their primed
     *  copies -- to the names they have in the flattened model. For the root it
     *  is the identity. For an instance it identifies the child's interface with
     *  the parent's arguments and gives the child's LOCALS a per-instance name.
     *
     *  That last point is the composition bug §4.2 leads with. Two instances of
     *  the same child sharing one copy of its locals is a strictly more
     *  constrained system that still answers: a reachable bad state can become
     *  unreachable and the instance reports safe. So the locals are qualified by
     *  the instance path, and the fixture that proves it is two instances of one
     *  child that must be in different states for the property to fail. */
    bool instantiate(const std::string& sys_name,
                     const std::unordered_map<std::string, std::string>& binding,
                     const std::unordered_map<std::string, H::Sort>& binding_sorts,
                     const std::string& path,
                     std::vector<std::string>& stack,
                     Uir::Diagnostics& diags) {
        const auto it = systems_.find(sys_name);
        if (it == systems_.end()) {
            diags.error(ErrorCode::E_PARSE,
                        "`:subsys` instantiates `" + sys_name
                            + "`, which this file does not define");
            return false;
        }
        // A hierarchy that contains itself has no finite flattening. Refused by
        // naming the cycle rather than by recursing until the stack goes.
        for (const std::string& on : stack) {
            if (on == sys_name) {
                std::string cyc;
                for (const std::string& n : stack) { cyc += n + " -> "; }
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "the subsystem hierarchy is cyclic (" + cyc + sys_name
                                + "), so it has no finite flattening");
                return false;
            }
        }
        stack.push_back(sys_name);

        SystemDef& d = it->second;
        const H::ExprPtr* parts[3] = {&d.init_e, &d.trans_e, &d.inv_e};
        std::vector<H::ExprPtr>* into[3] = {&flat_init_, &flat_trans_, &flat_inv_};
        for (int i = 0; i < 3; ++i) {
            if (!*parts[i]) { continue; }
            into[i]->push_back(H::substituteIdents(*parts[i], binding, binding_sorts));
        }

        for (const SubsysInst& si : d.subsys) {
            const auto ci = systems_.find(si.child);
            if (ci == systems_.end()) {
                diags.error(ErrorCode::E_PARSE,
                            "`:subsys " + si.inst + "` instantiates `" + si.child
                                + "`, which this file does not define");
                return false;
            }
            const std::vector<VarDeclText> iface = ci->second.interface();
            if (si.args.size() != iface.size()) {
                diags.error(ErrorCode::E_PARSE,
                            "`:subsys " + si.inst + " (" + si.child + " ...)` passes "
                                + std::to_string(si.args.size()) + " argument(s) and `"
                                + si.child + "` has " + std::to_string(iface.size())
                                + " interface variable(s) (" + std::to_string(
                                      ci->second.inputs.size()) + " input, "
                                + std::to_string(ci->second.outputs.size())
                                + " output); the correspondence is positional");
                return false;
            }

            std::unordered_map<std::string, std::string> child_bind;
            std::unordered_map<std::string, H::Sort> child_sorts;
            for (std::size_t a = 0; a < iface.size(); ++a) {
                // IDENTIFICATION, not an equation: the child's interface
                // variable and the parent's argument become one variable in the
                // flattened model. §4.2 records that treating it as
                // `arg = child_input` is usually equivalent and not always --
                // not when the child's input is also driven elsewhere -- and
                // that identification is the specification's reading while an
                // equation is an encoding choice.
                const auto pa = binding.find(si.args[a]);
                if (pa == binding.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "`:subsys " + si.inst + "` passes `" + si.args[a]
                                    + "`, which is not a variable of system `" + d.name
                                    + "`");
                    return false;
                }
                if (a >= ci->second.inputs.size()) {
                    bool writable = false;
                    for (const VarDeclText& v : d.outputs) {
                        writable = writable || v.name == si.args[a];
                    }
                    for (const VarDeclText& v : d.locals) {
                        writable = writable || v.name == si.args[a];
                    }
                    if (!writable) {
                        diags.error(ErrorCode::E_PARSE,
                                    "`:subsys " + si.inst + "` wires child output `"
                                        + iface[a].name + "` to parent input `" + si.args[a]
                                        + "`; a child output must map to a parent local or "
                                          "output variable");
                        return false;
                    }
                }
                const auto ps = binding_sorts.find(si.args[a]);
                const auto cs = ci->second.sorts.find(iface[a].name);
                if (ps == binding_sorts.end() || cs == ci->second.sorts.end()) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "missing sort while wiring `:subsys " + si.inst + "`");
                    return false;
                }
                if (!H::sameSort(ps->second, cs->second)) {
                    diags.error(ErrorCode::E_TYPE,
                                "`:subsys " + si.inst + "` wires parent variable `"
                                    + si.args[a] + "` to child variable `" + iface[a].name
                                    + "`, but their sorts differ");
                    return false;
                }
                child_bind[iface[a].name] = pa->second;
                child_bind[primeName(iface[a].name)] = primeName(pa->second);
                child_sorts[iface[a].name] = ps->second;
                child_sorts[primeName(iface[a].name)] = ps->second;
            }
            const std::string child_path = path + canonicalSymbol(si.inst) + ".";
            for (const VarDeclText& lv : ci->second.locals) {
                const auto si_it = ci->second.sorts.find(lv.name);
                if (si_it == ci->second.sorts.end()) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "missing sort for local `" + lv.name + "` in subsystem `"
                                    + si.child + "`");
                    return false;
                }
                const H::Sort s = si_it->second;
                std::string flat = symbolSpelling(child_path + canonicalSymbol(lv.name));
                for (unsigned suffix = 1; flat_seen_.count(flat) != 0; ++suffix) {
                    flat = appendSymbolSuffix(
                        symbolSpelling(child_path + canonicalSymbol(lv.name)),
                        ".fresh" + std::to_string(suffix));
                }
                child_bind[lv.name] = flat;
                child_bind[primeName(lv.name)] = primeName(flat);
                child_sorts[lv.name] = s;
                child_sorts[primeName(lv.name)] = s;
                addFlat(flat, s);
            }
            if (!instantiate(si.child, child_bind, child_sorts, child_path, stack, diags)) {
                return false;
            }
        }
        stack.pop_back();
        return true;
    }

    void addFlat(const std::string& name, const H::Sort& s) {
        if (flat_seen_.insert(name).second) { flat_.push_back(Flat{name, s}); }
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        // Only the systems the root reaches are lifted -- a file may define a
        // library of systems and ask about one of them, and parsing a system
        // nobody instantiated could refuse the file for a construct that has no
        // bearing on the question asked.
        {
            std::vector<std::string> want{root_};
            std::unordered_set<std::string> done;
            while (!want.empty()) {
                const std::string n = want.back();
                want.pop_back();
                if (!done.insert(n).second) { continue; }
                const auto it = systems_.find(n);
                if (it == systems_.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "`:subsys` instantiates `" + n
                                    + "`, which this file does not define");
                    return nullptr;
                }
                if (!lift(it->second, diags)) { return nullptr; }
                for (const SubsysInst& si : it->second.subsys) { want.push_back(si.child); }
            }
        }

        // The root's variables keep their own names, so a single-system file
        // produces exactly the output it did before flattening existed.
        const SystemDef& r = systems_.at(root_);
        std::unordered_map<std::string, std::string> root_bind;
        std::unordered_map<std::string, H::Sort> root_sorts;
        for (const VarDeclText& v : r.allVars()) {
            const auto si = r.sorts.find(v.name);
            if (si == r.sorts.end()) {
                diags.error(ErrorCode::E_INTERNAL,
                            "missing lifted sort for root variable `" + v.name + "`");
                return nullptr;
            }
            const H::Sort s = si->second;
            root_bind[v.name] = v.name;
            root_bind[primeName(v.name)] = primeName(v.name);
            root_sorts[v.name] = s;
            root_sorts[primeName(v.name)] = s;
            addFlat(v.name, s);
        }
        {
            std::vector<std::string> stack;
            if (!instantiate(root_, root_bind, root_sorts, "", stack, diags)) {
                return nullptr;
            }
        }

        std::unordered_map<std::string, H::Sort> sorts;
        for (const Flat& f : flat_) {
            sorts[f.name] = f.sort;
            sorts[primeName(f.name)] = f.sort;
        }
        for (const auto& kv : alias_) {
            const auto s = sorts.find(kv.second);
            if (s != sorts.end()) { sorts[kv.first] = s->second; }
        }

        auto model = std::make_shared<H::ConstraintModel>();
        model->datatypes = global_datatypes_;
        model->funs = global_funs_;
        for (const H::VarDecl& d : global_decls_) {
            if (!declared_.insert(d.name).second) {
                diags.error(ErrorCode::E_PARSE,
                            "global symbol `" + d.name + "` is declared more than once");
                return nullptr;
            }
            model->decls.push_back(d);
        }
        // n-satisfaction evaluates primed atoms at step n against state n+1,
        // so a depth-n finite trace needs n+2 valuations (0 through n+1).
        for (unsigned k = 0; k <= depth_ + 1; ++k) {
            for (const Flat& f : flat_) {
                const std::string name = step(f.name, k);
                if (declared_.count(name) != 0) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "unrolled name `" + name
                                    + "` collides with a rigid global symbol");
                    return nullptr;
                }
                declare(*model, name, f.sort);
            }
        }

        const auto atStep = [&](const H::ExprPtr& e, unsigned k) {
            std::unordered_map<std::string, std::string> map;
            for (const Flat& f : flat_) {
                map[f.name] = step(f.name, k);
                map[primeName(f.name)] = step(f.name, k + 1);
            }
            // An identified name resolves to the SAME step variable as the one
            // it was identified with, which is what makes them one variable.
            for (const auto& kv : alias_) {
                map[kv.first] = step(kv.second, k);
                map[primeName(kv.first)] = step(kv.second, k + 1);
            }
            return H::substituteIdents(e, map, sorts);
        };

        H::ExprPtr current;
        std::vector<H::ExprPtr> assumptions, reachable_terms, fairness_terms;
        for (const Condition& c : conditions_) {
            if (!c.selected) { continue; }
            const auto it = cond_e_.find(&c);
            if (it == cond_e_.end()) { continue; }
            if (c.keyword == "current") { current = it->second; }
            else if (c.keyword == "assumption") { assumptions.push_back(it->second); }
            else if (c.keyword == "reachable") { reachable_terms.push_back(it->second); }
            else if (c.keyword == "fairness") { fairness_terms.push_back(it->second); }
        }

        // A selected initiality condition C replaces IS; it is not an
        // additional invariant and it suppresses every flattened subsystem init.
        if (current) { add(*model, atStep(current, 0)); }
        else {
            for (const H::ExprPtr& f : flat_init_) { add(*model, atStep(f, 0)); }
        }
        for (const H::ExprPtr& f : flat_trans_) {
            for (unsigned k = 0; k <= depth_; ++k) { add(*model, atStep(f, k)); }
        }
        for (const H::ExprPtr& f : flat_inv_) {
            for (unsigned k = 0; k <= depth_; ++k) { add(*model, atStep(f, k)); }
        }
        for (const H::ExprPtr& f : assumptions) {
            for (unsigned k = 0; k <= depth_; ++k) { add(*model, atStep(f, k)); }
        }

        // Each reachable condition is its own eventuality. Add one disjunction
        // over time per condition; separate constraints then conjoin them while
        // still permitting their witnesses to occur at different steps.
        for (const H::ExprPtr& f : reachable_terms) {
            H::ExprPtr eventually;
            for (unsigned k = 0; k <= depth_; ++k) {
                H::ExprPtr v = atStep(f, k);
                eventually = eventually ? H::mkOp(H::Op::OR, {eventually, v}) : v;
            }
            add(*model, eventually);
        }

        // A selected fairness query has infinite-trace semantics. Enumerate
        // nonempty loops 0 <= l <= n with state(n+1) = state(l). Repeating
        // l..n then preserves every transition, invariant and assumption,
        // including formulas that mention primed inputs. Each fairness
        // condition must hold on the loop, not just in the finite prefix.
        if (!fairness_terms.empty()) {
            H::ExprPtr some_loop = H::mkBool(false);
            for (unsigned l = 0; l <= depth_; ++l) {
                H::ExprPtr loop = H::mkBool(true);
                for (const Flat& f : flat_) {
                    auto equal = H::mkOp(H::Op::EQ, {
                        H::mkIdent(step(f.name, depth_ + 1), f.sort),
                        H::mkIdent(step(f.name, l), f.sort)});
                    loop = H::mkOp(H::Op::AND, {loop, equal});
                }
                for (const auto& f : fairness_terms) {
                    H::ExprPtr seen = H::mkBool(false);
                    for (unsigned k = l; k <= depth_; ++k) {
                        seen = H::mkOp(H::Op::OR, {seen, atStep(f, k)});
                    }
                    loop = H::mkOp(H::Op::AND, {loop, seen});
                }
                some_loop = H::mkOp(H::Op::OR, {some_loop, loop});
            }
            add(*model, some_loop);
        }

        Uir::EncodingChoice ch;
        ch.site       = file_;
        ch.unified_op = "transition-system";
        ch.strategy   = fairness_terms.empty() ? "bmc-unrolling" : "bmc-fair-lasso";
        Uir::Fidelity::Bound b;
        b.kind  = Uir::Fidelity::Bound::BMC_DEPTH;
        b.value = static_cast<int64_t>(depth_);
        b.site  = file_;
        ch.fidelity = Uir::Fidelity::underApprox(b);
        ch.rationale =
            "a MoXI finite-trace query unrolled with n=" + std::to_string(depth_)
            + "; each selected :reachable is a separate eventuality, :current replaces "
              "the system initial predicate, and primed formulas at n use state n+1. "
              "SAT is a real bounded witness; UNSAT means no witness at this bound and "
              "must not be reported as globally unreachable";
        if (!fairness_terms.empty()) {
            ch.rationale = "a MoXI infinite-trace query restricted to lassos with "
                "n=" + std::to_string(depth_) + "; state n+1 equals one complete "
                "state l in 0..n, including inputs and flattened locals. Each "
                "selected :fairness holds at least once in l..n. :reachable may "
                "hold in the prefix; :current replaces initialization. SAT is "
                "a real infinite witness; UNSAT excludes only these bounded "
                "lassos, not longer or nonperiodic witnesses.";
        }
        report.addChoice(std::move(ch));
        return model;
    }

    static std::string step(const std::string& base, unsigned k) {
        return appendSymbolSuffix(base, "@" + std::to_string(k));
    }
    void declare(H::ConstraintModel& m, const std::string& name, const H::Sort& s) {
        if (!declared_.insert(name).second) { return; }
        H::VarDecl d;
        d.name = name;
        d.sort = s;
        m.decls.push_back(std::move(d));
    }
    static void add(H::ConstraintModel& m, const H::ExprPtr& e) {
        H::Constraint c;
        c.formula = e;
        m.constraints.push_back(c);
    }

    static constexpr const char* kPrimeSuffix = ".moxi.next";

    /** A named `check-system` condition from the published grammar. */
    struct Condition {
        std::string keyword;   // reachable | assumption | fairness | current
        std::string name;
        std::string term;
        bool        selected;  // named by the query, so actually checked
    };

    std::string src_, file_;
    unsigned    depth_;
    std::string query_selector_;
    std::optional<std::size_t> check_index_;
    bool flat_datatype_constructors_ = false;
    std::vector<SourceModule::SourceRewrite> source_rewrites_;

    std::vector<std::string> environment_;
    std::vector<std::string> system_bodies_, check_bodies_;
    std::unordered_set<std::string> defined_functions_;
    bool has_rigid_free_symbols_ = false;
    bool has_multi_query_group_ = false;
    std::vector<H::VarDecl> global_decls_;
    std::vector<H::FunDecl> global_funs_;
    std::vector<H::DatatypeDecl> global_datatypes_;
    unsigned sort_probe_ = 0;

    std::unordered_map<std::string, SystemDef> systems_;
    bool module_mode_ = false;
    std::unordered_map<std::string, std::string> module_versions_;
    std::vector<std::string> order_;
    /** The system `check-system` names: the root of the flattening. */
    std::string root_;

    std::vector<VarDeclText> chk_inputs_, chk_outputs_, chk_locals_;
    std::vector<Condition>   conditions_;
    std::vector<std::string> queries_;
    std::unordered_map<const Condition*, H::ExprPtr> cond_e_;

    /** The flattened model: every instance's variables under a name unique to
     *  the instance, and the three relations conjoined across the hierarchy. */
    std::vector<Flat> flat_;
    std::unordered_set<std::string> flat_seen_;
    std::vector<H::ExprPtr> flat_init_, flat_trans_, flat_inv_;

    /** check-system name -> the system variable it IS. */
    std::unordered_map<std::string, std::string> alias_;
    std::unordered_map<std::string, std::string> alias_sort_text_;
    std::unordered_set<std::string> declared_;
};

class MoxiLanguage : public Language {
public:
    ModuleOutcome parseModule(const SourceUnit& unit) override {
        return parseModule(unit, ParseOptions{});
    }

    ModuleOutcome parseModule(const SourceUnit& unit, const ParseOptions& opts) override {
        ModuleOutcome out;
        for (const auto& option : opts.options) {
            if (option.first != "flat_datatype_constructors") {
                out.diagnostics.error(ErrorCode::E_PARSE, "unknown MoXI module reader option: " + option.first);
                return out;
            }
        }
        bool flat = false;
        if (!flatDatatypeOption(opts, flat, out.diagnostics)) { return out; }
        std::string source;
        if (!readModuleSource(unit, source, out.diagnostics)) { return out; }
        MoxiParser parser(source, unit.main_path.empty() ? unit.display_name : unit.main_path,
                          0, "", std::nullopt, flat);
        out.module = parser.parseModule(out.diagnostics);
        return out;
    }

    MoxiLanguage() {
        coverage_.total = 13;
        coverage_.supported = 12;
        coverage_.missing = {
            "simultaneous grouped-query results sharing rigid interpretations",
        };
    }

    std::string id() const override { return "moxi"; }
    std::string displayName() const override { return "MoXI"; }
    std::string version() const override { return "1"; }
    std::vector<std::string> extensions() const override { return {".moxi", ".mxi"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    double sniff(std::string_view head) const override {
        return head.find("define-system") != std::string_view::npos ? 0.95 : 0.0;
    }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) override {
        ParseOutcome out;
        bool flat = false;
        if (!flatDatatypeOption(opts, flat, out.diagnostics)) { return out; }
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
        const auto it = opts.options.find("bmc_depth");
        if (it == opts.options.end()) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "no unrolling depth: pass bmc_depth=<k>. There is "
                                  "deliberately no default, because the depth is the "
                                  "bound the translation's fidelity is stated against");
            return out;
        }
        char* end = nullptr;
        errno = 0;
        const long long k = std::strtoll(it->second.c_str(), &end, 10);
        if (errno == ERANGE || end == it->second.c_str() || *end != '\0') {
            out.diagnostics.error(ErrorCode::E_PARSE,
                                  "bmc_depth must be a base-10 integer");
            return out;
        }
        if (k < 0) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "bmc_depth must not be negative");
            return out;
        }
        if (static_cast<unsigned long long>(k)
            >= static_cast<unsigned long long>(std::numeric_limits<unsigned>::max())) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "bmc_depth is too large for the finite-trace unroller");
            return out;
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            std::optional<std::size_t> check_index;
            const auto check_it = opts.options.find("check_index");
            if (check_it != opts.options.end()) {
                char* check_end = nullptr;
                errno = 0;
                const unsigned long long value =
                    std::strtoull(check_it->second.c_str(), &check_end, 10);
                if (errno == ERANGE || check_end == check_it->second.c_str()
                    || *check_end != '\0' || check_it->second.front() == '-') {
                    out.diagnostics.error(ErrorCode::E_PARSE,
                                          "check_index must be a non-negative base-10 integer");
                    return out;
                }
                if (value > std::numeric_limits<std::size_t>::max()) {
                    out.diagnostics.error(ErrorCode::E_PARSE,
                                          "check_index is too large");
                    return out;
                }
                check_index = static_cast<std::size_t>(value);
            }
            const auto query_it = opts.options.find("query");
            const std::string query = query_it == opts.options.end()
                ? std::string{} : query_it->second;
            MoxiParser p(src, name, static_cast<unsigned>(k), query, check_index, flat);
            out.model = p.parse(out.diagnostics, out.report);
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "moxi", out.report.fidelity()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("moxi frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkMoxiLanguage() { return std::make_shared<MoxiLanguage>(); }

} // namespace SOMTParser::Lang
