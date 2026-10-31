/* -*- Source -*-
 * VMT-LIB frontend — bounded model checking of an SMT-level transition system.
 *
 * The format is docs/languages/vmt-lib.md; its `implicit-constraints` block is
 * the specification this file implements, and each entry has a fixture in
 * languages/vmt/instances.
 *
 * **The obligation that makes this format dangerous.** A VMT file is a legal
 * SMT-LIB script throughout -- every VMT construct is an `!` attribute on a
 * term -- so a plain SMT-LIB reader parses it, ignores the transition
 * structure, and produces a one-step formula that is not the model. That is not
 * a hypothetical: run the SMT-LIB baseline over a VMT file and it preserves
 * the `define-fun` bodies, but emits no time frames or reachability query.
 * Definitions alone do not assert the VMT initial state or transition relation.
 *
 * BTOR2 and AIGER fail loudly under the wrong reader. VMT-LIB fails silently
 * and produces a well-formed script, which is why the shape has to be extracted
 * before the term language is parsed rather than recovered afterwards.
 *
 * **The other obligations**, each a wrong answer rather than a missing feature:
 *
 *   * a variable **with** `:next` is a state variable and the variable it names
 *     is its next-step copy -- and that named variable is then NOT an
 *     independent free variable of the model. Treating it as one gives the
 *     unrolling twice as many degrees of freedom as the system has;
 *   * a variable with **no** `:next` is an INPUT, fresh at every step, not a
 *     state that persists;
 *   * **`:trans` is the whole transition relation.** Unlike BTOR2 and AIGER
 *     there is no per-variable frame default to add: a state variable the
 *     formula does not mention is unconstrained across the step, and adding
 *     `s' = s` for it would be inventing a constraint the file does not state;
 *   * a `:invar-property` asks reachability of its NEGATION, so the unrolling
 *     searches for a state violating it. Asserting it positively asks the
 *     opposite question.
 *
 * The command and annotation structure is traversed as S-expressions, including
 * nested annotated terms and multiple attributes. Terms are then handed to the
 * engine's parser and lifted with Lower::ParserToHir, so the term language is
 * the real one rather than a subset re-implemented here.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/vmt.h"

#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/frontend/parser.h"

#include <cerrno>
#include <cctype>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <limits>
#include <memory>
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

/** One `(! <term> :<key> <value>)` found in the file. */
struct Annotated {
    std::string term;      // the term's source text
    std::string key;       // "next", "init", "trans", "invar-property", ...
    std::string value;     // empty for a valueless, non-VMT attribute
};

struct Span {
    std::size_t begin = 0;
    std::size_t end = 0;
};

/** The index just past the s-expression starting at @p open, which must be a
 *  `(`. Returns npos when the parentheses do not balance. */
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
        if (in_bar)    { if (c == '|') { in_bar = false; }    continue; }
        if (c == '"')  { in_string = true; continue; }
        if (c == '|')  { in_bar = true; continue; }
        if (c == ';')  { while (i < s.size() && s[i] != '\n') { ++i; } continue; }
        if (c == '(')  { ++depth; }
        else if (c == ')') {
            --depth;
            if (depth == 0) { return i + 1; }
        }
    }
    return std::string::npos;
}

/** Strip `;` comments so the lexical scan does not read an annotation out of
 *  one. Kept length-preserving so reported offsets stay meaningful. */
std::string blankComments(std::string s) {
    bool in_string = false, in_bar = false;
    for (std::size_t i = 0; i < s.size(); ++i) {
        const char c = s[i];
        if (in_string) {
            if (c == '"' && i + 1 < s.size() && s[i + 1] == '"') { ++i; continue; }
            if (c == '"') { in_string = false; }
            continue;
        }
        if (in_bar)    { if (c == '|') { in_bar = false; }    continue; }
        if (c == '"')  { in_string = true; continue; }
        if (c == '|')  { in_bar = true; continue; }
        if (c == ';') {
            while (i < s.size() && s[i] != '\n') { s[i] = ' '; ++i; }
        }
    }
    return s;
}

void skipSpace(const std::string& s, std::size_t& p, std::size_t stop) {
    while (p < stop && std::isspace(static_cast<unsigned char>(s[p]))) { ++p; }
}

std::size_t scanAtom(const std::string& s, std::size_t p, std::size_t stop) {
    if (p >= stop) { return std::string::npos; }
    if (s[p] == '|') {
        for (std::size_t i = p + 1; i < stop; ++i) {
            if (s[i] == '|') { return i + 1; }
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

bool listItems(const std::string& s, Span list, std::vector<Span>& out) {
    if (list.begin >= list.end || s[list.begin] != '(' || s[list.end - 1] != ')') {
        return false;
    }
    std::size_t p = list.begin + 1;
    const std::size_t stop = list.end - 1;
    while (true) {
        skipSpace(s, p, stop);
        if (p == stop) { return true; }
        const std::size_t end = scanExpr(s, p, stop);
        if (end == std::string::npos) { return false; }
        out.push_back({p, end});
        p = end;
    }
}

std::string textOf(const std::string& s, Span span) {
    return s.substr(span.begin, span.end - span.begin);
}

bool isAtom(const std::string& s, Span span) {
    return span.begin < span.end && s[span.begin] != '(';
}

std::string canonicalSymbol(std::string symbol) {
    if (symbol.size() >= 2 && symbol.front() == '|' && symbol.back() == '|') {
        return symbol.substr(1, symbol.size() - 2);
    }
    return symbol;
}

bool parseNonnegative(const std::string& text, unsigned long long& value) {
    if (text.empty()) { return false; }
    for (const char c : text) {
        if (!std::isdigit(static_cast<unsigned char>(c))) { return false; }
    }
    errno = 0;
    char* end = nullptr;
    const unsigned long long parsed = std::strtoull(text.c_str(), &end, 10);
    if (errno == ERANGE || end == text.c_str() || *end != '\0' || text.front() == '-') {
        return false;
    }
    value = parsed;
    return true;
}

void collectIdents(const H::ExprPtr& e, std::unordered_set<std::string>& out) {
    if (!e) { return; }
    if (e->kind == H::ExprKind::IDENT) { out.insert(e->name); }
    for (const H::ExprPtr& a : e->args) { collectIdents(a, out); }
}

H::ExprPtr conjoin(const std::vector<H::ExprPtr>& terms) {
    if (terms.empty()) { return H::mkBool(true); }
    H::ExprPtr out = terms.front();
    for (std::size_t i = 1; i < terms.size(); ++i) {
        out = H::mkOp(H::Op::AND, {out, terms[i]});
    }
    return out;
}

class VmtParser {
public:
    VmtParser(std::string src, std::string file, unsigned depth,
              std::optional<std::size_t> check_index)
        : src_(std::move(src)), file_(std::move(file)), depth_(depth),
          check_index_(check_index) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        const std::string clean = blankComments(src_);
        if (!extract(clean, diags)) { return nullptr; }
        return build(diags, report);
    }

private:
    bool walkAnnotations(const std::string& s, Span expr, Uir::Diagnostics& diags) {
        if (isAtom(s, expr)) { return true; }
        std::vector<Span> items;
        if (!listItems(s, expr, items)) {
            diags.error(ErrorCode::E_PARSE, "malformed s-expression in VMT input");
            return false;
        }
        if (!items.empty() && isAtom(s, items[0]) && textOf(s, items[0]) == "!") {
            if (items.size() < 3) {
                diags.error(ErrorCode::E_PARSE, "an annotated term needs at least one attribute");
                return false;
            }
            std::size_t i = 2;
            while (i < items.size()) {
                if (!isAtom(s, items[i])) {
                    diags.error(ErrorCode::E_PARSE, "an annotation attribute must be a :keyword");
                    return false;
                }
                const std::string keyword = textOf(s, items[i]);
                if (keyword.size() < 2 || keyword.front() != ':') {
                    diags.error(ErrorCode::E_PARSE, "an annotation attribute must be a :keyword");
                    return false;
                }
                Annotated a;
                a.term = textOf(s, items[1]);
                a.key = keyword.substr(1);
                ++i;
                if (i < items.size()
                    && !(isAtom(s, items[i]) && textOf(s, items[i]).front() == ':')) {
                    a.value = textOf(s, items[i]);
                    ++i;
                }
                annots_.push_back(std::move(a));
            }
        }
        for (const Span item : items) {
            if (!isAtom(s, item) && !walkAnnotations(s, item, diags)) { return false; }
        }
        return true;
    }

    /** Parse top-level commands and recursively find every annotated subterm. */
    bool extract(const std::string& s, Uir::Diagnostics& diags) {
        std::size_t p = 0;
        bool saw_terminal_assert = false;
        std::string disallowed_command;
        while (true) {
            skipSpace(s, p, s.size());
            if (p == s.size()) { break; }
            if (s[p] != '(') {
                diags.error(ErrorCode::E_PARSE, "VMT input contains text outside a command");
                return false;
            }
            const std::size_t end = matchParen(s, p);
            if (end == std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "unbalanced parentheses in VMT input");
                return false;
            }
            const Span command{p, end};
            std::vector<Span> items;
            if (!listItems(s, command, items) || items.empty() || !isAtom(s, items[0])) {
                diags.error(ErrorCode::E_PARSE, "malformed VMT command");
                return false;
            }
            const std::string head = textOf(s, items[0]);
            if (saw_terminal_assert) {
                diags.error(ErrorCode::E_PARSE, "(assert true) must be the final VMT command");
                return false;
            }
            const bool declaration = head == "set-logic" || head == "declare-sort"
                                  || head == "define-sort" || head == "declare-fun"
                                  || head == "declare-const" || head == "define-fun";
            if (head == "set-option") {
                // Solver options are operational metadata, not part of Sign,
                // Sen or Mod. They are legal VMT commands but do not enter the
                // semantic script used to elaborate annotated terms.
                if (items.size() != 3) {
                    diags.error(ErrorCode::E_PARSE, "set-option needs a keyword and value");
                    return false;
                }
            } else if (declaration) {
                environment_.push_back(textOf(s, command));
                if (head == "define-fun" && items.size() >= 2 && isAtom(s, items[1])) {
                    defined_functions_.insert(canonicalSymbol(textOf(s, items[1])));
                }
            } else if (head == "assert" && items.size() == 2
                       && isAtom(s, items[1]) && textOf(s, items[1]) == "true") {
                saw_terminal_assert = true;
            } else {
                if (disallowed_command.empty()) { disallowed_command = head; }
            }
            if (!walkAnnotations(s, command, diags)) { return false; }
            p = end;
        }
        if (annots_.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "no VMT annotations: this is a plain SMT-LIB script, and reading "
                        "it as a transition system would invent a structure it does not "
                        "have. Use --from smtlib2");
            return false;
        }
        if (!disallowed_command.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "command '" + disallowed_command
                        + "' is not allowed by VMT-LIB 0.1");
            return false;
        }
        return true;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        // Classify the variables. A `:next` annotation names a pair; the named
        // variable is the next-step copy and is NOT independent.
        std::vector<std::pair<std::string, std::string>> next_annotations;
        std::vector<std::string> init_terms, trans_terms, props;
        std::vector<unsigned long long> prop_ids;
        std::unordered_set<unsigned long long> property_ids;
        for (const Annotated& a : annots_) {
            if (a.key == "next") {
                if (a.value.empty()) {
                    diags.error(ErrorCode::E_PARSE, ":next requires a variable name");
                    return nullptr;
                }
                next_annotations.emplace_back(a.term, a.value);
            } else if (a.key == "init") {
                if (a.value != "true") {
                    diags.error(ErrorCode::E_PARSE, ":init must have the dummy value true");
                    return nullptr;
                }
                init_terms.push_back(a.term);
            } else if (a.key == "trans") {
                if (a.value != "true") {
                    diags.error(ErrorCode::E_PARSE, ":trans must have the dummy value true");
                    return nullptr;
                }
                trans_terms.push_back(a.term);
            } else if (a.key == "invar") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            ":invar is not a VMT-LIB 0.1 annotation; interpreting it as "
                            "an invariant assumption would add source semantics");
                return nullptr;
            } else if (a.key == "invar-property") {
                unsigned long long id = 0;
                if (!parseNonnegative(a.value, id)) {
                    diags.error(ErrorCode::E_PARSE,
                                ":invar-property needs a non-negative integer id");
                    return nullptr;
                }
                if (!property_ids.insert(id).second) {
                    diags.error(ErrorCode::E_PARSE,
                                "duplicate :invar-property id " + std::to_string(id));
                    return nullptr;
                }
                prop_ids.push_back(id);
                props.push_back(a.term);
            } else if (a.key == "live-property" || a.key == "ltl-property"
                       || a.key == "ltlf-property") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "'" + a.key + "' is a liveness or temporal property, which "
                            "asks about infinite behaviour; a bounded unrolling cannot "
                            "express it, and translating it as a safety property would "
                            "answer a different question");
                return nullptr;
            }
        }
        if (props.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "no :invar-property: there is nothing to check, and an unrolling "
                        "with no property asserted is trivially satisfiable");
            return nullptr;
        }
        if (check_index_ && *check_index_ >= props.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "check_index=" + std::to_string(*check_index_)
                            + " but the file declares "
                            + std::to_string(props.size())
                            + (props.size() == 1 ? " property" : " properties"));
            return nullptr;
        }

        // Parse the term language ONCE: the declarations, then one assertion
        // per annotated formula, in a fixed order so the lifted constraints can
        // be picked apart by position.
        std::ostringstream script;
        for (const std::string& d : environment_) { script << d << "\n"; }
        std::vector<std::pair<const char*, const std::string*>> ordered;
        for (const std::string& t : init_terms)  { ordered.emplace_back("init", &t); }
        for (const std::string& t : trans_terms) { ordered.emplace_back("trans", &t); }
        for (const std::string& t : props)       { ordered.emplace_back("prop", &t); }
        for (const auto& o : ordered) { script << "(assert " << *o.second << ")\n"; }

        ParserPtr engine = newParser();
        engine->getOptions()->setExpandFunctions(true);
        try {
            if (!engine->parseStr(script.str())) {
                diags.error(ErrorCode::E_PARSE,
                            "the annotated terms are not a well-formed SMT-LIB script");
                return nullptr;
            }
        } catch (const std::exception& e) {
            diags.error(ErrorCode::E_PARSE,
                        std::string("the annotated terms did not parse: ") + e.what());
            return nullptr;
        }

        H::ConstraintModel lifted;
        Lower::ParserToHir up(engine);
        if (!up.lift(lifted, diags)) { return nullptr; }
        if (lifted.constraints.size() < ordered.size()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "the term parser returned fewer formulas than were annotated");
            return nullptr;
        }
        // ParserToHir emits define-fun equations before assertions. Calls in
        // the appended assertions were explicitly expanded above, so only the
        // final |ordered| constraints are the VMT formulas to unroll.
        const std::size_t formula_begin = lifted.constraints.size() - ordered.size();

        // Sorts, by declared name.
        std::unordered_map<std::string, H::Sort> sorts;
        std::unordered_map<std::string, std::string> declared_by_symbol;
        for (const H::VarDecl& d : lifted.decls) {
            sorts[d.name] = d.sort;
            declared_by_symbol[canonicalSymbol(d.name)] = d.name;
        }

        std::unordered_map<std::string, std::string> next_of;   // state -> next copy
        std::unordered_set<std::string> next_copies;
        for (const auto& raw : next_annotations) {
            if (!raw.first.empty() && raw.first.front() == '(') {
                diags.error(ErrorCode::E_PARSE, ":next must annotate a declared variable");
                return nullptr;
            }
            if (!raw.second.empty() && raw.second.front() == '(') {
                diags.error(ErrorCode::E_PARSE, ":next must name a declared variable");
                return nullptr;
            }
            const auto ci = declared_by_symbol.find(canonicalSymbol(raw.first));
            const auto ni = declared_by_symbol.find(canonicalSymbol(raw.second));
            if (ci == declared_by_symbol.end() || ni == declared_by_symbol.end()) {
                diags.error(ErrorCode::E_PARSE,
                            ":next must pair two declared, nullary variables");
                return nullptr;
            }
            if (ci->second == ni->second) {
                diags.error(ErrorCode::E_PARSE, ":next cannot map a variable to itself");
                return nullptr;
            }
            if (!H::sameSort(sorts[ci->second], sorts[ni->second])) {
                diags.error(ErrorCode::E_PARSE, ":next variables must have the same sort");
                return nullptr;
            }
            if (!next_of.emplace(ci->second, ni->second).second) {
                diags.error(ErrorCode::E_PARSE,
                            "a state variable has more than one :next annotation");
                return nullptr;
            }
            if (!next_copies.insert(ni->second).second) {
                diags.error(ErrorCode::E_PARSE,
                            "a next-state variable is paired with more than one state variable");
                return nullptr;
            }
        }
        for (const auto& pair : next_of) {
            if (next_copies.count(pair.first) != 0) {
                diags.error(ErrorCode::E_PARSE,
                            "a variable cannot be both current-state and next-state");
                return nullptr;
            }
        }

        auto model = std::make_shared<H::ConstraintModel>();
        model->datatypes = lifted.datatypes;
        for (const H::FunDecl& f : lifted.funs) {
            if (defined_functions_.count(canonicalSymbol(f.name)) == 0) {
                model->funs.push_back(f);
            }
        }
        // Inputs are everything that is neither a state nor a next copy.
        std::vector<std::string> states, inputs;
        for (const H::VarDecl& d : lifted.decls) {
            if (next_of.count(d.name) != 0) { states.push_back(d.name); }
            else if (next_copies.count(d.name) == 0) { inputs.push_back(d.name); }
        }

        std::unordered_set<std::string> input_set(inputs.begin(), inputs.end());
        const auto validateStateFormula = [&](const char* label, const H::ExprPtr& formula) {
            std::unordered_set<std::string> ids;
            collectIdents(formula, ids);
            for (const std::string& id : ids) {
                if (next_copies.count(id) != 0 || input_set.count(id) != 0) {
                    diags.error(ErrorCode::E_PARSE,
                                std::string(label) + " may contain only current-state variables; '"
                                + id + "' is a "
                                + (next_copies.count(id) != 0 ? "next-state" : "input")
                                + " variable");
                    return false;
                }
            }
            return true;
        };

        std::size_t check_at = formula_begin;
        for (std::size_t i = 0; i < init_terms.size(); ++i, ++check_at) {
            if (!validateStateFormula(":init", lifted.constraints[check_at].formula)) {
                return nullptr;
            }
        }
        check_at += trans_terms.size();
        for (std::size_t i = 0; i < props.size(); ++i, ++check_at) {
            if (!validateStateFormula(":invar-property",
                                      lifted.constraints[check_at].formula)) {
                return nullptr;
            }
        }

        for (unsigned k = 0; k <= depth_; ++k) {
            for (const std::string& s : states) {
                declare(*model, step(s, k), sorts[s]);
            }
            for (const std::string& i : inputs) {
                declare(*model, step(i, k), sorts[i]);
            }
        }

        // Rename a formula's variables into a step. A state's next copy at step
        // k is the state at step k+1, which is the whole of what `:next` means.
        const auto atStep = [&](const H::ExprPtr& e, unsigned k) {
            std::unordered_map<std::string, std::string> map;
            for (const std::string& s : states) {
                map[s] = step(s, k);
                map[next_of[s]] = step(s, k + 1);
            }
            for (const std::string& i : inputs) { map[i] = step(i, k); }
            return H::substituteIdents(e, map, sorts);
        };

        std::size_t at = formula_begin;
        for (std::size_t i = 0; i < init_terms.size(); ++i, ++at) {
            add(*model, atStep(lifted.constraints[at].formula, 0));
        }
        const std::size_t trans_begin = at;
        at = trans_begin + trans_terms.size();

        // Build one path prefix per possible witness depth. Requiring all
        // transitions through depth_ globally would silently require a real
        // shorter counterexample to be extendible to depth_, which is not part
        // of finite-path reachability when :trans has a dead end.
        std::vector<H::ExprPtr> prefixes(depth_ + 1);
        prefixes[0] = H::mkBool(true);
        for (unsigned k = 1; k <= depth_; ++k) {
            std::vector<H::ExprPtr> extend{prefixes[k - 1]};
            for (std::size_t i = 0; i < trans_terms.size(); ++i) {
                // :trans IS the whole relation. No per-variable frame is added.
                extend.push_back(atStep(lifted.constraints[trans_begin + i].formula,
                                        k - 1));
            }
            prefixes[k] = conjoin(extend);
        }

        // The property asks reachability of its NEGATION. Each disjunct is a
        // complete finite source path ending in a violating state. The default
        // query aggregates every property as "find any violation"; with
        // check_index the query covers ONE property, so a harness running the
        // file once per index gets an independent verdict per property id.
        const std::size_t prop_first = check_index_.value_or(0);
        const std::size_t prop_last  = check_index_ ? prop_first + 1 : props.size();
        H::ExprPtr any;
        for (std::size_t i = prop_first; i < prop_last; ++i) {
            for (unsigned k = 0; k <= depth_; ++k) {
                H::ExprPtr viol =
                    H::mkOp(H::Op::NOT, {atStep(lifted.constraints[at + i].formula, k)});
                H::ExprPtr candidate = H::mkOp(H::Op::AND, {prefixes[k], viol});
                any = any ? H::mkOp(H::Op::OR, {any, candidate}) : candidate;
            }
        }
        add(*model, any);

        Uir::EncodingChoice ch;
        ch.site       = file_;
        ch.unified_op = "transition-system";
        ch.strategy   = "bmc-unrolling";
        Uir::Fidelity::Bound b;
        b.kind  = Uir::Fidelity::Bound::BMC_DEPTH;
        b.value = static_cast<int64_t>(depth_);
        b.site  = file_;
        ch.fidelity = Uir::Fidelity::underApprox(b);
        ch.rationale =
            "a VMT-LIB transition system unrolled to depth " + std::to_string(depth_)
            + "; the :invar-property is asserted NEGATED, so SAT is a real state "
              "violating it and UNSAT means NO VIOLATION WITHIN " + std::to_string(depth_)
            + " STEPS, which must not be reported as safe";
        if (check_index_) {
            ch.rationale +=
                "; check_index=" + std::to_string(*check_index_)
                + " restricts this query to :invar-property id "
                + std::to_string(prop_ids[prop_first])
                + " only -- the file's other "
                + std::to_string(props.size() - 1)
                + " propert" + (props.size() == 2 ? "y is" : "ies are")
                + " separate queries with their own verdicts, not part of this one";
        }
        report.addChoice(std::move(ch));
        if (init_terms.empty() || trans_terms.empty()) {
            Uir::EncodingChoice defaults;
            defaults.site = file_;
            defaults.unified_op = "transition-default";
            defaults.strategy = "empty-conjunction-true";
            defaults.fidelity = Uir::Fidelity::exact();
            defaults.rationale =
                "VMT reference readers conjoin all :init and :trans terms, so an "
                "absent section is the empty conjunction true; no frame equation is added";
            report.addChoice(std::move(defaults));
        }
        return model;
    }

    static std::string step(const std::string& base, unsigned k) {
        if (base.size() >= 2 && base.front() == '|' && base.back() == '|') {
            return "|" + base.substr(1, base.size() - 2) + "@" + std::to_string(k) + "|";
        }
        return base + "@" + std::to_string(k);
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


    std::string src_, file_;
    unsigned    depth_;
    std::optional<std::size_t> check_index_;
    std::vector<Annotated> annots_;
    std::vector<std::string> environment_;
    std::unordered_set<std::string> defined_functions_;
    std::unordered_set<std::string> declared_;
};

class VmtLanguage : public Language {
public:
    VmtLanguage() {
        coverage_.total = 9;
        coverage_.supported = 8;
        coverage_.missing = {
            "liveness and LTL properties",
        };
    }

    std::string id() const override { return "vmt"; }
    std::string displayName() const override { return "VMT-LIB"; }
    std::string version() const override { return "1"; }
    std::vector<std::string> extensions() const override { return {".vmt"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    /** A VMT file is also a legal SMT-LIB script, so the extension cannot be
     *  the whole story if anyone names one `.smt2`. The annotations are what
     *  distinguish it. */
    double sniff(std::string_view head) const override {
        return head.find(":invar-property") != std::string_view::npos
                   || head.find(":trans") != std::string_view::npos
               ? 0.95 : 0.0;
    }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) override {
        ParseOutcome out;
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
        errno = 0;
        char* end = nullptr;
        for (const char c : it->second) {
            if (!std::isdigit(static_cast<unsigned char>(c))) {
                out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                      "bmc_depth must be an unsigned integer in range");
                return out;
            }
        }
        const unsigned long long k = std::strtoull(it->second.c_str(), &end, 10);
        if (it->second.empty() || errno == ERANGE || end == it->second.c_str()
            || *end != '\0' || k > std::numeric_limits<unsigned>::max()) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "bmc_depth must be an unsigned integer in range");
            return out;
        }

        // Without a selector the query aggregates every :invar-property as
        // "find any violation"; check_index=<n> restricts it to one property
        // (file order), which is how a harness gets an independent verdict
        // per property id.
        std::optional<std::size_t> check_index;
        const auto check_it = opts.options.find("check_index");
        if (check_it != opts.options.end()) {
            errno = 0;
            char* check_end = nullptr;
            for (const char c : check_it->second) {
                if (!std::isdigit(static_cast<unsigned char>(c))) {
                    out.diagnostics.error(ErrorCode::E_PARSE,
                                          "check_index must be a non-negative base-10 integer");
                    return out;
                }
            }
            const unsigned long long value =
                std::strtoull(check_it->second.c_str(), &check_end, 10);
            if (check_it->second.empty() || errno == ERANGE
                || check_end == check_it->second.c_str() || *check_end != '\0'
                || value > std::numeric_limits<std::size_t>::max()) {
                out.diagnostics.error(ErrorCode::E_PARSE,
                                      "check_index must be a non-negative base-10 integer");
                return out;
            }
            check_index = static_cast<std::size_t>(value);
        }

        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            VmtParser p(src, name, static_cast<unsigned>(k), check_index);
            out.model = p.parse(out.diagnostics, out.report);
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "vmt", out.report.fidelity()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("vmt frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkVmtLanguage() { return std::make_shared<VmtLanguage>(); }

} // namespace SOMTParser::Lang
