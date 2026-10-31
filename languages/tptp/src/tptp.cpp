/* -*- Source -*-
 * TPTP frontend, CNF and FOF.
 *
 * The format is docs/languages/tptp.md; its `implicit-constraints` block is the
 * specification this file implements, and each entry has a fixture in
 * languages/tptp/instances.
 *
 * **The first obligation inverts every answer if it is missed**, and it is one
 * line of code:
 *
 *     all formulas with role `conjecture` are conjoined and NEGATED once.
 *
 * `axioms |= C1 AND ... AND Cn` is decided by refuting
 * `axioms AND NOT(C1 AND ... AND Cn)`. A frontend that negates each goal as a
 * separate constraint requires every goal to fail in one model -- and nothing
 * downstream can tell, because both formulas are well-formed and both get an
 * answer. `negated_conjecture` contributes itself, already negated, so the two
 * roles must not share a branch.
 *
 * The second is the lexical rule that carries the binding structure: **variables
 * are upper-case**, constants and functors lower-case. A reader that ignores
 * case turns bound variables into constants and produces a different formula,
 * usually a trivially satisfiable one.
 *
 * The third is the sort discipline. An untyped FOF term lives in a SINGLE
 * unsorted universe, so the translation introduces one uninterpreted sort and
 * puts every term in it. Guessing sorts from usage would invent distinctions the
 * logic does not have -- this is cluster G's shape, and the first language in
 * tree to use it.
 *
 * TFF and TXF keep that discipline honest rather than replacing it. `$i` is the
 * SAME uninterpreted sort the untyped path uses, so a mixed FOF/TFF file is one
 * problem; declared signatures are checked at every application; and undeclared
 * symbols get TPTP's default typing, recorded as an assumption that a
 * conflicting later declaration turns into a type error. TXF adds the FOOL
 * conflation ($o-sorted terms are formulas and vice versa), `$ite`, and
 * `$let` -- the last inlined at parse time, so a recursive definition under it
 * is refused rather than unfolded forever. THF is routed through a separate
 * typed strong-Henkin encoding; constructs outside its supported fragment are
 * refused rather than erased.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/tptp.h"
#include "somtparser/core/kind.h"
#include "rename_symbols.h"
#include "strong_henkin_encoding.h"
#include "thf_expression_parser.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <deque>
#include <filesystem>
#include <fstream>
#include <memory>
#include <new>
#include <optional>
#include <sstream>
#include <string>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

/** The single unsorted universe of untyped FOF. `$i` is TPTP's own name for it. */
const char* kUniverse = "$i";

bool containsStatement(const std::string& source, const std::string& language) {
    std::size_t offset = 0;
    std::size_t paren_depth = 0;
    char quote = 0;
    bool escaped = false;
    while (offset < source.size()) {
        const char c = source[offset];
        if (quote != 0) {
            if (escaped) { escaped = false; }
            else if (c == '\\') { escaped = true; }
            else if (c == quote) {
                if (offset + 1 < source.size() && source[offset + 1] == quote) {
                    offset += 2;
                    continue;
                }
                quote = 0;
            }
            ++offset;
            continue;
        }
        if (c == '%') {
            while (offset < source.size() && source[offset] != '\n') { ++offset; }
            continue;
        }
        if (c == '/' && offset + 1 < source.size() && source[offset + 1] == '*') {
            const auto end = source.find("*/", offset + 2);
            if (end == std::string::npos) { return false; }
            offset = end + 2;
            continue;
        }
        if (c == '\'' || c == '"') {
            quote = c;
            ++offset;
            continue;
        }
        if (paren_depth == 0
            && (std::isalpha(static_cast<unsigned char>(c)) || c == '_')) {
            const std::size_t begin = offset++;
            while (offset < source.size()
                   && (std::isalnum(static_cast<unsigned char>(source[offset]))
                       || source[offset] == '_')) { ++offset; }
            if (source.compare(begin, offset - begin, language) == 0) {
                std::size_t lookahead = offset;
                while (lookahead < source.size()
                       && std::isspace(static_cast<unsigned char>(source[lookahead]))) {
                    ++lookahead;
                }
                if (lookahead < source.size() && source[lookahead] == '(') { return true; }
            }
            continue;
        }
        if (c == '(') { ++paren_depth; }
        else if (c == ')' && paren_depth > 0) { --paren_depth; }
        ++offset;
    }
    return false;
}

struct Tok {
    enum Kind { IDENT, VAR, DISTINCT_OBJECT, NUMBER, PUNCT, INVALID, END } kind = END;
    std::string text;
    int line = 1;
    bool single_quoted = false;
};

class Lexer {
public:
    Lexer(std::string src, int first_line) : s_(std::move(src)), line_(first_line) {}

    Tok next() {
        skip();
        Tok t;
        t.line = line_;
        if (i_ >= s_.size()) { t.kind = Tok::END; return t; }
        const char c = s_[i_];
        // **The lexical rule that IS the binding structure.** Upper case opens a
        // variable; lower case a constant, functor or predicate.
        if (std::isupper(static_cast<unsigned char>(c))) {
            t.kind = Tok::VAR;
            t.text = word();
            return t;
        }
        if (std::islower(static_cast<unsigned char>(c)) || c == '$') {
            t.kind = Tok::IDENT;
            t.text = word();
            return t;
        }
        if (std::isdigit(static_cast<unsigned char>(c))) {
            t.kind = Tok::NUMBER;
            const std::size_t start = i_++;
            while (i_ < s_.size()
                   && !std::isspace(static_cast<unsigned char>(s_[i_]))
                   && std::string("(),[]:=!&|~<>").find(s_[i_]) == std::string::npos) {
                ++i_;
            }
            t.text = s_.substr(start, i_ - start);
            return t;
        }
        if (c == '\'' || c == '"') {
            const char quote = c;
            ++i_;
            std::string out;
            bool escaped = false;
            while (i_ < s_.size()) {
                const char q = s_[i_++];
                if (escaped) {
                    if (q != quote && q != '\\') {
                        t.kind = Tok::INVALID;
                        t.text = "only the quote character and backslash may be escaped";
                        return t;
                    }
                    out += q;
                    escaped = false;
                } else if (q == '\\') {
                    escaped = true;
                } else if (q == quote) {
                    if (quote == '\'' && out.empty()) {
                        t.kind = Tok::INVALID;
                        t.text = "a single-quoted atomic word may not be empty";
                        return t;
                    }
                    t.kind = quote == '\'' ? Tok::IDENT : Tok::DISTINCT_OBJECT;
                    t.single_quoted = quote == '\'';
                    t.text = std::move(out);
                    return t;
                } else {
                    if (q == '\n' || q == '\r') {
                        t.kind = Tok::INVALID;
                        t.text = "quoted tokens may not contain a newline";
                        return t;
                    }
                    out += q;
                }
            }
            t.kind = Tok::INVALID;
            t.text = quote == '\'' ? "unterminated single-quoted atomic word"
                                    : "unterminated distinct object";
            return t;
        }
        if (c == '`') {
            const std::size_t start = i_++;
            if (i_ >= s_.size()
                || !std::isupper(static_cast<unsigned char>(s_[i_]))) {
                t.kind = Tok::INVALID;
                t.text = "a back-quoted atomic word is followed by an upper-case word";
                return t;
            }
            word();
            t.kind = Tok::IDENT;
            t.text = s_.substr(start, i_ - start);
            return t;
        }
        static const char* kMulti[] = {"<=>", "<~>", "~&", "~|", "=>", "<=", "!=", nullptr};
        for (int k = 0; kMulti[k] != nullptr; ++k) {
            const std::string m = kMulti[k];
            if (s_.compare(i_, m.size(), m) == 0) {
                i_ += m.size();
                t.kind = Tok::PUNCT;
                t.text = m;
                return t;
            }
        }
        ++i_;
        t.kind = Tok::PUNCT;
        t.text = std::string(1, c);
        return t;
    }

private:
    void skip() {
        while (i_ < s_.size()) {
            const char c = s_[i_];
            if (c == '\n') { ++line_; ++i_; }
            else if (std::isspace(static_cast<unsigned char>(c))) { ++i_; }
            else if (c == '%') { while (i_ < s_.size() && s_[i_] != '\n') { ++i_; } }
            else if (c == '/' && i_ + 1 < s_.size() && s_[i_ + 1] == '*') {
                i_ += 2;
                while (i_ + 1 < s_.size() && !(s_[i_] == '*' && s_[i_ + 1] == '/')) {
                    if (s_[i_] == '\n') { ++line_; }
                    ++i_;
                }
                i_ += 2;
            }
            else { return; }
        }
    }
    std::string word() {
        const std::size_t start = i_;
        while (i_ < s_.size()
               && (std::isalnum(static_cast<unsigned char>(s_[i_])) || s_[i_] == '_'
                   || s_[i_] == '$')) {
            ++i_;
        }
        return s_.substr(start, i_ - start);
    }
    std::string s_;
    std::size_t i_ = 0;
    int line_ = 1;
};

enum class SymbolUse { UNKNOWN, TERM, PREDICATE };

struct SignatureEntry {
    std::string source_name;
    std::string parse_name;
    std::string target_name;
    std::size_t arity = 0;
    SymbolUse use = SymbolUse::UNKNOWN;
    Uir::SourceLoc loc;
    /* TFF/TXF typing. When `has_type` is false the symbol is FOF-style: every
     * argument and an ordinary result is the universe `$i`, worked out from
     * `use` at emission. When true, `params` and `result` carry the real
     * signature -- either from a `type` declaration or from TPTP's default
     * typing, in which case `assumed` is set and a later declaration that
     * conflicts with the assumption is a type error (an identical one is legal
     * spec merging). */
    bool has_type = false;
    bool assumed = false;
    std::vector<H::Sort> params;
    H::Sort result;
};

/** A quantifier- or $let-bound variable: the renamed target and its sort. */
struct BoundVar {
    std::string target;
    H::Sort     sort;
};

/** One TXF `$let` definition. `param_sorts` and `result` come from the let's
 *  type part; `formals` and `body` are filled when the definition itself is
 *  parsed, which is also when `ready` flips. A reference to a non-ready entry
 *  is a direct or transitive self-reference, and inlining it would not
 *  terminate -- so it is refused by name. */
struct LetDef {
    std::vector<H::Sort> param_sorts;
    H::Sort result;
    std::vector<std::pair<std::string, H::Sort>> formals;
    H::ExprPtr body;
    bool ready = false;
};

struct IncludeSelection {
    std::unordered_set<std::string> requested;
    std::unordered_map<std::string, std::size_t> seen;
    Uir::SourceLoc loc;
};

class TptpParser {
public:
    TptpParser(std::string src, std::string file)
        : src_(std::move(src)), file_(std::move(file)) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        report_ = &report;
        model_ = std::make_shared<H::ConstraintModel>();
        if (!items(src_, file_, 0, diags)) { return nullptr; }
        // TPTP solves a problem only when ALL conjectures follow. Therefore the
        // refutation goal is A AND NOT(C1 AND ... AND Cn), not one top-level
        // NOT(Ci) constraint per conjecture (which would require every goal to
        // fail in the same model). Negated-conjecture CNF clauses are already
        // the clausification of a negated goal and were added as written.
        if (!conjectures_.empty()) {
            H::ExprPtr all = conjectures_.front();
            for (std::size_t i = 1; i < conjectures_.size(); ++i) {
                all = H::mkOp(H::Op::AND, {all, conjectures_[i]}, all->loc);
            }
            H::Constraint goal;
            goal.loc = all->loc;
            goal.formula = H::mkOp(H::Op::NOT, {all}, all->loc);
            model_->constraints.push_back(std::move(goal));
        }
        if (!finalizeSignatureAndAxioms(diags)) { return nullptr; }
        // Signature declarations come first, as HirToParser needs the symbol to
        // exist before an application of it.
        for (const auto& [key, entry] : signature_) {
            H::FunDecl f;
            f.name = entry.target_name;
            if (entry.has_type) {
                // TFF/TXF symbols keep their real signature rather than the FOF
                // blanket $i. `$i` itself is shared with the untyped path by
                // name, so a mixed FOF/TFF file stays one problem.
                f.params = entry.params;
                f.result = entry.result;
            } else {
                f.params.assign(entry.arity, H::Sort::uninterpreted(kUniverse));
                f.result = entry.use == SymbolUse::PREDICATE
                               ? H::Sort::boolean()
                               : H::Sort::uninterpreted(kUniverse);
            }
            f.loc = entry.loc;
            model_->funs.push_back(std::move(f));
        }
        std::sort(model_->funs.begin(), model_->funs.end(),
                  [](const H::FunDecl& a, const H::FunDecl& b) { return a.name < b.name; });
        return model_;
    }

    bool hasPositiveConjecture() const noexcept { return has_positive_conjecture_; }
    // Parsing is complete before contract construction. Transfer its signature
    // rather than retaining a redundant copy of every high-arity domain.
    Uir::Sem::Signature takeSourceSignature() noexcept {
        return std::move(source_signature_);
    }
    std::vector<Uir::Sem::SymbolMapping> takeSymbolMap() noexcept {
        return std::move(symbol_map_);
    }
    std::vector<Uir::Sem::Sentence> takeTargetAxioms() noexcept {
        return std::move(target_axioms_);
    }

private:
    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = active_file_.empty() ? file_ : active_file_;
        l.line = line;
        l.column = 1;
        return l;
    }

    static Uir::SourceLoc at(const std::string& file, int line) {
        Uir::SourceLoc l;
        l.file = file;
        l.line = line;
        l.column = 1;
        return l;
    }

    /** Split the file into `name(...)` items terminated by `.` at depth zero. */
    bool items(const std::string& src, const std::string& file, int depth,
               Uir::Diagnostics& diags) {
        if (depth > 16) {
            diags.error(ErrorCode::E_PARSE, "include nesting is too deep", at(file, 1));
            return false;
        }
        std::size_t i = 0;
        int line = 1;
        std::string cur;
        int cur_line = 1;
        int paren = 0;
        int bracket = 0;
        char quote = '\0';
        bool escaped = false;
        while (i < src.size()) {
            const char c = src[i];
            // Comments are stripped HERE, in the splitter, rather than in the
            // formula lexer. A `%` comment can sit after an item's terminating
            // `.`, and the splitter -- not the lexer -- is what decides where
            // one item ends and the next begins: left in place, the trailing
            // comment becomes the first thing in the NEXT item's text and that
            // item fails to parse. A comment is also legal mid-item, between
            // the role and the formula.
            if (quote == '\0' && c == '%') {
                while (i < src.size() && src[i] != '\n') { ++i; }
                if (i < src.size()) { ++line; ++i; }
                continue;
            }
            if (quote == '\0' && c == '/' && i + 1 < src.size() && src[i + 1] == '*') {
                i += 2;
                while (i + 1 < src.size() && !(src[i] == '*' && src[i + 1] == '/')) {
                    if (src[i] == '\n') { ++line; }
                    ++i;
                }
                if (i + 1 >= src.size()) {
                    diags.error(ErrorCode::E_PARSE, "unterminated block comment",
                                at(file, line));
                    return false;
                }
                i += 2;
                continue;
            }
            if (c == '\n') { ++line; }
            if (cur.find_first_not_of(" \t\n\r") == std::string::npos
                && !std::isspace(static_cast<unsigned char>(c))) {
                cur_line = line;
            }
            if (quote != '\0') {
                if (escaped) {
                    escaped = false;
                } else if (c == '\\') {
                    escaped = true;
                } else if (c == quote) {
                    quote = '\0';
                }
            } else if (c == '\'' || c == '"') {
                quote = c;
            } else {
                if (c == '(') { ++paren; }
                else if (c == ')') { --paren; }
                else if (c == '[') { ++bracket; }
                else if (c == ']') { --bracket; }
                else if (c == '.' && paren == 0 && bracket == 0) {
                    if (!item(cur, file, cur_line, depth, diags)) { return false; }
                    cur.clear();
                    ++i;
                    continue;
                }
                if (paren < 0 || bracket < 0) {
                    diags.error(ErrorCode::E_PARSE, "unbalanced closing delimiter",
                                at(file, line));
                    return false;
                }
            }
            cur += c;
            ++i;
        }
        if (quote != '\0') {
            diags.error(ErrorCode::E_PARSE, "unterminated quoted token", at(file, line));
            return false;
        }
        if (cur.find_first_not_of(" \t\n\r") != std::string::npos) {
            diags.error(ErrorCode::E_PARSE, "the last item is not terminated by '.'",
                        at(file, cur_line));
            return false;
        }
        return true;
    }

    bool item(const std::string& text, const std::string& file, int line, int depth,
              Uir::Diagnostics& diags) {
        active_file_ = file;
        std::string s;
        for (char c : text) { if (!std::isspace(static_cast<unsigned char>(c)) || !s.empty()) { s += c; } }
        while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) { s.pop_back(); }
        if (s.empty()) { return true; }

        const std::size_t lp = s.find('(');
        if (lp == std::string::npos || s.back() != ')') {
            diags.error(ErrorCode::E_PARSE, "an item is `language(...)`", at(line));
            return false;
        }
        std::string lang = s.substr(0, lp);
        lang.erase(std::remove_if(lang.begin(), lang.end(),
                                  [](unsigned char c) { return std::isspace(c); }),
                   lang.end());
        const std::string body = s.substr(lp + 1, s.size() - lp - 2);

        if (lang == "include") { return include(body, file, line, depth, diags); }
        // Split fully rather than keeping three pieces: the optional
        // `source` and `useful_info` fields follow the formula, and a limit of
        // three glues them onto it -- `p(x), file('X.p', a), [status(thm)]`
        // then reaches the formula lexer, which stops at the first comma. The
        // formula itself can hold no depth-zero comma, so parts[2] is exactly
        // it and everything after is annotation this layer has no use for.
        const std::vector<std::string> parts = topCommas(body);
        if (parts.size() < 3) {
            diags.error(ErrorCode::E_PARSE, "an annotated formula is `name, role, formula`",
                        at(line));
            return false;
        }
        std::string formula_name;
        if (!parseFormulaName(parts[0], formula_name, diags, line)) { return false; }
        if (!selectedFormula(formula_name, diags)) { return true; }
        // Selection precedes formula elaboration, including dialect checks.
        // An empty selection of a THF library contributes no formula at all.
        if (lang != "fof" && lang != "cnf" && lang != "tff" && lang != "txf") {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "the '" + lang + "' language is not supported; only cnf, fof, "
                        "tff and txf are (thf is higher-order and stays refused)",
                        at(line));
            return false;
        }

        const std::string role = trim(parts[1]);
        Lexer lx(parts[2], line);
        toks_.clear();
        pos_ = 0;
        for (Tok t = lx.next(); t.kind != Tok::END; t = lx.next()) { toks_.push_back(t); }
        toks_.push_back(Tok{Tok::END, "", line});

        free_.clear();
        cnf_variables_.clear();
        current_language_ = lang;
        // A `type` item contributes its atom typing to the persistent
        // environment and produces no formula; name and role were validated
        // above. The environment lives on the parser object, so declarations
        // are shared across include() recursion.
        if ((lang == "tff" || lang == "txf") && role == "type") {
            return atomTyping(diags, line);
        }
        H::ExprPtr f = lang == "cnf" ? cnfFormula(diags) : formula(diags);
        if (!f) { return false; }
        if (toks_[pos_].kind != Tok::END) {
            diags.error(ErrorCode::E_PARSE,
                        "unexpected '" + toks_[pos_].text + "' after the formula",
                        at(toks_[pos_].line));
            return false;
        }

        // A CNF clause's variables are implicitly universally quantified. In
        // contrast, every FOF variable must be explicitly bound (TPTP 9.3 BNF),
        // so silently applying the CNF rule to FOF changes an ill-formed input
        // into another, well-formed problem.
        if (!free_.empty()) {
            if (lang != "cnf") {
                std::vector<std::string> names(free_.begin(), free_.end());
                std::sort(names.begin(), names.end());
                const std::string layer =
                    lang == "fof" ? "FOF" : (lang == "tff" ? "TFF" : "TXF");
                diags.error(ErrorCode::E_PARSE,
                            layer + " variable '" + names.front()
                                + "' is free; only CNF variables are implicitly universally quantified",
                            at(line));
                return false;
            }
            std::vector<std::string> names(free_.begin(), free_.end());
            std::sort(names.begin(), names.end());      // reproducible output
            std::vector<H::Binder> binders;
            for (const std::string& n : names) {
                binders.push_back(H::Binder{n, H::Sort::uninterpreted(kUniverse)});
            }
            f = H::mkForall(binders, f, at(line));
        }

        static const std::unordered_set<std::string> kAxiomLike = {
            "axiom", "hypothesis", "definition", "assumption", "lemma",
            "theorem", "corollary"
        };
        if (role != "conjecture" && role != "negated_conjecture"
            && kAxiomLike.count(role) == 0) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "formula role '" + role + "' has no supported input-problem "
                        "semantics; only axiom-like, conjecture, and "
                        "negated_conjecture roles are accepted",
                        at(line));
            return false;
        }

        // **The obligation that inverts every answer.** `axioms |= C1 & ... & Cn`
        // is decided by refuting `axioms AND NOT(C1 & ... & Cn)`. Positive
        // conjectures are therefore collected and negated together after all
        // includes have been expanded. A `negated_conjecture` contributes
        // itself: multiple CNF formulas with that role are the clauses of one
        // already-negated goal and must remain conjoined.
        if (role == "conjecture") {
            conjectures_.push_back(f);
        }
        if (role == "conjecture") {
            has_positive_conjecture_ = true;
            // The second obligation, said out loud rather than assumed: this
            // positive conjecture makes the source question validity, so target
            // UNSAT is a positive answer and target SAT is a countermodel. A
            // `negated_conjecture` alone does not do this: it is an asserted
            // formula in a satisfiability problem (e.g. official MGT031-1).
            //
            // Recorded as exact(), and that is not an oversight. The reduction
            // itself loses nothing -- `axioms |= C` holds exactly when
            // `axioms AND NOT C` is unsatisfiable -- so marking it unsound or
            // incomplete would put a false approximation into the very column
            // the results tables stratify on. What the reader needs is not a
            // downgrade but the *direction*, which is what the choice records.
            if (!said_inverted_) {
                said_inverted_ = true;
                Uir::EncodingChoice c;
                c.site       = active_file_ + ":" + std::to_string(line);
                c.unified_op = "conjecture";
                c.strategy   = "negate-and-refute";
                c.fidelity   = Uir::Fidelity::exact();
                c.rationale =
                    "a positive conjecture is translated to a refutation goal, so the "
                    "verdict mapping is inverted; UNSAT "
                    "means TPTP 'Theorem' and SAT means 'CounterSatisfiable'. A file "
                    "containing only negated_conjecture formulae remains a direct "
                    "satisfiability problem";
                report_->addChoice(std::move(c));
                // Kept as a note as well: the choice reaches the experiment
                // database, the note reaches whoever is reading a terminal.
                diags.note(ErrorCode::OK,
                           "a conjecture refutation goal is present; UNSAT of this "
                           "script means TPTP 'Theorem' and SAT means "
                           "'CounterSatisfiable' -- the verdict mapping is inverted",
                           at(line));
            }
        }
        if (role == "conjecture") { return true; }
        H::Constraint c;
        c.loc = at(line);
        c.formula = f;
        model_->constraints.push_back(c);
        return true;
    }

    /** `include('Axioms/X.ax')`. The included file is PART OF THE PROBLEM: a
     *  missing one is a wrong problem rather than a smaller one, so it is an
     *  error and never a warning. */
    bool include(const std::string& body, const std::string& file, int line, int depth,
                 Uir::Diagnostics& diags) {
        const std::vector<std::string> parts = topCommas(body);
        if (parts.empty() || parts.size() > 3 || parts[0].empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "include is `include(file[, selection[, namespace]])`", at(line));
            return false;
        }
        std::string path;
        if (!parseAtomicWord(parts[0], path, false)) {
            diags.error(ErrorCode::E_PARSE,
                        "an include file name is a lower-case or single-quoted atomic word",
                        at(line));
            return false;
        }
        if (parts.size() == 3) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "TPTP 9.3 include namespaces require systematic renaming of every symbol and are not supported",
                        at(line));
            return false;
        }

        IncludeSelection selection;
        IncludeSelection* selected = nullptr;
        if (parts.size() == 2 && trim(parts[1]) != "*" && trim(parts[1]) != "all") {
            if (!parseSelection(parts[1], selection, diags, line)) { return false; }
            selection.loc = at(line);
            selected = &selection;
        }
        namespace fs = std::filesystem;
        const fs::path base = fs::path(file).parent_path();
        std::vector<fs::path> tries{base / path, fs::path(path)};
        if (const char* root = std::getenv("TPTP")) {
            tries.push_back(fs::path(root) / path);
        }
        for (const auto& p : tries) {
            std::ifstream in(p, std::ios::binary);
            if (!in) { continue; }
            std::ostringstream ss;
            ss << in.rdbuf();
            if (selected) { selections_.push_back(selected); }
            const bool parsed = items(ss.str(), p.string(), depth + 1, diags);
            if (selected) { selections_.pop_back(); }
            if (!parsed) { return false; }
            if (selected && !validateSelection(*selected, diags)) { return false; }
            return true;
        }
        diags.error(ErrorCode::E_IO,
                    "cannot resolve include('" + path + "'); the included file is part "
                    "of the problem, so a missing one is a different problem rather "
                    "than a smaller one",
                    at(line));
        return false;
    }

    static std::string trim(const std::string& s) {
        const std::size_t a = s.find_first_not_of(" \t\n\r");
        if (a == std::string::npos) { return ""; }
        return s.substr(a, s.find_last_not_of(" \t\n\r") - a + 1);
    }

    /** Split on commas at depth zero. Parens and brackets both nest, because a
     *  quantifier's variable list is `[X, Y]` and an annotation's useful_info
     *  is a bracketed list. */
    static std::vector<std::string> topCommas(const std::string& s) {
        std::vector<std::string> out;
        int depth = 0;
        char quote = '\0';
        bool escaped = false;
        std::string cur;
        for (char c : s) {
            if (quote != '\0') {
                if (escaped) {
                    escaped = false;
                } else if (c == '\\') {
                    escaped = true;
                } else if (c == quote) {
                    quote = '\0';
                }
            } else if (c == '\'' || c == '"') {
                quote = c;
            } else {
                if (c == '(' || c == '[') { ++depth; }
                if (c == ')' || c == ']') { --depth; }
                if (c == ',' && depth == 0) {
                    out.push_back(trim(cur));
                    cur.clear();
                    continue;
                }
            }
            cur += c;
        }
        out.push_back(trim(cur));
        return out;
    }

    static bool parseAtomicWord(const std::string& spelling, std::string& value,
                                bool allow_integer) {
        const std::string s = trim(spelling);
        if (s.empty()) { return false; }
        if (allow_integer
            && std::all_of(s.begin(), s.end(), [](unsigned char c) {
                   return std::isdigit(c) != 0;
               })) {
            value = s;
            return true;
        }
        if (std::islower(static_cast<unsigned char>(s.front()))) {
            if (!std::all_of(s.begin() + 1, s.end(), [](unsigned char c) {
                    return std::isalnum(c) != 0 || c == '_';
                })) {
                return false;
            }
            value = s;
            return true;
        }
        if (s.front() != '\'' || s.size() < 3 || s.back() != '\'') { return false; }
        value.clear();
        bool escaped = false;
        for (std::size_t i = 1; i + 1 < s.size(); ++i) {
            const char c = s[i];
            if (escaped) {
                if (c != '\'' && c != '\\') { return false; }
                value += c;
                escaped = false;
            } else if (c == '\\') {
                escaped = true;
            } else if (c == '\'' || c == '\n' || c == '\r') {
                return false;
            } else {
                value += c;
            }
        }
        return !escaped && !value.empty();
    }

    bool parseFormulaName(const std::string& spelling, std::string& value,
                          Uir::Diagnostics& diags, int line) const {
        if (parseAtomicWord(spelling, value, true)) { return true; }
        diags.error(ErrorCode::E_PARSE,
                    "a formula name is an atomic word or integer", at(line));
        return false;
    }

    bool parseSelection(const std::string& spelling, IncludeSelection& selection,
                        Uir::Diagnostics& diags, int line) const {
        const std::string s = trim(spelling);
        if (s.size() < 2 || s.front() != '[' || s.back() != ']') {
            diags.error(ErrorCode::E_PARSE,
                        "an include selection is `*` or a bracketed formula-name list",
                        at(line));
            return false;
        }
        const std::string body = s.substr(1, s.size() - 2);
        if (trim(body).empty()) { return true; }
        for (const std::string& part : topCommas(body)) {
            std::string name;
            if (!parseFormulaName(part, name, diags, line)) { return false; }
            if (!selection.requested.insert(name).second) {
                diags.error(ErrorCode::E_PARSE,
                            "include selection names formula '" + name + "' more than once",
                            at(line));
                return false;
            }
        }
        return true;
    }

    bool selectedFormula(const std::string& name, Uir::Diagnostics& diags) {
        bool included = true;
        for (std::size_t n = selections_.size(); n > 0; --n) {
            IncludeSelection& selection = *selections_[n - 1];
            included = included && selection.requested.count(name) != 0;
            if (!included || selection.requested.count(name) == 0) { continue; }
            const std::size_t count = ++selection.seen[name];
            if (count > 1) {
                diags.error(ErrorCode::E_PARSE,
                            "selected formula name '" + name
                                + "' occurs more than once in the included subtree",
                            selection.loc);
                return false;
            }
        }
        return included;
    }

    static bool validateSelection(const IncludeSelection& selection,
                                  Uir::Diagnostics& diags) {
        for (const std::string& requested : selection.requested) {
            const auto found = selection.seen.find(requested);
            if (found == selection.seen.end() || found->second == 0) {
                diags.error(ErrorCode::E_PARSE,
                            "selected formula name '" + requested
                                + "' was not found exactly once in the included subtree",
                            selection.loc);
                return false;
            }
            if (found->second != 1) { return false; }
        }
        return true;
    }

    // ---- formula grammar --------------------------------------------------

    const Tok& peek() const { return toks_[pos_]; }
    bool isPunct(const char* p) const {
        return peek().kind == Tok::PUNCT && peek().text == p;
    }
    bool eat(const char* p) {
        if (!isPunct(p)) { return false; }
        ++pos_;
        return true;
    }

    H::ExprPtr formula(Uir::Diagnostics& diags) {
        H::ExprPtr left = unitFormula(diags);
        if (!left) { return nullptr; }
        if (peek().kind != Tok::PUNCT) { return left; }

        const std::string connective = peek().text;
        const int line = peek().line;
        if (connective == "&" || connective == "|") {
            ++pos_;
            std::vector<H::ExprPtr> parts{left};
            do {
                H::ExprPtr right = unitFormula(diags);
                if (!right) { return nullptr; }
                parts.push_back(std::move(right));
            } while (eat(connective.c_str()));
            return H::mkOp(connective == "&" ? H::Op::AND : H::Op::OR,
                           std::move(parts), at(line));
        }

        if (connective != "<=>" && connective != "<~>" && connective != "=>"
            && connective != "<=" && connective != "~&" && connective != "~|") {
            // A sequent arrow where a connective was expected is the TXF
            // <txf_sequent>; name it rather than dying on the trailing tokens.
            if (typed() && connective == "~" && pos_ + 1 < toks_.size()
                && toks_[pos_ + 1].text == ">") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "TXF sequents ('~>', <txf_sequent>) are not supported",
                            at(line));
                return nullptr;
            }
            return left;
        }
        ++pos_;
        H::ExprPtr right = unitFormula(diags);
        if (!right) { return nullptr; }
        if (connective == "<=>") {
            return H::mkOp(H::Op::EQ, {left, right}, at(line));
        }
        if (connective == "<~>") {
            return H::mkOp(H::Op::XOR, {left, right}, at(line));
        }
        if (connective == "=>") {
            return H::mkOp(H::Op::IMPLIES, {left, right}, at(line));
        }
        if (connective == "<=") {
            return H::mkOp(H::Op::IMPLIES, {right, left}, at(line));
        }
        const H::Op inside = connective == "~&" ? H::Op::AND : H::Op::OR;
        return H::mkOp(H::Op::NOT,
                       {H::mkOp(inside, {left, right}, at(line))}, at(line));
    }

    H::ExprPtr unitFormula(Uir::Diagnostics& diags) {
        const int line = peek().line;
        if (typed() && isPunct("[")) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "TXF tuples and sequents in formula position ('[...]', "
                        "<txf_tuple>/<txf_sequent>) are not supported",
                        at(line));
            return nullptr;
        }
        if (eat("~")) {
            H::ExprPtr e = unitFormula(diags);
            return e ? H::mkOp(H::Op::NOT, {e}, at(line)) : nullptr;
        }
        if (isPunct("!") || isPunct("?")) {
            const bool forall = peek().text == "!";
            ++pos_;
            if (!eat("[")) {
                diags.error(ErrorCode::E_PARSE, "a quantifier needs a variable list",
                            at(line));
                return nullptr;
            }
            std::vector<H::Binder> binders;
            std::unordered_map<std::string, H::Sort> binder_sorts;
            std::vector<std::string> source_names;
            for (;;) {
                if (peek().kind != Tok::VAR) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + peek().text + "' is not a variable; TPTP variables "
                                "are upper-case", at(peek().line));
                    return nullptr;
                }
                const std::string source_name = peek().text;
                ++pos_;
                // TFF/TXF binders may carry an atomic sort: ![X: fruit]. An
                // untyped variable defaults to $i -- the FOF universe -- which
                // is what makes a mixed FOF/TFF file one problem.
                H::Sort var_sort = H::Sort::uninterpreted(kUniverse);
                if (typed() && isPunct(":")) {
                    ++pos_;
                    bool ttype = false;
                    if (!parseAtomicType(var_sort, ttype, diags)) { return nullptr; }
                    if (ttype) {
                        diags.error(ErrorCode::E_TYPE,
                                    "'$tType' names the sort of sorts; it is not the "
                                    "sort of a variable",
                                    at(peek().line));
                        return nullptr;
                    }
                }
                auto prior_binder = binder_sorts.find(source_name);
                if (prior_binder != binder_sorts.end()
                    && !H::sameSort(prior_binder->second, var_sort)) {
                    diags.error(ErrorCode::E_TYPE,
                                "repeated quantifier variable '" + source_name
                                    + "' has incompatible sorts "
                                    + H::toString(prior_binder->second) + " and "
                                    + H::toString(var_sort),
                                at(peek().line));
                    return nullptr;
                }
                binder_sorts.emplace(source_name, var_sort);

                std::string target_name = source_name;
                auto& scope = bound_names_[source_name];
                if (!scope.empty()) {
                    target_name = "tptp_shadow_" + std::to_string(++binder_serial_);
                    if (!said_alpha_rename_) {
                        said_alpha_rename_ = true;
                        Uir::EncodingChoice choice;
                        choice.site = active_file_ + ":" + std::to_string(peek().line);
                        choice.unified_op = "shadowed-bound-variable";
                        choice.strategy = "capture-avoiding-alpha-renaming";
                        choice.fidelity = Uir::Fidelity::exact();
                        choice.rationale =
                            "a TPTP binder reuses a variable spelling already in scope (including an earlier entry in the same binder list); the target binder is fresh and occurrences resolve to the innermost binding only";
                        report_->addChoice(std::move(choice));
                    }
                }
                binders.push_back(H::Binder{target_name, var_sort});
                source_names.push_back(source_name);
                scope.push_back(BoundVar{target_name, var_sort});
                if (eat(",")) { continue; }
                break;
            }
            if (!eat("]") || !eat(":")) {
                diags.error(ErrorCode::E_PARSE, "a quantifier is `! [X] : F`", at(line));
                return nullptr;
            }
            H::ExprPtr body = unitFormula(diags);
            for (const std::string& source_name : source_names) {
                auto found = bound_names_.find(source_name);
                if (found == bound_names_.end()) { continue; }
                found->second.pop_back();
                if (found->second.empty()) { bound_names_.erase(found); }
            }
            if (!body) { return nullptr; }
            return forall ? H::mkForall(binders, body, at(line))
                          : H::mkExists(binders, body, at(line));
        }
        if (eat("(")) {
            H::ExprPtr e = formula(diags);
            if (!e) { return nullptr; }
            if (!eat(")")) {
                diags.error(ErrorCode::E_PARSE, "expected ')'", at(peek().line));
                return nullptr;
            }
            return e;
        }
        return atom(diags);
    }

    H::ExprPtr cnfFormula(Uir::Diagnostics& diags) {
        if (eat("(")) {
            H::ExprPtr nested = cnfFormula(diags);
            if (!nested) { return nullptr; }
            if (!eat(")")) {
                diags.error(ErrorCode::E_PARSE, "expected ')' after CNF clause",
                            at(peek().line));
                return nullptr;
            }
            return nested;
        }
        const int line = peek().line;
        H::ExprPtr first = cnfLiteral(diags);
        if (!first) { return nullptr; }
        std::vector<H::ExprPtr> literals{first};
        while (eat("|")) {
            H::ExprPtr next = cnfLiteral(diags);
            if (!next) { return nullptr; }
            literals.push_back(next);
        }
        return literals.size() == 1 ? literals.front()
                                    : H::mkOp(H::Op::OR, std::move(literals), at(line));
    }

    H::ExprPtr cnfLiteral(Uir::Diagnostics& diags) {
        const int line = peek().line;
        if (!eat("~")) { return atom(diags); }
        const bool parenthesized = eat("(");
        H::ExprPtr value = atom(diags);
        if (!value) { return nullptr; }
        if (parenthesized && !eat(")")) {
            diags.error(ErrorCode::E_PARSE, "expected ')' after negated CNF atom",
                        at(peek().line));
            return nullptr;
        }
        return H::mkOp(H::Op::NOT, {value}, at(line));
    }

    H::ExprPtr atom(Uir::Diagnostics& diags) {
        const int line = peek().line;
        if (peek().kind == Tok::IDENT && !peek().single_quoted
            && (peek().text == "$true" || peek().text == "$false")) {
            const bool value = peek().text == "$true";
            ++pos_;
            return H::mkBool(value, at(line));
        }
        H::ExprPtr l = term(diags, true);
        if (!l) { return nullptr; }
        if (eat("=")) {
            // `==` is the TXF <txf_definition>, not doubled equality.
            if (typed() && isPunct("=")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "the TXF definition construct ('atom == term', "
                            "<txf_definition>) is not supported",
                            at(line));
                return nullptr;
            }
            if (typed() && l->sort.kind == H::SortKind::BOOL) {
                // An $o-sorted term on the left of `=` stays a predicate use
                // (TFF equality is ad-hoc polymorphic, $o included).
                if (!commitUse(l, SymbolUse::PREDICATE, diags)) { return nullptr; }
            } else if (!commitUse(l, SymbolUse::TERM, diags)) {
                return nullptr;
            }
            H::ExprPtr r = term(diags);
            if (!r || !sameEqualitySides(l, r, diags, at(line))) { return nullptr; }
            return H::mkOp(H::Op::EQ, {l, r}, at(line));
        }
        if (eat("!=")) {
            if (typed() && l->sort.kind == H::SortKind::BOOL) {
                if (!commitUse(l, SymbolUse::PREDICATE, diags)) { return nullptr; }
            } else if (!commitUse(l, SymbolUse::TERM, diags)) {
                return nullptr;
            }
            H::ExprPtr r = term(diags);
            if (!r || !sameEqualitySides(l, r, diags, at(line))) { return nullptr; }
            return H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {l, r}, at(line))}, at(line));
        }
        if (typed() && isPunct("@")) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "NXF atoms ('{connective} @ (args)') are non-classical and "
                        "not supported",
                        at(line));
            return nullptr;
        }
        if (typed()) {
            // In TFF a predicate application IS an atom, and TXF (FOOL)
            // conflates $o-sorted terms and formulas. Either way, a Bool-sorted
            // term in formula position is the atom; anything else is a type
            // error, and TPTP has no to-bool coercion to apply silently.
            if (l->kind == H::ExprKind::APPLY) {
                if (!commitUse(l, SymbolUse::PREDICATE, diags)) { return nullptr; }
                if (l->sort.kind != H::SortKind::BOOL) {
                    // First met in formula position: the assumed default typing
                    // is revised from ($i * ... * $i) > $i to > $o in setUse,
                    // and the expression's sort follows it here.
                    auto fixed = std::make_shared<H::Expr>(*l);
                    fixed->sort = H::Sort::boolean();
                    return fixed;
                }
                return l;
            }
            if (l->sort.kind == H::SortKind::BOOL) { return l; }
            diags.error(ErrorCode::E_TYPE,
                        "a term of sort " + H::toString(l->sort)
                            + " is used as a formula; only $o-sorted terms are formulas",
                        at(line));
            return nullptr;
        }
        // A bare term in formula position is a predicate application. Its sort
        // was recorded as the universe when the term was built; a predicate is a
        // function whose result is Bool, so the signature is corrected here --
        // TPTP has no syntax distinguishing the two, and position is the only
        // evidence there is.
        if (l->kind == H::ExprKind::APPLY) {
            if (!commitUse(l, SymbolUse::PREDICATE, diags)) { return nullptr; }
            auto fixed = std::make_shared<H::Expr>(*l);
            fixed->sort = H::Sort::boolean();
            return fixed;
        }
        if (l->kind == H::ExprKind::LIT_BOOL) { return l; }
        diags.error(ErrorCode::E_PARSE,
                    "'" + l->name + "' is used as a formula but is a term", at(line));
        return nullptr;
    }

    /** TPTP equality is ad-hoc polymorphic: both sides must share ONE sort,
     *  and no coercion crosses numeric sort boundaries. */
    bool sameEqualitySides(const H::ExprPtr& l, const H::ExprPtr& r,
                           Uir::Diagnostics& diags, Uir::SourceLoc loc) {
        if (!typed() || H::sameSort(l->sort, r->sort)) { return true; }
        diags.error(ErrorCode::E_TYPE,
                    "the two sides of '=' have different sorts ("
                        + H::toString(l->sort) + " vs " + H::toString(r->sort)
                        + "); TPTP equality is ad-hoc polymorphic, not coercing",
                    std::move(loc));
        return false;
    }

    H::ExprPtr term(Uir::Diagnostics& diags, bool defer_outer_use = false) {
        const Tok t = peek();
        if (t.kind == Tok::VAR) {
            ++pos_;
            const auto bound = bound_names_.find(t.text);
            if (bound == bound_names_.end() || bound->second.empty()) {
                // A free variable in a CNF clause is implicitly universally
                // quantified. Recorded so the clause can be closed.
                free_.insert(t.text);
                // CNF variables are bound once for the whole annotated clause.
                // Represent that binding by one HIR leaf, located at its first
                // occurrence; each enclosing application keeps its own source
                // location. This shares binding references across literals,
                // instead of allocating a full Expr and path for every use.
                if (current_language_ == "cnf") {
                    auto& expression = cnf_variables_[t.text];
                    if (!expression) {
                        expression = H::mkBoundVar(t.text, H::Sort::uninterpreted(kUniverse),
                                                  at(t.line));
                    }
                    return expression;
                }
                return H::mkBoundVar(t.text, H::Sort::uninterpreted(kUniverse),
                                     at(t.line));
            }
            return H::mkBoundVar(bound->second.back().target,
                                 bound->second.back().sort, at(t.line));
        }
        if (t.kind == Tok::INVALID) {
            diags.error(ErrorCode::E_PARSE, t.text, at(t.line));
            return nullptr;
        }
        if (t.kind == Tok::NUMBER) {
            if (!typed()) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "numeric terms require a typed TPTP language; CNF/FOF has no numeric carrier",
                            at(t.line));
                return nullptr;
            }
            ++pos_;
            return numericLiteral(t.text, false, diags, at(t.line));
        }
        if (typed() && t.kind == Tok::PUNCT) {
            // A sign is part of TPTP's <number>, so `-3` is one literal.
            if ((t.text == "-" || t.text == "+") && pos_ + 1 < toks_.size()
                && toks_[pos_ + 1].kind == Tok::NUMBER) {
                const bool negative = t.text == "-";
                ++pos_;
                const Tok num = peek();
                ++pos_;
                return numericLiteral(num.text, negative, diags, at(t.line));
            }
            if (t.text == "(" && current_language_ == "txf") {
                // TXF (FOOL): a parenthesized formula is a $o-sorted term.
                ++pos_;
                H::ExprPtr f = formula(diags);
                if (!f) { return nullptr; }
                if (!eat(")")) {
                    diags.error(ErrorCode::E_PARSE, "expected ')'", at(peek().line));
                    return nullptr;
                }
                return f;
            }
            if (t.text == "[") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "TXF tuples ('[t1, ..., tn]', <txf_tuple>) are not supported",
                            at(t.line));
                return nullptr;
            }
            if (t.text == "{" || t.text == "@") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "NXF atoms ('{connective} @ (args)') are non-classical and "
                            "not supported",
                            at(t.line));
                return nullptr;
            }
        }
        if (t.kind != Tok::IDENT && t.kind != Tok::DISTINCT_OBJECT) {
            diags.error(ErrorCode::E_PARSE, "expected a term, got '" + t.text + "'",
                        at(t.line));
            return nullptr;
        }
        ++pos_;
        if (t.kind == Tok::IDENT && !t.single_quoted && !t.text.empty()
            && t.text.front() == '$') {
            if (!typed()) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            (t.text.rfind("$$", 0) == 0
                                 ? "system symbol '" + t.text
                                       + "' has tool-specific semantics and cannot be translated exactly"
                                 : "defined symbol '" + t.text
                                       + "' is not part of the exact classical CNF/FOF fragment"),
                            at(t.line));
                return nullptr;
            }
            return definedTerm(t.text, diags, at(t.line));
        }
        // A TXF $let definition shadows any global reading of its name.
        if (typed() && t.kind == Tok::IDENT) {
            if (LetDef* def = lookupLet(t.text)) {
                return letUse(t.text, *def, diags, at(t.line));
            }
        }
        std::vector<H::ExprPtr> args;
        if (eat("(")) {
            if (t.kind == Tok::DISTINCT_OBJECT) {
                diags.error(ErrorCode::E_PARSE,
                            "a distinct object is a constant and cannot take arguments",
                            at(t.line));
                return nullptr;
            }
            for (;;) {
                H::ExprPtr a = term(diags);
                if (!a) { return nullptr; }
                args.push_back(a);
                if (eat(",")) { continue; }
                break;
            }
            if (!eat(")")) {
                diags.error(ErrorCode::E_PARSE, "expected ')'", at(peek().line));
                return nullptr;
            }
        }
        // **The sort discipline.** Untyped FOF lives in ONE unsorted universe, so
        // every term gets the same uninterpreted sort; guessing per-symbol sorts
        // from usage would invent distinctions the logic does not have. TFF/TXF
        // symbols instead carry their declared signature, and an undeclared one
        // gets TPTP's default typing ($i * ... * $i) > $i -- recorded as ASSUMED,
        // so a conflicting later declaration is a type error while an identical
        // one is legal spec merging.
        const std::string parse_name = t.kind == Tok::DISTINCT_OBJECT
                                           ? distinctParseName(t.text)
                                           : t.text;
        const std::string source_name = t.kind == Tok::DISTINCT_OBJECT
                                            ? distinctSourceName(t.text)
                                            : t.text;
        SignatureEntry& entry = declareSymbol(parse_name, source_name, args.size(),
                                              at(t.line));
        if (typed() && !entry.has_type) {
            entry.has_type = true;
            entry.assumed = true;
            entry.params.assign(args.size(), H::Sort::uninterpreted(kUniverse));
            // A symbol an earlier untyped item already classified keeps that
            // classification: the default is ($i * ... * $i) > $o for a
            // predicate and > $i for a function.
            entry.result = entry.use == SymbolUse::PREDICATE
                               ? H::Sort::boolean()
                               : H::Sort::uninterpreted(kUniverse);
        }
        if (!defer_outer_use && !setUse(entry, SymbolUse::TERM, diags, at(t.line))) {
            return nullptr;
        }
        if (entry.has_type) {
            for (std::size_t i = 0; i < args.size(); ++i) {
                if (!H::sameSort(args[i]->sort, entry.params[i])) {
                    diags.error(ErrorCode::E_TYPE,
                                "'" + entry.source_name + "' is "
                                    + (entry.assumed ? "assumed " : "declared ")
                                    + signatureString(entry.params, entry.result)
                                    + " but argument " + std::to_string(i + 1)
                                    + " has sort " + H::toString(args[i]->sort),
                                at(t.line));
                    return nullptr;
                }
            }
        }
        const H::Sort result = entry.has_type ? entry.result
                                              : H::Sort::uninterpreted(kUniverse);
        if (t.kind == Tok::DISTINCT_OBJECT
            && distinct_object_names_.insert(parse_name).second) {
            distinct_objects_.push_back(H::mkApply(parse_name, result, {}, at(t.line)));
        }
        return H::mkApply(parse_name, result, args, at(t.line));
    }

    bool typed() const { return current_language_ == "tff" || current_language_ == "txf"; }

    /** TPTP numeric literal: `3` is $int, `3/5` is $rat, `3.5` and `1.5E-2` are
     *  $real -- the literal's FORM decides the sort, and there is no other
     *  rule. Exponent reals are expanded to plain decimals because the SMT-LIB
     *  real literal has no exponent spelling; the expansion is exact. */
    H::ExprPtr numericLiteral(const std::string& text, bool negative,
                              Uir::Diagnostics& diags, Uir::SourceLoc loc) {
        const std::string sign = negative ? "-" : "";
        const auto digits = [](const std::string& s) {
            return !s.empty()
                   && std::all_of(s.begin(), s.end(), [](unsigned char c) {
                          return std::isdigit(c) != 0;
                      });
        };
        const std::size_t slash = text.find('/');
        if (slash == std::string::npos && digits(text)) {
            return H::mkInt(sign + text, loc);
        }
        if (slash != std::string::npos) {
            const std::string num = text.substr(0, slash);
            const std::string den = text.substr(slash + 1);
            if (!digits(num) || !digits(den)
                || den.find_first_not_of('0') == std::string::npos) {
                diags.error(ErrorCode::E_PARSE,
                            "malformed rational literal '" + text + "'", loc);
                return nullptr;
            }
            return H::mkReal(sign + text, loc);
        }
        std::string mantissa = text;
        long exponent = 0;
        const std::size_t epos = text.find_first_of("Ee");
        if (epos != std::string::npos) {
            mantissa = text.substr(0, epos);
            const std::string etext = text.substr(epos + 1);
            char* end = nullptr;
            exponent = std::strtol(etext.c_str(), &end, 10);
            if (end == etext.c_str() || *end != '\0') {
                diags.error(ErrorCode::E_PARSE,
                            "malformed real literal '" + text + "'", loc);
                return nullptr;
            }
        }
        const std::size_t dot = mantissa.find('.');
        if (dot == std::string::npos || !digits(mantissa.substr(0, dot))
            || !digits(mantissa.substr(dot + 1))) {
            diags.error(ErrorCode::E_PARSE,
                        "malformed numeric literal '" + text + "'", loc);
            return nullptr;
        }
        return H::mkReal(sign + expandExponent(mantissa.substr(0, dot),
                                               mantissa.substr(dot + 1), exponent),
                         loc);
    }

    /** `int_part.frac_part * 10^exponent` as an exact SMT-LIB decimal. */
    static std::string expandExponent(const std::string& int_part,
                                      const std::string& frac_part, long exponent) {
        const std::string digits = int_part + frac_part;
        const long point = static_cast<long>(int_part.size()) + exponent;
        if (point <= 0) {
            return "0." + std::string(static_cast<std::size_t>(-point), '0') + digits;
        }
        if (static_cast<std::size_t>(point) >= digits.size()) {
            return digits + std::string(static_cast<std::size_t>(point) - digits.size(), '0')
                   + ".0";
        }
        return digits.substr(0, static_cast<std::size_t>(point)) + "."
               + digits.substr(static_cast<std::size_t>(point));
    }

    /** The ONE numeric sort shared by every argument of an arithmetic builtin,
     *  or an error: TPTP has no implicit $int-to-$real coercion, so mixing is
     *  what TPTP itself forbids (E_TYPE, not a fragment refusal). */
    bool numericSort(const std::string& name, const std::vector<H::ExprPtr>& args,
                     H::Sort& out, Uir::Diagnostics& diags, Uir::SourceLoc loc) {
        for (const H::ExprPtr& a : args) {
            if (a->sort.kind != H::SortKind::INT && a->sort.kind != H::SortKind::REAL) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + name + "' is arithmetic but its argument has sort "
                                + H::toString(a->sort),
                            std::move(loc));
                return false;
            }
        }
        out = args.front()->sort;
        for (const H::ExprPtr& a : args) {
            if (!H::sameSort(a->sort, out)) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + name + "' requires all arguments to share one numeric "
                                "sort (" + H::toString(out) + " vs "
                                + H::toString(a->sort)
                                + "); TPTP has no implicit $int-to-$real coercion",
                            std::move(loc));
                return false;
            }
        }
        return true;
    }

    /** TPTP's division and remainder are TOTAL: a zero divisor yields an
     *  unspecified value, which is exactly SMT-LIB's reading of a total
     *  uninterpreted function, so no definedness guard is added -- but the
     *  choice is stated, as the HIR operator family header requires. */
    void noteTotalDivision(const Uir::SourceLoc& loc) {
        if (said_total_division_) { return; }
        said_total_division_ = true;
        Uir::EncodingChoice c;
        c.site       = loc.file + ":" + std::to_string(loc.line);
        c.unified_op = "tff-division";
        c.strategy   = "total-zero-divisor";
        c.fidelity   = Uir::Fidelity::exact();
        c.rationale  =
            "TPTP division and remainder are total: a zero divisor yields an "
            "unspecified value, which is exactly SMT-LIB's uninterpreted total "
            "function reading; no definedness guard is added";
        report_->addChoice(std::move(c));
    }

    void noteLetInlining(const Uir::SourceLoc& loc) {
        if (said_let_inline_) { return; }
        said_let_inline_ = true;
        Uir::EncodingChoice c;
        c.site       = loc.file + ":" + std::to_string(loc.line);
        c.unified_op = "txf-let";
        c.strategy   = "parse-time-substitutive-inlining";
        c.fidelity   = Uir::Fidelity::exact();
        c.rationale  =
            "non-recursive TXF $let definitions are inlined at parse time with "
            "capture-avoiding renaming; the HIR has no let binder, and inlining "
            "a non-recursive definition is definitionally exact";
        report_->addChoice(std::move(c));
    }

    /** A `$`-prefixed defined symbol in term position (TFF/TXF only). The
     *  arithmetic builtins are ad-hoc polymorphic over ONE numeric sort. What
     *  TPTP itself forbids (e.g. $quotient on $int) is E_TYPE; what is legal
     *  but has no HIR reading is E_UNSUPPORTED_CONSTRUCT, named. */
    H::ExprPtr definedTerm(const std::string& name, Uir::Diagnostics& diags,
                           Uir::SourceLoc loc) {
        if (name == "$true") { return H::mkBool(true, loc); }
        if (name == "$false") { return H::mkBool(false, loc); }
        if (name.rfind("$$", 0) == 0) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "system symbol '" + name
                            + "' has tool-specific semantics and cannot be translated exactly",
                        loc);
            return nullptr;
        }
        if (name == "$ite") {
            if (current_language_ != "txf") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "$ite is a TXF (FOOL) construct; it is not part of plain TFF",
                            loc);
                return nullptr;
            }
            return iteTerm(diags, loc);
        }
        if (name == "$let") {
            if (current_language_ != "txf") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "$let is a TXF (FOOL) construct; it is not part of plain TFF",
                            loc);
                return nullptr;
            }
            return letTerm(diags, loc);
        }
        // Legal TPTP this frontend does not implement -- each refused by name.
        if (name == "$quotient_n" || name == "$remainder_n") {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'" + name + "' (round-to-nearest) has no HIR operator; the "
                            "Euclidean, truncating and flooring variants are supported",
                        loc);
            return nullptr;
        }
        if (name == "$round") {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'$round' rounds to nearest with a tie-break TPTP does not pin "
                        "down; there is no HIR operator for it",
                        loc);
            return nullptr;
        }
        if (name == "$is_rat") {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'$is_rat' is not expressible over SMT Reals ($rat and $real "
                        "share the Real carrier); refusing rather than guessing",
                        loc);
            return nullptr;
        }
        static const std::unordered_map<std::string, H::Op> kBinary = {
            {"$sum", H::Op::ADD},
            {"$difference", H::Op::SUB},
            {"$product", H::Op::MUL},
        };
        static const std::unordered_map<std::string, H::Op> kIntQuotient = {
            {"$quotient_e", H::Op::DIV_EUCLID}, {"$quotient_t", H::Op::DIV_TRUNC},
            {"$quotient_f", H::Op::DIV_FLOOR},  {"$remainder_e", H::Op::MOD_EUCLID},
            {"$remainder_t", H::Op::MOD_TRUNC}, {"$remainder_f", H::Op::MOD_FLOOR},
        };
        static const std::unordered_map<std::string, H::Op> kCompare = {
            {"$less", H::Op::LT},   {"$lesseq", H::Op::LE},
            {"$greater", H::Op::GT}, {"$greatereq", H::Op::GE},
        };
        const bool unary =
            name == "$uminus" || name == "$floor" || name == "$ceiling"
            || name == "$truncate" || name == "$to_int" || name == "$to_rat"
            || name == "$to_real" || name == "$is_int";
        const bool known = unary || name == "$quotient" || kBinary.count(name) != 0
                           || kIntQuotient.count(name) != 0 || kCompare.count(name) != 0;
        if (!known) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "defined symbol '" + name
                            + "' is not part of the supported TFF/TXF fragment",
                        loc);
            return nullptr;
        }
        if (!eat("(")) {
            diags.error(ErrorCode::E_PARSE,
                        "defined functor '" + name + "' needs its argument list",
                        at(peek().line));
            return nullptr;
        }
        std::vector<H::ExprPtr> args;
        for (;;) {
            H::ExprPtr a = term(diags);
            if (!a) { return nullptr; }
            args.push_back(a);
            if (eat(",")) { continue; }
            break;
        }
        if (!eat(")")) {
            diags.error(ErrorCode::E_PARSE, "expected ')'", at(peek().line));
            return nullptr;
        }
        const std::size_t want = unary ? 1 : 2;
        if (args.size() != want) {
            diags.error(ErrorCode::E_PARSE,
                        "TPTP defines '" + name + "' with " + std::to_string(want)
                            + (want == 1 ? " argument" : " arguments") + "; got "
                            + std::to_string(args.size()),
                        loc);
            return nullptr;
        }
        H::Sort s;
        if (!numericSort(name, args, s, diags, loc)) { return nullptr; }
        if (kBinary.count(name) != 0) { return H::mkOp(kBinary.at(name), args, loc); }
        if (name == "$uminus") { return H::mkOp(H::Op::NEG, args, loc); }
        if (kCompare.count(name) != 0) { return H::mkOp(kCompare.at(name), args, loc); }
        if (name == "$quotient") {
            if (s.kind == H::SortKind::INT) {
                diags.error(ErrorCode::E_TYPE,
                            "'$quotient' is not defined on $int by TPTP itself; use "
                            "$quotient_e, $quotient_t or $quotient_f",
                            loc);
                return nullptr;
            }
            noteTotalDivision(loc);
            return H::mkOp(H::Op::DIV_REAL, args, loc);
        }
        if (kIntQuotient.count(name) != 0) {
            if (s.kind != H::SortKind::INT) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + name + "' is $int-only in TPTP; the arguments have "
                                "sort " + H::toString(s),
                            loc);
                return nullptr;
            }
            noteTotalDivision(loc);
            return H::mkOp(kIntQuotient.at(name), args, loc);
        }
        // $floor and $ceiling on $real, exactly: floor(x) = to_real(to_int(x))
        // and ceiling(x) = to_real(-to_int(-x)); on $int both are the identity.
        if (name == "$floor") {
            if (s.kind == H::SortKind::INT) { return args[0]; }
            return H::mkOp(H::Op::TO_REAL, {H::mkOp(H::Op::TO_INT, {args[0]}, loc)}, loc);
        }
        if (name == "$ceiling") {
            if (s.kind == H::SortKind::INT) { return args[0]; }
            return H::mkOp(H::Op::TO_REAL,
                           {H::mkOp(H::Op::NEG,
                                    {H::mkOp(H::Op::TO_INT,
                                             {H::mkOp(H::Op::NEG, {args[0]}, loc)}, loc)},
                                    loc)},
                           loc);
        }
        if (name == "$truncate") {
            if (s.kind == H::SortKind::INT) { return args[0]; }
            H::ExprPtr floor =
                H::mkOp(H::Op::TO_REAL, {H::mkOp(H::Op::TO_INT, {args[0]}, loc)}, loc);
            H::ExprPtr ceiling = H::mkOp(
                H::Op::TO_REAL,
                {H::mkOp(H::Op::NEG,
                         {H::mkOp(H::Op::TO_INT,
                                  {H::mkOp(H::Op::NEG, {args[0]}, loc)}, loc)},
                         loc)},
                loc);
            return H::mkOp(H::Op::ITE,
                           {H::mkOp(H::Op::GE, {args[0], H::mkReal("0.0", loc)}, loc),
                            floor, ceiling},
                           loc);
        }
        if (name == "$to_int") {
            if (s.kind == H::SortKind::INT) { return args[0]; }
            return H::mkOp(H::Op::TO_INT, args, loc);
        }
        if (name == "$to_rat" || name == "$to_real") {
            if (s.kind == H::SortKind::REAL) { return args[0]; }
            return H::mkOp(H::Op::TO_REAL, args, loc);
        }
        // $is_int: literal true on an $int argument, the real predicate else.
        if (s.kind == H::SortKind::INT) { return H::mkBool(true, loc); }
        return H::mkOp(H::Op::IS_INT, args, loc);
    }

    /** Commit a term-position application whose sort decides the use: Bool is
     *  a predicate use, anything else a function use (TXF branch positions). */
    bool commitBySort(const H::ExprPtr& expression, Uir::Diagnostics& diags) {
        if (!expression || expression->kind != H::ExprKind::APPLY) { return true; }
        return commitUse(expression,
                         expression->sort.kind == H::SortKind::BOOL
                             ? SymbolUse::PREDICATE
                             : SymbolUse::TERM,
                         diags);
    }

    /** `$ite(formula, then, else)`. The branches are terms; per the TPTP
     *  grammar note, a branch that "does not look like a term" must be
     *  parenthesized, which is exactly what the term parser reads back. */
    H::ExprPtr iteTerm(Uir::Diagnostics& diags, Uir::SourceLoc loc) {
        if (!eat("(")) {
            diags.error(ErrorCode::E_PARSE, "$ite is `$ite(formula, then, else)`", loc);
            return nullptr;
        }
        H::ExprPtr cond = formula(diags);
        if (!cond) { return nullptr; }
        if (!eat(",")) {
            diags.error(ErrorCode::E_PARSE, "$ite is `$ite(formula, then, else)`",
                        at(peek().line));
            return nullptr;
        }
        H::ExprPtr then = term(diags, true);
        if (!then || !commitBySort(then, diags)) { return nullptr; }
        if (!eat(",")) {
            diags.error(ErrorCode::E_PARSE, "$ite is `$ite(formula, then, else)`",
                        at(peek().line));
            return nullptr;
        }
        H::ExprPtr els = term(diags, true);
        if (!els || !commitBySort(els, diags)) { return nullptr; }
        if (!eat(")")) {
            diags.error(ErrorCode::E_PARSE, "expected ')'", at(peek().line));
            return nullptr;
        }
        if (!H::sameSort(then->sort, els->sort)) {
            diags.error(ErrorCode::E_TYPE,
                        "$ite branches must have the same sort; got "
                            + H::toString(then->sort) + " and "
                            + H::toString(els->sort),
                        loc);
            return nullptr;
        }
        return H::mkOp(H::Op::ITE, {cond, then, els}, loc);
    }

    // ---- TXF $let ----------------------------------------------------------
    //
    // `$let(types, defns, body)` is expanded at parse time: each definition's
    // body is parsed once with its LHS variables bound, and every use inlines
    // it with argument substitution. A definition that references itself,
    // directly or transitively, would make inlining diverge and is refused by
    // name -- caught at the forward edge, since the type part (which comes
    // first) already names every definition.

    LetDef* lookupLet(const std::string& name) {
        for (auto frame = let_frames_.rbegin(); frame != let_frames_.rend(); ++frame) {
            const auto found = frame->find(name);
            if (found != frame->end()) { return &found->second; }
        }
        return nullptr;
    }

    H::ExprPtr letTerm(Uir::Diagnostics& diags, Uir::SourceLoc loc) {
        if (!eat("(")) {
            diags.error(ErrorCode::E_PARSE, "$let is `$let(types, defns, body)`", loc);
            return nullptr;
        }
        let_frames_.emplace_back();
        // Popped on every path: a nested $let in a definition body pushes
        // another frame, and the deque keeps outer frames' entries addressable.
        struct FramePop {
            TptpParser& self;
            ~FramePop() { self.let_frames_.pop_back(); }
        } pop{*this};

        const auto oneTyping = [&]() -> bool {
            std::string name;
            std::vector<H::Sort> params;
            H::Sort result;
            bool is_ttype = false;
            if (!typingCore(name, params, result, is_ttype, diags)) { return false; }
            if (is_ttype) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a sort declaration ('$tType') inside a $let type part is "
                            "not supported",
                            at(peek().line));
                return false;
            }
            LetDef def;
            def.param_sorts = std::move(params);
            def.result = result;
            if (!let_frames_.back().emplace(name, std::move(def)).second) {
                diags.error(ErrorCode::E_PARSE,
                            "the $let types declare '" + name + "' more than once",
                            at(peek().line));
                return false;
            }
            return true;
        };
        if (eat("[")) {
            do {
                if (!oneTyping()) { return nullptr; }
            } while (eat(","));
            if (!eat("]")) {
                diags.error(ErrorCode::E_PARSE, "expected ']' after the $let types",
                            at(peek().line));
                return nullptr;
            }
        } else if (!oneTyping()) {
            return nullptr;
        }
        if (!eat(",")) {
            diags.error(ErrorCode::E_PARSE, "$let is `$let(types, defns, body)`",
                        at(peek().line));
            return nullptr;
        }
        if (eat("[")) {
            do {
                if (!letDefn(diags)) { return nullptr; }
            } while (eat(","));
            if (!eat("]")) {
                diags.error(ErrorCode::E_PARSE,
                            "expected ']' after the $let definitions", at(peek().line));
                return nullptr;
            }
        } else if (!letDefn(diags)) {
            return nullptr;
        }
        for (const auto& [name, def] : let_frames_.back()) {
            if (!def.ready) {
                diags.error(ErrorCode::E_PARSE,
                            "the $let type declaration of '" + name
                                + "' has no matching definition",
                            at(peek().line));
                return nullptr;
            }
        }
        if (!eat(",")) {
            diags.error(ErrorCode::E_PARSE, "$let is `$let(types, defns, body)`",
                        at(peek().line));
            return nullptr;
        }
        H::ExprPtr body = term(diags);
        if (!body) { return nullptr; }
        if (!eat(")")) {
            diags.error(ErrorCode::E_PARSE, "expected ')' after the $let body",
                        at(peek().line));
            return nullptr;
        }
        noteLetInlining(loc);
        return body;
    }

    /** One `name(X, ...) := term` definition. The LHS variables are bound --
     *  with the sorts the type part declared for `name` -- while the body is
     *  parsed, so occurrences of them in the body are ordinary bound-variable
     *  references that letUse substitutes. */
    bool letDefn(Uir::Diagnostics& diags) {
        const Tok t = peek();
        if (t.kind != Tok::IDENT || t.text.empty()
            || (!t.single_quoted && t.text.front() == '$')) {
            diags.error(ErrorCode::E_PARSE,
                        "a $let definition is `name(X, ...) := term`", at(t.line));
            return false;
        }
        ++pos_;
        auto found = let_frames_.back().find(t.text);
        if (found == let_frames_.back().end()) {
            diags.error(ErrorCode::E_PARSE,
                        "the $let definition of '" + t.text
                            + "' has no type declaration in the $let types",
                        at(t.line));
            return false;
        }
        LetDef& def = found->second;
        if (def.ready) {
            diags.error(ErrorCode::E_PARSE,
                        "the $let defines '" + t.text + "' more than once", at(t.line));
            return false;
        }
        std::vector<std::string> formal_sources;
        if (eat("(")) {
            for (;;) {
                if (peek().kind != Tok::VAR) {
                    diags.error(ErrorCode::E_PARSE,
                                "a $let definition's left-hand side takes distinct "
                                "variables; got '" + peek().text + "'",
                                at(peek().line));
                    return false;
                }
                const std::string v = peek().text;
                ++pos_;
                const std::size_t idx = formal_sources.size();
                if (idx >= def.param_sorts.size()) {
                    diags.error(ErrorCode::E_TYPE,
                                "the $let definition of '" + t.text
                                    + "' has more parameters than its declared type",
                                at(t.line));
                    return false;
                }
                if (std::find(formal_sources.begin(), formal_sources.end(), v)
                    != formal_sources.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "$let formal '" + v + "' occurs more than once",
                                at(t.line));
                    return false;
                }
                std::string target = v;
                auto& scope = bound_names_[v];
                if (!scope.empty()) {
                    target = "tptp_shadow_" + std::to_string(++binder_serial_);
                }
                scope.push_back(BoundVar{target, def.param_sorts[idx]});
                def.formals.push_back({target, def.param_sorts[idx]});
                formal_sources.push_back(v);
                if (eat(",")) { continue; }
                break;
            }
            if (!eat(")")) {
                diags.error(ErrorCode::E_PARSE, "expected ')'", at(peek().line));
                return false;
            }
        }
        if (def.formals.size() != def.param_sorts.size()) {
            diags.error(ErrorCode::E_TYPE,
                        "the $let definition of '" + t.text + "' takes "
                            + std::to_string(def.formals.size())
                            + " parameters but its declared type has "
                            + std::to_string(def.param_sorts.size()),
                        at(t.line));
            return false;
        }
        if (!eat(":") || !eat("=")) {
            diags.error(ErrorCode::E_PARSE,
                        "a $let definition uses ':=' (<assignment>)", at(peek().line));
            return false;
        }
        H::ExprPtr rhs = term(diags);
        for (const std::string& v : formal_sources) {
            auto scope = bound_names_.find(v);
            if (scope == bound_names_.end()) { continue; }
            scope->second.pop_back();
            if (scope->second.empty()) { bound_names_.erase(scope); }
        }
        if (!rhs) { return false; }
        if (!H::sameSort(rhs->sort, def.result)) {
            diags.error(ErrorCode::E_TYPE,
                        "the $let definition of '" + t.text + "' declares result "
                            + H::toString(def.result) + " but defines a term of sort "
                            + H::toString(rhs->sort),
                        at(t.line));
            return false;
        }
        def.body = rhs;
        def.ready = true;
        return true;
    }

    /** A use of a $let-defined name: inline the definition, substituting the
     *  actual arguments for the formals. */
    H::ExprPtr letUse(const std::string& name, const LetDef& def,
                      Uir::Diagnostics& diags, Uir::SourceLoc loc) {
        if (!def.ready) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "the $let definition of '" + name
                            + "' is recursive (directly or transitively); parse-time "
                              "inlining would not terminate",
                        loc);
            return nullptr;
        }
        std::vector<H::ExprPtr> args;
        if (eat("(")) {
            for (;;) {
                H::ExprPtr a = term(diags);
                if (!a) { return nullptr; }
                args.push_back(a);
                if (eat(",")) { continue; }
                break;
            }
            if (!eat(")")) {
                diags.error(ErrorCode::E_PARSE, "expected ')'", at(peek().line));
                return nullptr;
            }
        }
        if (args.size() != def.formals.size()) {
            diags.error(ErrorCode::E_TYPE,
                        "'" + name + "' is defined in $let with "
                            + std::to_string(def.formals.size())
                            + " parameters but applied to " + std::to_string(args.size())
                            + " arguments",
                        loc);
            return nullptr;
        }
        std::unordered_map<std::string, H::ExprPtr> formals;
        for (std::size_t i = 0; i < args.size(); ++i) {
            if (!H::sameSort(args[i]->sort, def.formals[i].second)) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + name + "' is defined in $let with parameter "
                                + std::to_string(i + 1) + " of sort "
                                + H::toString(def.formals[i].second)
                                + " but the argument has sort "
                                + H::toString(args[i]->sort),
                            loc);
                return nullptr;
            }
            formals.emplace(def.formals[i].first, args[i]);
        }
        std::unordered_map<std::string, std::vector<std::string>> renames;
        return letExpand(def.body, formals, renames);
    }

    /** The substitution behind letUse. Every quantifier binder in the
     *  definition body is alpha-renamed fresh at each inlining, so a binder
     *  can never capture a variable free in a substituted argument. */
    H::ExprPtr letExpand(
        const H::ExprPtr& e,
        const std::unordered_map<std::string, H::ExprPtr>& formals,
        std::unordered_map<std::string, std::vector<std::string>>& renames) {
        if (!e) { return nullptr; }
        if (e->kind == H::ExprKind::BOUND_VAR) {
            const auto formal = formals.find(e->name);
            if (formal != formals.end()) { return formal->second; }
            const auto renamed = renames.find(e->name);
            if (renamed != renames.end() && !renamed->second.empty()) {
                return H::mkBoundVar(renamed->second.back(), e->sort, e->loc);
            }
            return e;
        }
        if (e->kind == H::ExprKind::FORALL || e->kind == H::ExprKind::EXISTS) {
            std::vector<H::Binder> binders;
            std::vector<std::string> sources;
            binders.reserve(e->binders.size());
            for (const H::Binder& b : e->binders) {
                const std::string fresh =
                    "tptp_let_" + std::to_string(++binder_serial_);
                renames[b.name].push_back(fresh);
                sources.push_back(b.name);
                binders.push_back(H::Binder{fresh, b.sort});
            }
            H::ExprPtr body = letExpand(e->args.front(), formals, renames);
            for (const std::string& n : sources) {
                auto stack = renames.find(n);
                stack->second.pop_back();
                if (stack->second.empty()) { renames.erase(stack); }
            }
            if (!body) { return nullptr; }
            return e->kind == H::ExprKind::FORALL
                       ? H::mkForall(binders, body, e->loc)
                       : H::mkExists(binders, body, e->loc);
        }
        if (e->args.empty()) { return e; }
        auto copy = std::make_shared<H::Expr>(*e);
        copy->args.clear();
        copy->args.reserve(e->args.size());
        for (const H::ExprPtr& a : e->args) {
            copy->args.push_back(letExpand(a, formals, renames));
        }
        return copy;
    }

    // ---- TFF/TXF type expressions ------------------------------------------

    /** One atomic TFF type: a builtin sort, a user sort (legal on the fly, no
     *  declaration needed), or a parenthesized atomic type. `is_ttype` marks
     *  the bare `$tType`, legal only as the whole right-hand side of a sort
     *  declaration. Type variables and applied type constructors are TF1
     *  polymorphism and are refused by name. */
    bool parseAtomicType(H::Sort& out, bool& is_ttype, Uir::Diagnostics& diags) {
        is_ttype = false;
        const Tok t = peek();
        if (t.kind == Tok::PUNCT && t.text == "[") {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "TXF tuple types ('[S, T]', <txf_tuple_type>) are not supported",
                        at(t.line));
            return false;
        }
        if (t.kind == Tok::PUNCT && t.text == "(") {
            ++pos_;
            if (!parseAtomicType(out, is_ttype, diags)) { return false; }
            if (!eat(")")) {
                diags.error(ErrorCode::E_PARSE, "expected ')' in the type",
                            at(peek().line));
                return false;
            }
            return true;
        }
        if (t.kind == Tok::VAR) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "TF1 polymorphic types (the type variable '" + t.text
                            + "') are not supported",
                        at(t.line));
            return false;
        }
        if (t.kind != Tok::IDENT) {
            diags.error(ErrorCode::E_PARSE, "expected a sort name, got '" + t.text + "'",
                        at(t.line));
            return false;
        }
        ++pos_;
        if (!t.single_quoted && t.text == "$tType") { is_ttype = true; return true; }
        if (!t.single_quoted && (t.text == "$o" || t.text == "$oType")) {
            out = H::Sort::boolean();
            return true;
        }
        if (!t.single_quoted && t.text == "$i") {
            out = H::Sort::uninterpreted(kUniverse);
            return true;
        }
        if (!t.single_quoted && t.text == "$int") {
            out = H::Sort::integer();
            return true;
        }
        if (!t.single_quoted && (t.text == "$rat" || t.text == "$real")) {
            out = H::Sort::real();
            return true;
        }
        if (!t.single_quoted && !t.text.empty() && t.text.front() == '$') {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "defined sort '" + t.text
                            + "' is not one of $i, $o, $int, $rat, $real",
                        at(t.line));
            return false;
        }
        if (isPunct("(")) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "type constructor '" + t.text
                            + "' applied to arguments is TF1 polymorphism, not TFF0",
                        at(t.line));
            return false;
        }
        out = H::Sort::uninterpreted(ordinarySortName(t));
        return true;
    }

    /** A mapping's result type: atomic, and not `$tType`. */
    bool parseResultType(H::Sort& out, Uir::Diagnostics& diags) {
        bool ttype = false;
        if (!parseAtomicType(out, ttype, diags)) { return false; }
        if (ttype) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'$tType' is only legal as the whole right-hand side of a "
                        "sort declaration; type constructors are TF1 polymorphism",
                        at(peek().line));
            return false;
        }
        return true;
    }

    /** A tff_top_level_type: an atomic type (a constant's sort), a mapping
     *  `(A * B) > R` or `A > R`, or the bare `$tType` of a sort declaration. */
    bool parseTopType(std::vector<H::Sort>& params, H::Sort& result, bool& is_ttype,
                      Uir::Diagnostics& diags) {
        is_ttype = false;
        if (isPunct("!") && pos_ + 1 < toks_.size() && toks_[pos_ + 1].text == ">") {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "TF1 polymorphic types ('!>') are not supported", at(peek().line));
            return false;
        }
        if (isPunct("[")) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "TXF tuple types ('[S, T]', <txf_tuple_type>) are not supported",
                        at(peek().line));
            return false;
        }
        if (isPunct("(")) {
            ++pos_;
            // `($tType)` -- a parenthesized atomic is the same atomic type.
            if (peek().kind == Tok::IDENT && !peek().single_quoted
                && peek().text == "$tType"
                && pos_ + 1 < toks_.size() && toks_[pos_ + 1].text == ")") {
                pos_ += 2;
                is_ttype = true;
                return true;
            }
            std::vector<H::Sort> members;
            bool inner_mapping = false;
            H::Sort inner_result;
            if (!parseProductType(members, inner_mapping, inner_result, diags)) {
                return false;
            }
            if (!eat(")")) {
                diags.error(ErrorCode::E_PARSE, "expected ')' in the type",
                            at(peek().line));
                return false;
            }
            if (inner_mapping) {
                // A parenthesized mapping is a tff_non_atomic_type.
                params = std::move(members);
                result = inner_result;
                return true;
            }
            if (eat(">")) {
                if (!parseResultType(result, diags)) { return false; }
                params = std::move(members);
                return true;
            }
            if (members.size() == 1) {
                result = members.front();
                return true;
            }
            diags.error(ErrorCode::E_PARSE,
                        "a product type must be followed by '> <result sort>'",
                        at(peek().line));
            return false;
        }
        bool ttype = false;
        H::Sort s;
        if (!parseAtomicType(s, ttype, diags)) { return false; }
        if (ttype) {
            if (isPunct(">") || isPunct("*")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "'$tType' is only legal as the whole right-hand side of a "
                            "sort declaration; type constructors are TF1 polymorphism",
                            at(peek().line));
                return false;
            }
            is_ttype = true;
            return true;
        }
        if (eat(">")) {
            if (!parseResultType(result, diags)) { return false; }
            params = {s};
            return true;
        }
        result = s;
        return true;
    }

    /** The inside of a parenthesized type: `unitary ('*' unitary)*` with an
     *  optional `> atomic` tail, which makes the group a parenthesized mapping
     *  (a tff_non_atomic_type). */
    bool parseProductType(std::vector<H::Sort>& members, bool& is_mapping,
                          H::Sort& map_result, Uir::Diagnostics& diags) {
        is_mapping = false;
        for (;;) {
            if (isPunct("!") && pos_ + 1 < toks_.size()
                && toks_[pos_ + 1].text == ">") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "TF1 polymorphic types ('!>') are not supported",
                            at(peek().line));
                return false;
            }
            if (isPunct("(")) {
                ++pos_;
                std::vector<H::Sort> sub;
                bool sub_mapping = false;
                H::Sort sub_result;
                if (!parseProductType(sub, sub_mapping, sub_result, diags)) {
                    return false;
                }
                if (!eat(")")) {
                    diags.error(ErrorCode::E_PARSE, "expected ')' in the type",
                                at(peek().line));
                    return false;
                }
                if (sub_mapping) {
                    diags.error(ErrorCode::E_PARSE,
                                "a mapping type cannot be a member of a product type",
                                at(peek().line));
                    return false;
                }
                members.insert(members.end(), sub.begin(), sub.end());
            } else {
                bool ttype = false;
                H::Sort s;
                if (!parseAtomicType(s, ttype, diags)) { return false; }
                if (ttype) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "'$tType' is only legal as the whole right-hand side of "
                                "a sort declaration; type constructors are TF1 polymorphism",
                                at(peek().line));
                    return false;
                }
                members.push_back(s);
            }
            if (eat("*")) { continue; }
            break;
        }
        if (isPunct(">")) {
            ++pos_;
            if (!parseResultType(map_result, diags)) { return false; }
            is_mapping = true;
        }
        return true;
    }

    /** `symbol : type`, optionally parenthesized -- the body of a `type` item
     *  and of each entry in a $let type part. */
    bool typingCore(std::string& name, std::vector<H::Sort>& params, H::Sort& result,
                    bool& is_ttype, Uir::Diagnostics& diags) {
        const bool parenthesized = eat("(");
        const int line = peek().line;
        if (peek().kind != Tok::IDENT || peek().text.empty()
            || (!peek().single_quoted && peek().text.front() == '$')) {
            diags.error(ErrorCode::E_PARSE,
                        "the left-hand side of a type declaration is an ordinary "
                        "atomic word",
                        at(line));
            return false;
        }
        name = peek().text;
        ++pos_;
        if (!eat(":")) {
            diags.error(ErrorCode::E_PARSE, "a type declaration is `symbol : type`",
                        at(line));
            return false;
        }
        if (!parseTopType(params, result, is_ttype, diags)) { return false; }
        if (isPunct("<")) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "TPTP subtype declarations ('<<', <tff_subtype>) are not "
                        "supported",
                        at(peek().line));
            return false;
        }
        if (parenthesized && !eat(")")) {
            diags.error(ErrorCode::E_PARSE, "expected ')' after the type declaration",
                        at(peek().line));
            return false;
        }
        return true;
    }

    /** The body of a `tff(name, type, symbol : signature)` item: updates the
     *  persistent typing environment and produces no formula. */
    bool atomTyping(Uir::Diagnostics& diags, int line) {
        std::string name;
        std::vector<H::Sort> params;
        H::Sort result;
        bool is_ttype = false;
        if (!typingCore(name, params, result, is_ttype, diags)) { return false; }
        if (toks_[pos_].kind != Tok::END) {
            diags.error(ErrorCode::E_PARSE,
                        "unexpected '" + toks_[pos_].text + "' after the type declaration",
                        at(toks_[pos_].line));
            return false;
        }
        if (is_ttype) {
            // A sort declaration; redeclaration is identical and legal. The
            // sort needs no declaration in the model -- the lowering registers
            // every uninterpreted sort at each use site.
            return true;
        }
        return declareTyped(name, params, result, at(line), diags);
    }

    /** Install a declared TFF/TXF signature. TPTP's own shape rules are
     *  E_TYPE: argument sorts cannot be $o, and a redeclaration must agree
     *  with what the symbol already has -- whether that is an earlier
     *  declaration (identical redeclaration is legal spec merging) or an
     *  ASSUMED default typing. */
    bool declareTyped(const std::string& name, const std::vector<H::Sort>& params,
                      const H::Sort& result, Uir::SourceLoc loc,
                      Uir::Diagnostics& diags) {
        for (std::size_t i = 0; i < params.size(); ++i) {
            if (params[i].kind == H::SortKind::BOOL) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + name + "' declares $o as an argument sort; TFF "
                                "argument sorts cannot be $o",
                            loc);
                return false;
            }
        }
        SignatureEntry& entry = declareSymbol(name, name, params.size(), loc);
        if (entry.has_type) {
            const bool same =
                entry.params.size() == params.size()
                && std::equal(entry.params.begin(), entry.params.end(), params.begin(),
                              [](const H::Sort& a, const H::Sort& b) {
                                  return H::sameSort(a, b);
                              })
                && H::sameSort(entry.result, result);
            if (same) {
                entry.assumed = false;
                return true;
            }
            diags.error(ErrorCode::E_TYPE,
                        "conflicting redeclaration of '" + name + "': it is "
                            + (entry.assumed ? "assumed " : "already declared ")
                            + signatureString(entry.params, entry.result)
                            + " and cannot be redeclared "
                            + signatureString(params, result),
                        std::move(loc));
            return false;
        }
        if (entry.use != SymbolUse::UNKNOWN) {
            // The symbol was already applied in an untyped (fof/cnf) item,
            // which fixed the blanket-$i reading; a declaration that disagrees
            // with it contradicts that use.
            const H::Sort i = H::Sort::uninterpreted(kUniverse);
            const bool fits_use =
                std::all_of(params.begin(), params.end(),
                            [&](const H::Sort& s) { return H::sameSort(s, i); })
                && (entry.use == SymbolUse::PREDICATE
                        ? result.kind == H::SortKind::BOOL
                        : H::sameSort(result, i));
            if (!fits_use) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + name + "' was already used untyped (every argument "
                                "and result $i) and cannot now be declared "
                                + signatureString(params, result),
                            std::move(loc));
                return false;
            }
        }
        entry.has_type = true;
        entry.assumed = false;
        entry.params = params;
        entry.result = result;
        return true;
    }

    static std::string signatureString(const std::vector<H::Sort>& params,
                                       const H::Sort& result) {
        if (params.empty()) { return H::toString(result); }
        std::string out = "(";
        for (std::size_t i = 0; i < params.size(); ++i) {
            if (i != 0) { out += " * "; }
            out += H::toString(params[i]);
        }
        return out + ") > " + H::toString(result);
    }

    static std::string hex(const std::string& value) {
        static const char digits[] = "0123456789abcdef";
        std::string out;
        out.reserve(value.size() * 2);
        for (unsigned char c : value) {
            out += digits[c >> 4];
            out += digits[c & 0x0f];
        }
        return out;
    }

    static std::string distinctParseName(const std::string& value) {
        return std::string(1, '\x1d') + "distinct:" + value;
    }

    static std::string distinctSourceName(const std::string& value) {
        std::string out = "\"";
        for (char c : value) {
            if (c == '\\' || c == '"') { out += '\\'; }
            out += c;
        }
        out += '"';
        return out;
    }

    static bool isDistinctParseName(const std::string& value) {
        return !value.empty() && value.front() == '\x1d';
    }

    static std::string ordinarySortName(const Tok& token) {
        // Encode every non-lower-word spelling, including source names that
        // themselves resemble an encoded name. This keeps the encoding
        // injective for quoted identifiers as well as ordinary lower words,
        // and keeps a user '$i' distinct from the builtin individual sort.
        if (!isSafeTargetSpelling(token.text)) {
            return "tptp$sort$" + hex(token.text);
        }
        return token.text;
    }

    static bool isSafeTargetSpelling(const std::string& value) {
        // Alpha-renamed binders occupy this target namespace. A legal source
        // constant with that spelling must be encoded, or printing a bound
        // variable and a free application would capture the free occurrence.
        if (value.rfind("tptp_shadow_", 0) == 0) { return false; }
        if (value.empty() || value == "true" || value == "false"
            || value == "let" || value == "forall" || value == "exists"
            || value == "match" || value == "par" || value == "as"
            || getOperKind(value) != NODE_KIND::NT_UNKNOWN
            || !std::islower(static_cast<unsigned char>(value.front()))) {
            return false;
        }
        return std::all_of(value.begin() + 1, value.end(), [](unsigned char c) {
            return std::isalnum(c) != 0 || c == '_';
        });
    }

    static std::string signatureKey(const std::string& parse_name, std::size_t arity) {
        return parse_name + std::string(1, '\x1e') + std::to_string(arity);
    }

    static std::string sourceSymbolId(const SignatureEntry& entry) {
        return "tptp:" + hex(entry.source_name) + "/" + std::to_string(entry.arity);
    }

    SignatureEntry& declareSymbol(const std::string& parse_name,
                                  const std::string& source_name,
                                  std::size_t arity, Uir::SourceLoc loc) {
        const std::string key = signatureKey(parse_name, arity);
        auto [found, inserted] = signature_.emplace(key, SignatureEntry{});
        if (inserted) {
            found->second.source_name = source_name;
            found->second.parse_name = parse_name;
            found->second.arity = arity;
            found->second.loc = std::move(loc);
        }
        return found->second;
    }

    bool setUse(SignatureEntry& entry, SymbolUse use, Uir::Diagnostics& diags,
                Uir::SourceLoc loc) {
        if (isDistinctParseName(entry.parse_name) && use != SymbolUse::TERM) {
            diags.error(ErrorCode::E_TYPE,
                        "distinct object " + entry.source_name
                            + " is an individual term, not a proposition or predicate",
                        std::move(loc));
            return false;
        }
        if (entry.has_type) {
            // The signature decides what a use must be: a $o result is a
            // predicate, anything else a function. An ASSUMED default is
            // usage-directed, so a first use in formula position revises the
            // assumed result from $i to $o (the predicate default) instead of
            // conflicting with the term default recorded at parse time.
            SymbolUse implied = entry.result.kind == H::SortKind::BOOL
                                    ? SymbolUse::PREDICATE
                                    : SymbolUse::TERM;
            if (entry.assumed && entry.use == SymbolUse::UNKNOWN
                && use == SymbolUse::PREDICATE && implied == SymbolUse::TERM) {
                entry.result = H::Sort::boolean();
                implied = SymbolUse::PREDICATE;
            }
            if (implied != use) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + entry.source_name + "' is "
                                + (entry.assumed ? "assumed " : "declared ")
                                + signatureString(entry.params, entry.result)
                                + " but is used as a "
                                + (use == SymbolUse::PREDICATE ? "predicate" : "function"),
                            std::move(loc));
                return false;
            }
        }
        if (entry.use == SymbolUse::UNKNOWN) {
            entry.use = use;
            return true;
        }
        if (entry.use == use) { return true; }
        diags.error(ErrorCode::E_TYPE,
                    "symbol '" + entry.source_name + "' with arity "
                        + std::to_string(entry.arity)
                        + " is used both as a function and as a predicate",
                    std::move(loc));
        return false;
    }

    bool commitUse(const H::ExprPtr& expression, SymbolUse use,
                   Uir::Diagnostics& diags) {
        if (!expression || expression->kind != H::ExprKind::APPLY) { return true; }
        const std::string key = signatureKey(expression->name, expression->args.size());
        const auto found = signature_.find(key);
        if (found == signature_.end()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "TPTP symbol use has no signature entry", expression->loc);
            return false;
        }
        return setUse(found->second, use, diags, expression->loc);
    }

    bool finalizeSignatureAndAxioms(Uir::Diagnostics& diags) {
        if (distinct_objects_.size() > 1) {
            H::Constraint axiom;
            axiom.loc = distinct_objects_.front()->loc;
            axiom.formula = H::mkOp(H::Op::DISTINCT, distinct_objects_, axiom.loc);
            model_->constraints.push_back(axiom);
            target_axioms_.push_back(axiom.formula);

            Uir::EncodingChoice choice;
            choice.site = axiom.loc.file + ":" + std::to_string(axiom.loc.line);
            choice.unified_op = "distinct-object";
            choice.strategy = "fresh-constants-plus-pairwise-distinct-axiom";
            choice.fidelity = Uir::Fidelity::exact();
            choice.rationale =
                "TPTP distinct objects denote themselves and pairwise different spellings are unequal; ordinary constants remain free to denote the same element";
            report_->addChoice(std::move(choice));
        }

        std::unordered_map<std::string, std::size_t> arities_per_name;
        std::unordered_set<std::string> reserved;
        for (const auto& [key, entry] : signature_) {
            ++arities_per_name[entry.source_name];
            if (!isDistinctParseName(entry.parse_name)) { reserved.insert(entry.parse_name); }
        }

        std::unordered_map<std::string, std::string> targets;
        std::unordered_map<std::string, H::Sort> result_sorts;
        bool has_overload = false;
        bool has_unsafe_spelling = false;
        for (auto& [key, entry] : signature_) {
            if (entry.use == SymbolUse::UNKNOWN) {
                // A TFF/TXF symbol declared (or default-typed) but never
                // applied: the signature, not a use site, says what it is.
                if (entry.has_type) {
                    entry.use = entry.result.kind == H::SortKind::BOOL
                                    ? SymbolUse::PREDICATE
                                    : SymbolUse::TERM;
                } else {
                    diags.error(ErrorCode::E_INTERNAL,
                                "TPTP symbol '" + entry.source_name
                                    + "' was parsed without a term/predicate classification",
                                entry.loc);
                    return false;
                }
            }
            const bool overloaded = arities_per_name[entry.source_name] > 1;
            const bool unsafe_spelling = !isDistinctParseName(entry.parse_name)
                                         && !isSafeTargetSpelling(entry.parse_name);
            if (!isDistinctParseName(entry.parse_name) && !overloaded
                && !unsafe_spelling) {
                entry.target_name = entry.parse_name;
            } else {
                has_overload = has_overload || overloaded;
                has_unsafe_spelling = has_unsafe_spelling || unsafe_spelling;
                const std::string base =
                    std::string(overloaded ? "tptp$arity$" : "tptp$symbol$")
                    + hex(entry.source_name) + "$" + std::to_string(entry.arity);
                entry.target_name = base;
                for (std::size_t suffix = 1; reserved.count(entry.target_name) != 0;
                     ++suffix) {
                    entry.target_name = base + "$" + std::to_string(suffix);
                }
                reserved.insert(entry.target_name);
            }
            targets.emplace(key, entry.target_name);
            result_sorts.emplace(key, entry.has_type
                                          ? entry.result
                                          : (entry.use == SymbolUse::PREDICATE
                                                 ? H::Sort::boolean()
                                                 : H::Sort::uninterpreted(kUniverse)));
        }

        if (has_overload) {
            Uir::EncodingChoice choice;
            choice.site = file_ + ":1";
            choice.unified_op = "arity-overloaded-symbol";
            choice.strategy = "arity-indexed-signature-morphism";
            choice.fidelity = Uir::Fidelity::exact();
            choice.rationale =
                "TPTP identifies overloaded symbols by spelling and arity, while SMT-LIB user symbols cannot be overloaded; each overloaded source identity is injectively renamed";
            report_->addChoice(std::move(choice));
        }
        if (has_unsafe_spelling) {
            Uir::EncodingChoice choice;
            choice.site = file_ + ":1";
            choice.unified_op = "quoted-atomic-word";
            choice.strategy = "injective-smt-symbol-encoding";
            choice.fidelity = Uir::Fidelity::exact();
            choice.rationale =
                "a TPTP atomic word is not a safe target identifier or collides with a target builtin; Phi assigns an injective ASCII name and beta records the inverse source identity";
            report_->addChoice(std::move(choice));
        }

        detail::TptpSymbolRenamer renamer(targets, result_sorts);
        for (H::Constraint& constraint : model_->constraints) {
            constraint.formula = renamer.apply(constraint.formula);
        }
        for (H::ExprPtr& axiom : target_axioms_) {
            axiom = renamer.apply(axiom);
        }

        std::vector<std::pair<std::string, const SignatureEntry*>> ordered;
        ordered.reserve(signature_.size());
        for (const auto& [key, entry] : signature_) {
            ordered.push_back({sourceSymbolId(entry), &entry});
        }
        std::sort(ordered.begin(), ordered.end(),
                  [](const auto& left, const auto& right) {
                      return left.first < right.first;
                  });
        for (const auto& [source_id, entry] : ordered) {
            const H::Sort result = entry->has_type
                                       ? entry->result
                                       : (entry->use == SymbolUse::PREDICATE
                                              ? H::Sort::boolean()
                                              : H::Sort::uninterpreted(kUniverse));
            const std::vector<H::Sort> domain =
                entry->has_type ? entry->params
                                : std::vector<H::Sort>(entry->arity,
                                                       H::Sort::uninterpreted(kUniverse));
            source_signature_.symbols.push_back(
                {source_id,
                 entry->use == SymbolUse::PREDICATE
                     ? Uir::Sem::SymbolKind::RELATION
                     : Uir::Sem::SymbolKind::FUNCTION,
                 domain, result});
            symbol_map_.push_back({source_id, entry->target_name});
        }
        return true;
    }

    std::string src_;
    std::string file_;
    std::string active_file_;
    std::string current_language_;
    H::ConstraintModelPtr model_;
    std::vector<Tok> toks_;
    std::size_t pos_ = 0;
    std::unordered_map<std::string, std::vector<BoundVar>> bound_names_;
    std::unordered_set<std::string> free_;
    // Cleared per item, including across files: source locations and implicit
    // quantifier scopes must never be borrowed from another clause.
    std::unordered_map<std::string, H::ExprPtr> cnf_variables_;
    std::unordered_map<std::string, SignatureEntry> signature_;
    std::vector<H::ExprPtr> conjectures_;
    std::unordered_set<std::string> distinct_object_names_;
    std::vector<H::ExprPtr> distinct_objects_;
    /** Active TXF `$let` frames, innermost last. A deque so a nested $let's
     *  push_back cannot invalidate a LetDef reference held by an outer frame's
     *  definition parser. */
    std::deque<std::unordered_map<std::string, LetDef>> let_frames_;
    std::vector<IncludeSelection*> selections_;
    Uir::Sem::Signature source_signature_;
    std::vector<Uir::Sem::SymbolMapping> symbol_map_;
    std::vector<Uir::Sem::Sentence> target_axioms_;
    Uir::TranslationReport* report_ = nullptr;   // set by parse(), never null after
    bool said_inverted_ = false;
    bool said_alpha_rename_ = false;
    bool said_total_division_ = false;
    bool said_let_inline_ = false;
    bool has_positive_conjecture_ = false;
    std::size_t binder_serial_ = 0;
};

class TptpLanguage : public Language {
public:
    TptpLanguage() {
        // cnf, fof, tff and txf: includes, all connectives, quantifiers,
        // equality, TFF/TXF typing and interpreted arithmetic. THF dispatches
        // to the separate monomorphic THF0 strong-Henkin adapter; general THF
        // remains explicitly partial and reports unsupported constructs.
        coverage_.total = 4;
        coverage_.supported = 3;
        coverage_.missing = {
            "THF outside the supported monomorphic THF0 Boolean/individual fragment (include namespaces, polymorphism, interpreted $int/$real, quoted atoms, and unsupported syntax)"};
    }

    std::string id() const override { return "tptp"; }
    std::string displayName() const override { return "TPTP (CNF/FOF/TFF/TXF/THF0 fragment)"; }
    std::string version() const override { return "cnf,fof,tff,txf,thf0-monomorphic-henkin-v1"; }
    std::vector<std::string> extensions() const override { return {".p", ".tptp", ".ax"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions&) override {
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
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        if (containsStatement(src, "thf") || containsStatement(src, "include")) {
            using namespace ThfPrototype;
            const char* phase = "scanning source statements and includes";
            try {
                std::optional<ThfFile> file;
                {
                    FunctionHirBuilder builder;
                    ThfFileParser parser(src, name, builder);
                    // The parsed file owns its terms, types and source locations.
                    // Release the reader's statement text before constructing
                    // the target representation alongside the source term DAG.
                    if (parser.hasThfStatements()) {
                        phase = "parsing typed higher-order terms";
                        file.emplace(parser.parse());
                    }
                }
                if (file) {
                    const bool has_conjecture = std::any_of(
                        file->formulas.begin(), file->formulas.end(),
                        [](const ThfAnnotatedFormula& formula) {
                            return formula.role == "conjecture";
                        });
                    phase = "encoding higher-order terms";
                    auto model = std::make_shared<H::ConstraintModel>();
                    {
                        StrongHenkinEncoding encoding(*model);
                        encoding.encode(*file);
                    }
                    // Contract construction needs only the completed HIR and
                    // conjecture mode. It must not overlap with the source DAG
                    // or the encoder's now-obsolete lookup tables.
                    file.reset();
                    phase = "building the semantic contract";
                    out.report.addChoice({"tptp-thf0-henkin", "typed higher-order formula",
                        "strong-type-code-henkin", Uir::Fidelity::exact(),
                        "generic TypeCode/application, logical-constant, I/K/S, choice, "
                        "function-extensionality and source-lambda axioms preserve the "
                        "supported monomorphic THF0 Henkin semantics"});
                    out.semantics.add(Uir::Sem::tptpThfToRelationalContract(
                        *model, out.report.fidelity(), has_conjecture));
                    // Publish only after complete report/contract assembly.
                    out.model = std::move(model);
                    return out;
                }
            } catch (const std::bad_alloc&) {
                out.diagnostics.error(ErrorCode::E_RESOURCE,
                    std::string("TPTP THF exhausted memory while ") + phase);
                return out;
            } catch (const ThfParseError& error) {
                const ErrorCode code = error.kind() == ThfParseError::Kind::IO
                    ? ErrorCode::E_IO
                    : error.kind() == ThfParseError::Kind::UNSUPPORTED
                        ? ErrorCode::E_UNSUPPORTED_CONSTRUCT : ErrorCode::E_PARSE;
                out.diagnostics.error(code,
                    std::string("TPTP THF parse/unsupported construct: ") + error.what(),
                    Uir::SourceLoc{error.source().file,
                        static_cast<int>(error.source().line),
                        static_cast<int>(error.source().column)});
                return out;
            } catch (const std::invalid_argument& error) {
                out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    std::string("TPTP THF unsupported semantics: ") + error.what());
                return out;
            } catch (const std::exception& error) {
                out.diagnostics.error(ErrorCode::E_INTERNAL,
                    std::string("TPTP THF lowering failed: ") + error.what());
                return out;
            }
        }
        try {
            TptpParser p(src, name);
            out.model = p.parse(out.diagnostics, out.report);
            if (out.model) {
                out.semantics.add(Uir::Sem::tptpToRelationalContract(
                    *out.model, out.report.fidelity(), p.hasPositiveConjecture(),
                    p.takeSourceSignature(), p.takeSymbolMap(), p.takeTargetAxioms()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("tptp frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkTptpLanguage() { return std::make_shared<TptpLanguage>(); }

} // namespace SOMTParser::Lang
