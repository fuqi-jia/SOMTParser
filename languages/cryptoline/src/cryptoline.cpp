/* -*- Source -*-
 * CryptoLine frontend.
 *
 * The format is docs/languages/cryptoline.md; its `implicit-constraints` block
 * is the specification this file implements, and each entry has a fixture in
 * languages/cryptoline/instances.
 *
 * **The width is part of the arithmetic, not an annotation on it.** Every
 * CryptoLine variable declares a bit width and a signedness, and every operation
 * wraps at that width. Translating to unbounded `Int` is not a relaxation -- it
 * is a *different* arithmetic, one in which `mull` never overflows and the carry
 * outputs the program depends on are always zero. So variables are BitVec and
 * operations are bit-vector operations, throughout.
 *
 * **And that makes the signedness declaration decide a conversion whose two
 * readings are indistinguishable downstream.** A postcondition's algebraic half
 * (`eqn sum + carry * 2**64 = a * b + c`) is integer arithmetic over the VALUES
 * of those bit-vectors, so each operand is lifted to Int -- by `bv2nat` for a
 * `uintN` variable and by `bv2int` for a `sintN` one. The two read the same bits
 * as `[0, 2^w)` and as `[-2^(w-1), 2^(w-1))`; picking the wrong one shifts every
 * negative value by exactly 2^w, and both are BitVec -> Int, so nothing
 * downstream can tell. The declaration is the only evidence there is, which is
 * why the lift is driven by it and never by context.
 *
 * The carry outputs and the split identity are the two places a translation
 * silently loses a value the program then uses:
 *
 *   * `adds carry sum x y` produces the carry as DATA. Dropping it leaves a
 *     variable the rest of the program reads and nothing defines.
 *   * `split hi lo x n` redistributes one value across two, and the identity
 *     `x = hi * 2^n + lo` relating the pieces to the whole has to be ASSERTED.
 *     Assuming it -- declaring hi and lo and moving on -- leaves them
 *     unconstrained, and the postcondition then proves nothing about `x`.
 *
 * `cut` is a *proof structure*: it splits the verification into independent
 * fragments, each proved separately with the previous fragment's cut
 * predicates as its ONLY precondition ("starts afresh with the predicate
 * assumed" -- doc/cryptoline.pdf; ast/cryptoline.ml: evisit_with_pwss resets
 * the visited program at each cut). One instance is then N obligations on N
 * prefixes, and a `ConstraintModel` is one query -- so each fragment's
 * refutation is a disjunct of the emitted query (UNSAT iff every fragment
 * verifies), tagged with its fragment index so the check_index option (the
 * VMT/MoXI selector idiom) can emit one fragment as one measurable unit.
 * Dropping the chaining -- carrying the whole path into every fragment, or
 * forgetting the cut predicates -- is the unsound shape §6 of the format
 * document lists.
 *
 * Procedures compose by the official rule (parsers/common.ml: parse_call_at /
 * parse_inline_at / parse_inlinespec_at): `call` is the CONTRACT (assert the
 * precondition, havock the outputs, assume the postcondition -- an inout
 * actual's entry value captured by a fresh ghost), `inline` is the BODY
 * spliced at the call site with the formals bound to the actuals, and
 * `inlinespec` is the body havocked plus the contract. Every procedure is
 * registered in file order -- its body validated in a scratch scope -- and
 * the entry procedure (main, or the only one) is translated. Ghost variables
 * are specification-only constants whose predicate is always assumed.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/cryptoline.h"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <filesystem>
#include <fstream>
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

struct Tok {
    enum Kind { IDENT, NUM, PUNCT, END } kind = END;
    std::string text;
    int line = 1;
};

class Lexer {
public:
    explicit Lexer(std::string s) : s_(std::move(s)) {}

    Tok next() {
        skip();
        Tok t;
        t.line = line_;
        if (i_ >= s_.size()) { t.kind = Tok::END; return t; }
        const char c = s_[i_];
        if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
            const std::size_t start = i_;
            while (i_ < s_.size()
                   && (std::isalnum(static_cast<unsigned char>(s_[i_])) || s_[i_] == '_')) {
                ++i_;
            }
            t.kind = Tok::IDENT;
            t.text = s_.substr(start, i_ - start);
            return t;
        }
        if (std::isdigit(static_cast<unsigned char>(c))) {
            const std::size_t start = i_;
            if (c == '0' && i_ + 1 < s_.size()
                && (s_[i_ + 1] == 'x' || s_[i_ + 1] == 'X')) {
                i_ += 2;
                while (i_ < s_.size()
                       && std::isxdigit(static_cast<unsigned char>(s_[i_]))) { ++i_; }
            } else if (c == '0' && i_ + 1 < s_.size()
                       && (s_[i_ + 1] == 'b' || s_[i_ + 1] == 'B')) {
                i_ += 2;
                while (i_ < s_.size() && (s_[i_] == '0' || s_[i_] == '1')) { ++i_; }
            } else {
                while (i_ < s_.size()
                       && std::isdigit(static_cast<unsigned char>(s_[i_]))) { ++i_; }
            }
            t.kind = Tok::NUM;
            t.text = s_.substr(start, i_ - start);
            return t;
        }
        // `**` is exponentiation and `&&` separates the two halves of a
        // condition; both must not be split into two single-character tokens.
        // `>>a` is the infix arithmetic shift, `/\\` and `\\/` the predicate
        // conjunction and disjunction of the official grammar
        // (parsers/cryptolineLexer.mll: SAROP, LANDOP, LOROP). `>>a` must
        // precede `>>` or the longer token is never seen.
        static const char* kMulti[] = {
            "<=u", ">=u", "<=s", ">=s", "<u", ">u", "<s", ">s",
            ">>a", "/\\", "\\/", "**", "&&", "<<", ">>", "<=", ">=", "!=",
            nullptr};
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
            else if (c == '#') { while (i_ < s_.size() && s_[i_] != '\n') { ++i_; } }
            else if (c == '(' && s_.compare(i_, 2, "(*") == 0) {
                i_ += 2;
                while (i_ + 1 < s_.size() && !(s_[i_] == '*' && s_[i_ + 1] == ')')) {
                    if (s_[i_] == '\n') { ++line_; }
                    ++i_;
                }
                i_ = i_ + 1 < s_.size() ? i_ + 2 : s_.size();
            }
            else { return; }
        }
    }
    std::string s_;
    std::size_t i_ = 0;
    int line_ = 1;
};

/** A variable's declared type. Both halves matter and neither is decoration:
 *  the width is the arithmetic, and the signedness picks the Int lift. */
struct VarType {
    unsigned width = 0;
    bool     is_signed = false;
};

bool sameType(const VarType& lhs, const VarType& rhs) {
    return lhs.width == rhs.width && lhs.is_signed == rhs.is_signed;
}

struct Dest {
    std::string            name;
    std::optional<VarType> annotation;
};

/** A call/inline actual bound to a formal: either a caller variable (read
 *  dynamically, so an actual that is also an output sees its own updates)
 *  or a typed constant. */
struct InlineBinding {
    bool is_const = false;
    std::string actual;
    Uir::Hir::ExprPtr literal;
    VarType    type;
};

class ClParser {
public:
    ClParser(std::string src, std::string file, std::optional<std::size_t> check_index)
        : file_(std::move(file)), check_index_(check_index) {
        // Buffered rather than streamed, because the range half needs to look
        // ahead: a decimal literal there has no width of its own and takes the
        // one of the variable it is compared against, which may appear after it
        // (`rng 4 <= x`).
        Lexer lex(std::move(src));
        for (Tok k = lex.next(); k.kind != Tok::END; k = lex.next()) { toks_.push_back(k); }
        toks_.push_back(Tok{Tok::END, "", toks_.empty() ? 1 : toks_.back().line});
    }

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        report_ = &report;
        model_ = std::make_shared<H::ConstraintModel>();
        if (!program(diags)) { return nullptr; }
        if (check_index_ && *check_index_ > fragment_) {
            diags.error(ErrorCode::E_PARSE,
                        "check_index=" + std::to_string(*check_index_)
                            + " but the program has " + std::to_string(fragment_ + 1)
                            + (fragment_ == 0 ? " fragment" : " fragments")
                            + " (one more than its cut instructions)", at());
            return nullptr;
        }
        // A ConstraintModel is one query, so the fragments' refutations are
        // disjoined into it: UNSAT iff every fragment's every obligation
        // holds. check_index=k -- the VMT/MoXI query-selector idiom --
        // restricts the query to fragment k alone, which is the per-fragment
        // measurable unit docs/languages/cryptoline.md §4.4 wants.
        H::ExprPtr any_counterexample;
        for (const ObligationBranch& b : obligation_branches_) {
            if (check_index_ && b.fragment != *check_index_) { continue; }
            any_counterexample =
                any_counterexample ? H::mkOp(H::Op::OR, {any_counterexample, b.branch})
                                   : b.branch;
        }
        // No obligation of the (selected) fragment can fail => no
        // counterexample exists: UNSAT, the fragment verifies.
        if (!any_counterexample) { any_counterexample = H::mkBool(false, at()); }
        H::Constraint query;
        query.formula = std::move(any_counterexample);
        model_->constraints.push_back(std::move(query));
        if (fragment_ != 0 && report_ != nullptr) {
            // RECORDED: the fragment structure is invisible in the emitted
            // script -- one query is a disjunction of per-fragment branches --
            // but the chaining (each fragment proved against only the previous
            // cut's predicates) is the semantics, and the selector is the
            // measurable unit.
            Uir::EncodingChoice ch;
            ch.site       = "cut";
            ch.unified_op = "fragmented-refutation";
            ch.strategy   = "chained-per-fragment-branches";
            ch.fidelity   = Uir::Fidelity::exact();
            ch.rationale =
                "the program has " + std::to_string(fragment_ + 1)
                + " verification fragments delimited by cut instructions; each "
                  "fragment's obligations are refuted under ONLY the previous "
                  "cut's predicates (the official 'starts afresh': earlier "
                  "instructions and assumes are not carried), and the branches "
                  "are disjoined into this one query -- UNSAT iff every "
                  "fragment verifies"
                + (check_index_
                       ? "; check_index=" + std::to_string(*check_index_)
                             + " restricts this query to fragment "
                             + std::to_string(*check_index_)
                             + " alone -- the other fragments are separate "
                               "queries with their own verdicts, not part of "
                               "this one"
                       : "");
            report_->addChoice(std::move(ch));
        }
        return model_;
    }

    Uir::Sem::ModelProjection finalProjection() const {
        std::vector<std::pair<std::string, std::string>> final_versions(
            version_.begin(), version_.end());
        std::sort(final_versions.begin(), final_versions.end());
        Uir::Sem::ModelProjection projection;
        for (const auto& [source, target] : final_versions) {
            projection.observables.push_back(
                {source, target, Uir::Sem::ProjectionKind::DIRECT});
        }
        return projection;
    }

private:
    // ---- token helpers ---------------------------------------------------
    Uir::SourceLoc at() const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = tok().line;
        l.column = 1;
        return l;
    }
    const Tok& tok() const { return toks_[pos_]; }
    void eat() { if (pos_ + 1 < toks_.size()) { ++pos_; } }

    /** Is the token after the current one an `@`? Used only to tell CryptoLine's
     *  annotated `name@type` apart from a plain misspelled type, so the
     *  diagnostic names the construct rather than blaming the variable. */
    bool peekIsAt() const {
        return pos_ + 1 < toks_.size() && toks_[pos_ + 1].text == "@";
    }

    /** The bit width the current condition half is written at: the width of the
     *  first declared variable appearing in it, scanning to `&&` or `}`. A
     *  `rng` half compares same-width operands by construction, so one width
     *  describes the half -- and it is what an untyped decimal literal there
     *  means. Zero when the half mentions no variable. */
    unsigned halfWidth() const {
        for (std::size_t k = pos_; k < toks_.size(); ++k) {
            const Tok& x = toks_[k];
            if (x.kind == Tok::END) { break; }
            if (x.kind == Tok::PUNCT
                && (x.text == "&&" || x.text == "}" || x.text == ";")) { break; }
            if (x.kind == Tok::IDENT && x.text == "prove") { break; }
            if (x.kind != Tok::IDENT) { continue; }
            std::string scanned = x.text;
            if (const InlineBinding* binding = inlineBinding(scanned)) {
                if (binding->is_const) { continue; }
                scanned = binding->actual;
            }
            auto v = version_.find(scanned);
            if (v == version_.end()) { continue; }
            auto ty = types_.find(v->second);
            if (ty != types_.end()) { return ty->second.width; }
        }
        return 0;
    }
    bool isIdent(const char* s) const { return tok().kind == Tok::IDENT && tok().text == s; }
    bool isPunct(const char* s) const { return tok().kind == Tok::PUNCT && tok().text == s; }

    /** Is the `(` at the current position opening a nested PREDICATE rather
     *  than a parenthesized operand of a comparison? Decided by what follows
     *  the matching `)`: a relational operator (or an expression continuation
     *  like `@`, `**`, an arithmetic or a bit-wise infix) means the group is an
     *  operand; anything else -- a half separator, a connective, a list
     *  separator, the end of the half -- means the group itself is the
     *  predicate. Looking for predicate keywords INSIDE the group instead
     *  misreads `(and x y) = 0`, where `and` is the bit-wise expression
     *  operator. */
    bool parenStartsPredicate() const { return parenStartsPredicateAt(pos_); }

    bool parenStartsPredicateAt(std::size_t from) const {
        if (from >= toks_.size() || toks_[from].kind != Tok::PUNCT
            || toks_[from].text != "(") {
            return false;
        }
        unsigned depth = 0;
        for (std::size_t k = from; k < toks_.size(); ++k) {
            const Tok& x = toks_[k];
            if (x.kind == Tok::END) { return false; }
            if (x.kind == Tok::PUNCT && x.text == "(") { ++depth; continue; }
            if (x.kind == Tok::PUNCT && x.text == ")") {
                if (--depth != 0) { continue; }
                if (k + 1 >= toks_.size()) { return true; }
                const Tok& after = toks_[k + 1];
                if (after.kind == Tok::PUNCT
                    && (after.text == "=" || after.text == "<" || after.text == ">"
                        || after.text == "<=" || after.text == ">="
                        || after.text == "<u" || after.text == ">u"
                        || after.text == "<=u" || after.text == ">=u"
                        || after.text == "<s" || after.text == ">s"
                        || after.text == "<=s" || after.text == ">=s"
                        || after.text == "@" || after.text == "**"
                        || after.text == "+" || after.text == "-"
                        || after.text == "*" || after.text == "<<"
                        || after.text == ">>" || after.text == ">>a"
                        || after.text == "&" || after.text == "|"
                        || after.text == "^")) {
                    return false;
                }
                return true;
            }
        }
        return false;
    }

    bool expect(const char* s, Uir::Diagnostics& diags) {
        if (!isPunct(s)) {
            diags.error(ErrorCode::E_PARSE,
                        "expected '" + std::string(s) + "', got '" + tok().text + "'", at());
            return false;
        }
        eat();
        return true;
    }

    // ---- SSA -------------------------------------------------------------
    //
    // "the program is straight-line SSA after unrolling => each assignment
    // defines a new version, so a translation that reuses one variable per name
    // conflates distinct values". CryptoLine source does reuse names, so the
    // versioning has to happen here: `mov x a; mov x b;` defines two values and
    // a later reference means the second.

    /** The current SSA name for a source name, or empty if never defined.
     *  Under an `inline`, a formal parameter resolves through the binding
     *  stack to the actual (parsers/common.ml: parse_inline_at substitutes
     *  formals by actuals textually); a formal bound to a constant actual is
     *  not a variable and resolves to empty here -- the expression readers
     *  substitute the literal before calling this. */
    std::string current(const std::string& name) const {
        std::string resolved = name;
        for (auto it = inline_maps_.rbegin(); it != inline_maps_.rend(); ++it) {
            auto b = it->find(resolved);
            if (b == it->end()) { break; }
            if (b->second.is_const) { return std::string(); }
            resolved = b->second.actual;
        }
        auto it = version_.find(resolved);
        return it == version_.end() ? std::string() : it->second;
    }

    /** The inline binding for a source name, innermost scope first. */
    const InlineBinding* inlineBinding(const std::string& name) const {
        for (auto it = inline_maps_.rbegin(); it != inline_maps_.rend(); ++it) {
            auto b = it->find(name);
            if (b != it->end()) { return &b->second; }
        }
        return nullptr;
    }

    /** Introduce the next version of `name` at type `ty`, declare it, and return
     *  its SSA name. Under an `inline`, the formal's definition lands on the
     *  actual variable (parsers/common.ml: textual substitution); a formal
     *  bound to a constant actual can never be a destination (its actual is a
     *  variable -- the call checks). */
    std::string define(const std::string& name, VarType ty) {
        std::string resolved = name;
        for (auto it = inline_maps_.rbegin(); it != inline_maps_.rend(); ++it) {
            auto b = it->find(resolved);
            if (b == it->end()) { break; }
            if (b->second.is_const) { break; }
            resolved = b->second.actual;
        }
        const unsigned n = ++counter_[resolved];
        const std::string ssa =
            n == 1 ? resolved : resolved + "!" + std::to_string(n);
        version_[resolved] = ssa;
        types_[ssa] = ty;
        if (record_assigned_ && ghosts_.count(resolved) == 0) {
            assigned_in_body_[resolved] = ty;
        }
        H::VarDecl d;
        d.name = ssa;
        d.sort = H::Sort::bitvec(ty.width);
        d.loc = at();
        d.auxiliary = n > 1;
        model_->decls.push_back(d);
        return ssa;
    }

    H::ExprPtr ref(const std::string& ssa) const {
        return H::mkIdent(ssa, H::Sort::bitvec(types_.at(ssa).width));
    }

    /** The identifiers (SSA names) an expression mentions. Bound variables
     *  (eqmod's existential multipliers) are not identifiers and are not
     *  collected. */
    static void collectIdents(const H::ExprPtr& e,
                              std::unordered_set<std::string>& out) {
        if (e->kind == H::ExprKind::IDENT) { out.insert(e->name); }
        for (const H::ExprPtr& a : e->args) { collectIdents(a, out); }
    }

    /** Split a predicate into its top-level conjuncts
     *  (ast/cryptoline.ml: split_eand/split_rand). */
    static void splitConjuncts(const H::ExprPtr& e, std::vector<H::ExprPtr>& out) {
        if (e->kind == H::ExprKind::OP && e->op == H::Op::AND) {
            for (const H::ExprPtr& a : e->args) { splitConjuncts(a, out); }
            return;
        }
        out.push_back(e);
    }

    /** Substitute identifiers by expressions -- a call's formals-to-actuals
     *  map over the callee's recorded pre/postconditions
     *  (parsers/common.ml: subst_maps_of_list over the formal versions). */
    static H::ExprPtr substIdents(
        const H::ExprPtr& e,
        const std::unordered_map<std::string, H::ExprPtr>& map) {
        if (e->kind == H::ExprKind::IDENT) {
            const auto it = map.find(e->name);
            return it == map.end() ? e : it->second;
        }
        if (e->args.empty()) { return e; }
        auto copy = std::make_shared<H::Expr>(*e);
        for (H::ExprPtr& a : copy->args) { a = substIdents(a, map); }
        return copy;
    }

    /** The fact-selecting prove-with hints of one predicate (doc/cryptoline.pdf:
     *  "Sometimes a predicate has to be proved with facts that have been cut
     *  off"). The solver-selection hints (algebra/range solver, orders,
     *  eqfirst, args) carry no denotation and never reach here. */
    struct ProveWith {
        bool precondition = false;
        bool all_cuts = false;
        bool all_assumes = false;
        bool all_ghosts = false;
        std::vector<unsigned> cuts;
    };

    /** A predicate with the side it was parsed on and its prove-with hints. */
    struct PredClause {
        H::ExprPtr expr;
        bool algebraic = false;
        ProveWith hints;
    };

    /** One refutation branch: a counterexample to one obligation of one
     *  fragment. The fragment index is what check_index selects by. */
    struct ObligationBranch {
        H::ExprPtr branch;
        std::size_t fragment = 0;
    };

    /** A registered procedure declaration. The body is kept as a TOKEN RANGE:
     *  `inline` re-translates it at the call site with the formals bound to
     *  the actuals (the parser is token-buffered), while `call`/`inlinespec`
     *  substitute only the pre-/postconditions (parsers/common.ml:
     *  parse_call_at / parse_inline_at / parse_inlinespec_at). */
    struct ProcDecl {
        std::string name;
        std::size_t ordinal = 0;   // file order: a call names an EARLIER proc
        std::vector<std::pair<std::string, VarType>> ins;    // inout formals
        std::vector<std::pair<std::string, VarType>> outs;   // out formals
        std::vector<PredClause> pre;     // over the formals' SSA names
        std::vector<PredClause> post;    // over the formals' final SSA names
        /** formal base name -> every SSA version the registration gave it
         *  (the postcondition may mention any of them; a call substitutes all
         *  by the actual). */
        std::unordered_map<std::string, std::vector<std::string>> formal_versions;
        std::unordered_map<std::string, VarType> assigned;   // written in the body
        std::unordered_set<std::string> assigned_inputs;     // formal inputs written
        std::unordered_set<std::string> post_formals;        // formals read in post
        /** Non-formal identifiers in the postcondition: legal only for the
         *  entry procedure (parsers/common.ml: parse_proc); program()
         *  reports them for callable procedures. */
        std::unordered_set<std::string> post_nonformals;
        std::size_t pre_begin = 0;     // token index of the precondition's '{'
        std::size_t body_begin = 0;    // token index of the first instruction
        std::size_t body_end = 0;      // token index of the postcondition's '{'
    };

    /** Where a parsed condition goes: the precondition and the assumes extend
     *  the path (and are recorded for the `precondition` resp. `all assumes`
     *  hints -- the precondition is NOT an assume, ast/cryptoline.ml's
     *  eprove_with_filter keeps them apart); obligations become refutation
     *  branches. */
    enum class Role { PRECONDITION, ASSUME, OBLIGATION };

    /** An instruction equation belongs to BOTH verification runs: the
     *  algebraic and the range side each model the program (verify/std.ml
     *  verifies the espec and the rspec separately). The fragment prefixes are
     *  reset at cuts -- "CryptoLine verifies the predicate and starts afresh
     *  with the predicate assumed" (doc/cryptoline.pdf) -- so an equation only
     *  reaches the obligations of its own fragment. */
    void assertFormula(const H::ExprPtr& f) {
        prefix_e_.push_back(f);
        prefix_r_.push_back(f);
    }

    /** Record failure of one proof obligation under the exact prefix visible
     *  at its source location: the current fragment's assumptions on the
     *  obligation's SIDE, plus the facts its prove-with hints select for this
     *  verification only (ast/cryptoline.ml: eprove_with_filter -- the
     *  selected facts are prepended to the fragment's program for this
     *  predicate). Later assumptions cannot erase this branch. */
    void addObligation(const H::ExprPtr& obligation, bool algebraic,
                       const ProveWith& hints, const Uir::SourceLoc& loc) {
        H::ExprPtr branch;
        const std::vector<H::ExprPtr>& prefix = algebraic ? prefix_e_ : prefix_r_;
        for (const H::ExprPtr& assumption : prefix) {
            branch = branch ? H::mkOp(H::Op::AND, {branch, assumption}) : assumption;
        }
        auto conjoin = [&branch](const H::ExprPtr& fact) {
            branch = branch ? H::mkOp(H::Op::AND, {branch, fact}) : fact;
        };
        if (hints.precondition) {
            for (const H::ExprPtr& fact : algebraic ? pre_e_ : pre_r_) {
                conjoin(fact);
            }
        }
        const std::vector<H::ExprPtr>& cuts = algebraic ? cuts_e_ : cuts_r_;
        for (const unsigned i : hints.cuts) { conjoin(cuts[i]); }
        if (hints.all_cuts) {
            for (const H::ExprPtr& fact : cuts) { conjoin(fact); }
        }
        if (hints.all_assumes) {
            for (const H::ExprPtr& fact : algebraic ? assumes_e_ : assumes_r_) {
                conjoin(fact);
            }
        }
        if (hints.all_ghosts) {
            for (const H::ExprPtr& fact : algebraic ? ghosts_e_ : ghosts_r_) {
                conjoin(fact);
            }
        }
        const H::ExprPtr failure = H::mkOp(H::Op::NOT, {obligation}, obligation->loc);
        branch = branch ? H::mkOp(H::Op::AND, {branch, failure}) : failure;
        obligation_branches_.push_back({std::move(branch), fragment_});
    }

    /** Safety and value-preservation obligations are bit-vector conditions:
     *  they belong to the range side's fragment (verify/smt.ml) and carry no
     *  prove-with hints. */
    void addObligation(const H::ExprPtr& obligation) {
        addObligation(obligation, false, ProveWith{}, obligation->loc);
    }

    H::ExprPtr bvZero(unsigned width, const Uir::SourceLoc& loc) const {
        return H::mkBitVec(binaryOf("0", width), width, loc);
    }

    H::ExprPtr bvOne(unsigned width, const Uir::SourceLoc& loc) const {
        return H::mkBitVec(binaryOf("1", width), width, loc);
    }

    H::ExprPtr integerValue(const H::ExprPtr& value, const VarType& type,
                            const Uir::SourceLoc& loc) const {
        return H::mkOp(type.is_signed ? H::Op::BV_TO_INT : H::Op::BV_TO_NAT,
                       {value}, loc);
    }

    /** The exact mathematical result represented in 2w bits must equal the
     * signed/unsigned extension of its low w-bit machine result. */
    H::ExprPtr extendedResultFits(const H::ExprPtr& full, const H::ExprPtr& low,
                                  const VarType& type,
                                  const Uir::SourceLoc& loc) const {
        const unsigned extra = full->sort.width - type.width;
        const H::Op extension = type.is_signed ? H::Op::BV_SIGN_EXTEND
                                                : H::Op::BV_ZERO_EXTEND;
        return H::mkOp(H::Op::EQ,
                       {full, H::mkBvExtend(extension, low, extra, loc)}, loc);
    }

    H::ExprPtr noOverflowAdd(const H::ExprPtr& lhs, const H::ExprPtr& rhs,
                             const VarType& type,
                             const Uir::SourceLoc& loc) const {
        const H::Op extension = type.is_signed ? H::Op::BV_SIGN_EXTEND
                                                : H::Op::BV_ZERO_EXTEND;
        const H::ExprPtr full = H::mkOp(
            H::Op::BV_ADD,
            {H::mkBvExtend(extension, lhs, type.width, loc),
             H::mkBvExtend(extension, rhs, type.width, loc)}, loc);
        const H::ExprPtr low = H::mkBvExtract(full, type.width - 1, 0, loc);
        return extendedResultFits(full, low, type, loc);
    }

    H::ExprPtr noOverflowSub(const H::ExprPtr& lhs, const H::ExprPtr& rhs,
                             const VarType& type,
                             const Uir::SourceLoc& loc) const {
        const H::Op extension = type.is_signed ? H::Op::BV_SIGN_EXTEND
                                                : H::Op::BV_ZERO_EXTEND;
        const H::ExprPtr full = H::mkOp(
            H::Op::BV_SUB,
            {H::mkBvExtend(extension, lhs, type.width, loc),
             H::mkBvExtend(extension, rhs, type.width, loc)}, loc);
        const H::ExprPtr low = H::mkBvExtract(full, type.width - 1, 0, loc);
        return extendedResultFits(full, low, type, loc);
    }

    H::ExprPtr noOverflowMul(const H::ExprPtr& lhs, const H::ExprPtr& rhs,
                             const VarType& type,
                             const Uir::SourceLoc& loc) const {
        const H::Op extension = type.is_signed ? H::Op::BV_SIGN_EXTEND
                                                : H::Op::BV_ZERO_EXTEND;
        const H::ExprPtr full = H::mkOp(
            H::Op::BV_MUL,
            {H::mkBvExtend(extension, lhs, type.width, loc),
             H::mkBvExtend(extension, rhs, type.width, loc)}, loc);
        const H::ExprPtr low = H::mkBvExtract(full, type.width - 1, 0, loc);
        return extendedResultFits(full, low, type, loc);
    }

    H::ExprPtr shiftSafety(const std::string& op, const H::ExprPtr& value,
                           const H::ExprPtr& amount, const VarType& type,
                           const Uir::SourceLoc& loc) const {
        const unsigned w = type.width;
        const H::ExprPtr width = H::mkBitVec(binaryOf(std::to_string(w), w), w, loc);
        const H::ExprPtr remaining =
            H::mkOp(H::Op::BV_SUB, {width, amount}, loc);
        const H::ExprPtr shifted_out = H::mkOp(
            op == "shl" ? H::Op::BV_LSHR : H::Op::BV_SHL,
            {value, remaining}, loc);
        H::ExprPtr zero_bits =
            H::mkOp(H::Op::EQ, {shifted_out, bvZero(w, loc)}, loc);
        if (op == "shl" && type.is_signed) {
            const H::ExprPtr one = bvOne(w, loc);
            const H::ExprPtr one_less =
                H::mkOp(H::Op::BV_SUB, {remaining, one}, loc);
            const H::ExprPtr sign_prefix =
                H::mkOp(H::Op::BV_ASHR, {value, one_less}, loc);
            const H::ExprPtr all_ones =
                H::mkBitVec("#b" + std::string(w, '1'), w, loc);
            return H::mkOp(
                H::Op::OR,
                {H::mkOp(H::Op::EQ, {sign_prefix, bvZero(w, loc)}, loc),
                 H::mkOp(H::Op::EQ, {sign_prefix, all_ones}, loc)}, loc);
        }
        if ((op == "shr" && type.is_signed) || (op == "sar" && !type.is_signed)) {
            const H::ExprPtr sign = H::mkBvExtract(value, w - 1, w - 1, loc);
            const H::ExprPtr nonnegative =
                H::mkOp(H::Op::EQ, {sign, H::mkBitVec("#b0", 1, loc)}, loc);
            return H::mkOp(H::Op::AND, {nonnegative, zero_bits}, loc);
        }
        return zero_bits;
    }

    // ---- types -----------------------------------------------------------

    /** A typed name, in EITHER of CryptoLine's two spellings.
     *
     *  `sint32 a` puts the type first; `a@sint32` puts the name first and the
     *  type after an `@`. Both are ordinary, and the annotated form is what the
     *  real inputs use -- nine of the seventeen upstream files open with
     *  `proc main(a@sint32, B@sint32, ...)`. Reading only the first spelling
     *  reported "'a' is not a supported type": true of `a`, and it sends the
     *  reader looking for a typo in a file whose type is spelled correctly one
     *  token later.
     *
     *  Told apart without lookahead past one token: a type name is `uintN`,
     *  `sintN` or `bit`, and a name followed by `@` cannot be any of those in
     *  the position a type would occupy. */
    bool typedName(std::string& name, VarType& out, Uir::Diagnostics& diags) {
        if (tok().kind == Tok::IDENT && peekIsAt()) {
            name = tok().text;
            eat();                                   // the name
            eat();                                   // '@'
            if (!typeName(out, diags)) { return false; }
            if (isPunct("[")) { return vectorTypeRefused(diags); }
            return true;
        }
        if (!typeName(out, diags)) { return false; }
        if (isPunct("[")) { return vectorTypeRefused(diags); }
        if (tok().kind != Tok::IDENT) {
            diags.error(ErrorCode::E_PARSE, "expected a name after the type", at());
            return false;
        }
        name = tok().text;
        eat();
        return true;
    }

    /** Vector types (`uint64[4]`) and the `%v` vector variables are an
     *  implementation extension (parsers/cryptolineParser.mly: vectyp,
     *  VEC_ID) that the manual's grammar does not define; the scalar core
     *  refuses them by name rather than silently reading the element type. */
    bool vectorTypeRefused(Uir::Diagnostics& diags) {
        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "vector types (`uint64[4]`) and vector variables (`%v`) are an "
                    "implementation extension outside the manual's scalar grammar; "
                    "their elementwise lifting is not implemented", at());
        return false;
    }

    bool typeName(VarType& out, Uir::Diagnostics& diags) {
        if (tok().kind != Tok::IDENT) {
            diags.error(ErrorCode::E_PARSE, "expected a type", at());
            return false;
        }
        const std::string t = tok().text;
        std::string digits;
        if (t.compare(0, 4, "uint") == 0)      { out.is_signed = false; digits = t.substr(4); }
        else if (t.compare(0, 4, "sint") == 0) { out.is_signed = true;  digits = t.substr(4); }
        // The official lexer spells the signed types `sintN` or `intN`
        // (parsers/cryptolineLexer.mll: `("sint"|"int") (number+)`).
        else if (t.compare(0, 3, "int") == 0)  { out.is_signed = true;  digits = t.substr(3); }
        else if (t == "bit") { out.is_signed = false; digits = "1"; }
        else {
            // `a@sint32` is CryptoLine's ANNOTATED form -- the variable first,
            // its type after an `@` -- and this subset reads only `sint32 a`.
            // Left to the generic message the diagnostic blamed the variable
            // ("'a' is not a supported type"), which is true of `a` and sends
            // the reader looking for a typo in a file whose type is spelled
            // correctly one token later. Nine of the seventeen upstream files
            // stop here, and `cast b64@sint64 b` puts the same form on
            // instructions rather than only on parameters.
            if (peekIsAt()) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "'" + t + "@...' is the annotated form of a typed name, "
                            "which this subset does not read; it accepts the type "
                            "first, as in 'uint64 " + t + "'",
                            at());
                return false;
            }
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'" + t + "' is not a supported type; expected uintN, sintN, "
                            "intN or bit",
                        at());
            return false;
        }
        unsigned long long w = 0;
        const char* first = digits.data();
        const char* last = first + digits.size();
        if (digits.empty() || std::from_chars(first, last, w).ptr != last || w == 0
            || w > 4096) {
            diags.error(ErrorCode::E_PARSE, "'" + t + "' has no usable width", at());
            return false;
        }
        out.width = static_cast<unsigned>(w);
        eat();
        return true;
    }

    /** A type after `@`. Historical inputs also write `@64` for `@uint64`. */
    bool typeAnnotation(VarType& out, Uir::Diagnostics& diags) {
        if (tok().kind == Tok::IDENT) { return typeName(out, diags); }
        if (tok().kind != Tok::NUM
            || tok().text.find_first_not_of("0123456789") != std::string::npos) {
            diags.error(ErrorCode::E_PARSE,
                        "expected uintN, sintN, bit, or a width after '@'", at());
            return false;
        }
        unsigned long long width = 0;
        const char* first = tok().text.data();
        const char* last = first + tok().text.size();
        const auto parsed = std::from_chars(first, last, width);
        if (parsed.ec != std::errc() || parsed.ptr != last || width == 0 || width > 4096) {
            diags.error(ErrorCode::E_PARSE,
                        "'@" + tok().text + "' has no usable bit width", at());
            return false;
        }
        out = VarType{static_cast<unsigned>(width), false};
        eat();
        return true;
    }

    // ---- the procedure ---------------------------------------------------

    /** The program: a sequence of semicolon-separated statements -- procedure
     *  declarations, and named-constant declarations which stay refused by
     *  name (doc/cryptoline.pdf: stmt ::= proc | const id = const). Every
     *  procedure is registered in file order -- its body validated in a
     *  scratch scope, its pre/postconditions recorded over the formals --
     *  and then the ENTRY (main, or the only procedure) is translated for
     *  real. A call or inline names an EARLIER procedure: the reference
     *  parser resolves callees against the declarations parsed so far
     *  (parsers/common.ml: parse_call_at looks up ctx.cfuns). */
    bool program(Uir::Diagnostics& diags) {
        for (;;) {
            while (isPunct(";")) { eat(); }
            if (tok().kind == Tok::END) { break; }
            if (isIdent("const")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "named integer constants (`const id = ...`, read back as "
                            "'$id') are a statement form outside the procedure core "
                            "and are not implemented", at());
                return false;
            }
            if (!isIdent("proc")) {
                diags.error(ErrorCode::E_PARSE,
                            "expected a procedure declaration, got '" + tok().text + "'",
                            at());
                return false;
            }
            if (!procDecl(diags)) { return false; }
        }
        if (procs_.empty()) {
            diags.error(ErrorCode::E_PARSE, "a CryptoLine file starts with 'proc'", at());
            return false;
        }
        // The entry point of a program is the main procedure
        // (doc/cryptoline.pdf). A single-procedure file verifies that
        // procedure, whatever its name.
        const ProcDecl* entry = &procs_.begin()->second;
        if (procs_.size() != 1) {
            auto m = procs_.find("main");
            if (m == procs_.end()) {
                diags.error(ErrorCode::E_PARSE,
                            "the program has no 'main' procedure; the entry point of a "
                            "multi-procedure program is main", at());
                return false;
            }
            entry = &m->second;
        }
        // A callable procedure's postcondition may reference only its formal
        // parameters (parsers/common.ml: parse_proc) -- the entry procedure's
        // ranges over the whole program state.
        for (const auto& [pname, decl] : procs_) {
            if (&decl != entry && !decl.post_nonformals.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "variable '" + *decl.post_nonformals.begin()
                                + "' is not a formal parameter of procedure '" + pname
                                + "'; variables in postconditions for procedures other "
                                  "than the entry point must be formal input or output "
                                  "variables",
                            at());
                return false;
            }
        }
        return translateEntry(*entry, diags);
    }

    bool procDecl(Uir::Diagnostics& diags) {
        const std::size_t ordinal = procs_order_.size();
        eat();  // proc
        if (tok().kind != Tok::IDENT) {
            diags.error(ErrorCode::E_PARSE, "the procedure has no name", at());
            return false;
        }
        const std::string name = tok().text;
        const Uir::SourceLoc loc = at();
        eat();
        if (procs_.count(name) != 0) {
            diags.error(ErrorCode::E_PARSE,
                        "the procedure '" + name + "' is redefined", loc);
            return false;
        }
        if (!expect("(", diags)) { return false; }
        // The formal parameters may be separated by a semicolon into inout
        // and out variables (doc/cryptoline.pdf: formals ::= tvar* [; tvar*]).
        ProcDecl decl;
        decl.name = name;
        decl.ordinal = ordinal;
        std::vector<std::pair<std::string, VarType>>* formal_list = &decl.ins;
        while (!isPunct(")")) {
            if (isPunct(";")) {
                if (formal_list != &decl.ins) {
                    diags.error(ErrorCode::E_PARSE,
                                "the formal parameter list has at most one ';'", at());
                    return false;
                }
                eat();
                formal_list = &decl.outs;
                continue;
            }
            if (isPunct("%")) { return vectorTypeRefused(diags); }
            std::string pname;
            VarType ty;
            if (!typedName(pname, ty, diags)) { return false; }
            formal_list->push_back({pname, ty});
            if (isPunct(",")) { eat(); continue; }
            if (isPunct(";")) { continue; }
            break;
        }
        if (!expect(")", diags)) { return false; }
        if (!expect("=", diags)) { return false; }
        {
            std::unordered_set<std::string> seen;
            for (const auto& [fname, fty] : decl.ins) {
                if (!seen.insert(fname).second) {
                    diags.error(ErrorCode::E_PARSE,
                                "duplicate formal parameter '" + fname + "'", loc);
                    return false;
                }
            }
            for (const auto& [fname, fty] : decl.outs) {
                if (!seen.insert(fname).second) {
                    diags.error(ErrorCode::E_PARSE,
                                "duplicate formal parameter '" + fname + "'", loc);
                    return false;
                }
            }
        }

        // Register in a scratch scope: the body is validated and its assigned
        // variables recorded, but its constraints and declarations belong to
        // the callers (inline) or to the contract (call), never to this
        // translation directly.
        ScopeState saved = saveScope();
        const std::size_t previous_ordinal = current_ordinal_;
        current_ordinal_ = ordinal;
        bool ok = registerBody(decl, diags);
        current_ordinal_ = previous_ordinal;
        restoreScope(std::move(saved));
        if (!ok) { return false; }
        procs_order_.push_back(name);
        procs_.emplace(name, std::move(decl));
        return true;
    }

    bool registerBody(ProcDecl& decl, Uir::Diagnostics& diags) {
        // The input formals are defined; the outputs are NOT -- an output
        // variable cannot be read before it is initialized
        // (doc/cryptoline.pdf).
        for (const auto& [pname, ty] : decl.ins) { define(pname, ty); }
        decl.pre_begin = pos_;
        // The precondition accesses only the input variables.
        if (!conditionParts(true, false, decl.pre, diags)) { return false; }
        decl.body_begin = pos_;
        record_assigned_ = true;
        while (tok().kind != Tok::END && !isPunct("{")) {
            if (!instruction(diags)) { return false; }
        }
        record_assigned_ = false;
        decl.body_end = pos_;
        if (tok().kind == Tok::END) {
            diags.error(ErrorCode::E_PARSE, "the procedure has no postcondition", at());
            return false;
        }
        decl.assigned = assigned_in_body_;
        for (const auto& [pname, ty] : decl.ins) {
            if (decl.assigned.count(pname) != 0) { decl.assigned_inputs.insert(pname); }
        }
        // The postcondition may mention the outputs; an output the body never
        // wrote gets a free final version (its value is unconstrained).
        for (const auto& [pname, ty] : decl.outs) {
            if (version_.find(pname) == version_.end()) { define(pname, ty); }
        }
        if (!conditionParts(true, true, decl.post, diags)) { return false; }
        // Record every SSA version of each formal, for call substitution.
        for (const auto& [pname, ty] : decl.ins) { recordVersions(decl, pname); }
        for (const auto& [pname, ty] : decl.outs) { recordVersions(decl, pname); }
        // The postcondition of a CALLABLE procedure may reference only its
        // formal parameters (parsers/common.ml: parse_proc). The entry
        // procedure's postcondition ranges over the whole program state, so
        // the violation is recorded and program() reports it only for
        // non-entry procedures.
        std::unordered_set<std::string> post_idents;
        for (const PredClause& p : decl.post) { collectIdents(p.expr, post_idents); }
        std::unordered_set<std::string> formal_ssa;
        for (const auto& [base, versions] : decl.formal_versions) {
            formal_ssa.insert(versions.begin(), versions.end());
        }
        for (const std::string& ident : post_idents) {
            if (formal_ssa.count(ident) == 0) { decl.post_nonformals.insert(ident); }
            // The formal input assigned in the body cannot appear in the
            // postcondition (parsers/common.ml: check_updated_formal_inputs
            // is checked at the call; the set membership is recorded here).
            for (const auto& [base, versions] : decl.formal_versions) {
                if (std::find(versions.begin(), versions.end(), ident)
                    != versions.end()) {
                    decl.post_formals.insert(base);
                }
            }
        }
        return true;
    }

    void recordVersions(ProcDecl& decl, const std::string& base) {
        auto it = counter_.find(base);
        if (it == counter_.end() || it->second == 0) { return; }
        std::vector<std::string> versions;
        for (unsigned k = 1; k <= it->second; ++k) {
            versions.push_back(k == 1 ? base : base + "!" + std::to_string(k));
        }
        decl.formal_versions[base] = std::move(versions);
    }

    /** The entry procedure is translated for real: its formals are the
     *  program's inputs, its precondition is ASSUMED, and its postcondition
     *  is the OBLIGATION, negated -- the emitted script is a refutation, so
     *  UNSAT means the procedure is correct. Same inversion as TPTP's
     *  conjecture, arrived at from the other direction. */
    bool translateEntry(const ProcDecl& decl, Uir::Diagnostics& diags) {
        current_ordinal_ = decl.ordinal;
        for (const auto& [pname, ty] : decl.ins) { define(pname, ty); }
        for (const auto& [pname, ty] : decl.outs) { define(pname, ty); }
        pos_ = decl.pre_begin;
        if (!condition(Role::PRECONDITION, false, diags)) { return false; }
        while (tok().kind != Tok::END && !isPunct("{")) {
            if (!instruction(diags)) { return false; }
        }
        return condition(Role::OBLIGATION, true, diags);
    }

    void applyCondition(const std::vector<PredClause>& parts, Role role,
                        const Uir::SourceLoc& loc, Uir::Diagnostics& diags) {
        for (const PredClause& p : parts) {
            auto& prefix = p.algebraic ? prefix_e_ : prefix_r_;
            if (role == Role::PRECONDITION) {
                // A hypothesis the proof may use, and the fact the
                // `precondition` hint selects.
                prefix.push_back(p.expr);
                (p.algebraic ? pre_e_ : pre_r_).push_back(p.expr);
                continue;
            }
            if (role == Role::ASSUME) {
                // A hypothesis the proof may use. Its prove-with hints are
                // inert: a hypothesis is never proved.
                prefix.push_back(p.expr);
                (p.algebraic ? assumes_e_ : assumes_r_).push_back(p.expr);
                continue;
            }
            // An obligation at this prefix. It is not assumed afterwards, and
            // a later `assume` must not suppress a counterexample already
            // found. A literal-true half can never fail and adds no branch.
            if (p.expr->kind == H::ExprKind::LIT_BOOL && p.expr->bool_value) {
                continue;
            }
            if (!validateHints(p.hints, p.algebraic, diags, loc)) { continue; }
            addObligation(p.expr, p.algebraic, p.hints, loc);
        }
    }

    bool validateHints(const ProveWith& hints, bool algebraic,
                       Uir::Diagnostics& diags, const Uir::SourceLoc& loc) const {
        const std::size_t available = (algebraic ? cuts_e_ : cuts_r_).size();
        for (const unsigned i : hints.cuts) {
            if (i >= available) {
                diags.error(ErrorCode::E_PARSE,
                            "prove with [ cuts [ " + std::to_string(i)
                                + " ] ] but only " + std::to_string(available)
                                + (algebraic ? " algebraic" : " range")
                                + (available == 1 ? " cut precedes" : " cuts precede")
                                + " this predicate; ecut and rcut are numbered "
                                  "separately from 0",
                            loc);
                return false;
            }
        }
        return true;
    }

    /** The cut semantics (ast/cryptoline.ml: cut_espec/cut_rspec over
     *  evisit_with_pwss/rvisit_with_pwss): each cut predicate is verified as
     *  an obligation of the CURRENT fragment, and then the side "starts
     *  afresh with the predicate assumed" -- the conjunction of the cut's
     *  predicates becomes the next fragment's ONLY precondition on this side;
     *  the earlier instructions and assumes are not carried. The conjunction
     *  is also recorded so later `cuts [i]` / `all cuts` hints can select it. */
    bool applyCut(const std::vector<PredClause>& preds, bool algebraic,
                  Uir::Diagnostics& diags, const Uir::SourceLoc& loc) {
        if (preds.empty()) { return true; }
        H::ExprPtr conjunction;
        for (const PredClause& p : preds) {
            const bool trivial = p.expr->kind == H::ExprKind::LIT_BOOL
                                 && p.expr->bool_value;
            if (!trivial) {
                if (!validateHints(p.hints, algebraic, diags, loc)) { return false; }
                addObligation(p.expr, algebraic, p.hints, loc);
            }
            conjunction = conjunction ? H::mkOp(H::Op::AND, {conjunction, p.expr}, loc)
                                      : p.expr;
        }
        (algebraic ? cuts_e_ : cuts_r_).push_back(conjunction);
        (algebraic ? prefix_e_ : prefix_r_) = {conjunction};
        return true;
    }

    /** `prove with [ ... ]` on a predicate clause. The fact-selecting hints
     *  (precondition, cuts [i, ...], all cuts/assumes/ghosts) are recorded on
     *  the clause; the solver-selection hints carry no denotation and are
     *  skipped in the operational layer. */
    bool proveWith(ProveWith& out, bool allow_hints, Uir::Diagnostics& diags) {
        if (!isIdent("prove")) { return true; }
        const Uir::SourceLoc loc = at();
        eat();
        if (!isIdent("with")) {
            diags.error(ErrorCode::E_PARSE, "expected 'with' after 'prove'", at());
            return false;
        }
        eat();
        if (!allow_hints) {
            diags.error(ErrorCode::E_PARSE,
                        "'prove with' belongs to a predicate clause (assert, cut, "
                        "postcondition); the precondition is a plain predicate", loc);
            return false;
        }
        if (!expect("[", diags)) { return false; }
        while (!isPunct("]")) {
            if (tok().kind != Tok::IDENT) {
                diags.error(ErrorCode::E_PARSE,
                            "expected a prove-with hint, got '" + tok().text + "'", at());
                return false;
            }
            const std::string hint = tok().text;
            if (hint == "precondition") {
                out.precondition = true;
                eat();
            } else if (hint == "cuts") {
                eat();
                if (!expect("[", diags)) { return false; }
                while (!isPunct("]")) {
                    if (tok().kind != Tok::NUM
                        || tok().text.find_first_not_of("0123456789")
                               != std::string::npos) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a cuts selector needs decimal cut indices", at());
                        return false;
                    }
                    unsigned long long idx = 0;
                    const char* first = tok().text.data();
                    std::from_chars(first, first + tok().text.size(), idx);
                    eat();
                    out.cuts.push_back(static_cast<unsigned>(idx));
                    if (isPunct(",")) { eat(); continue; }
                    break;
                }
                if (!expect("]", diags)) { return false; }
            } else if (hint == "all") {
                eat();
                if (isIdent("cuts"))        { out.all_cuts = true; }
                else if (isIdent("assumes")) { out.all_assumes = true; }
                else if (isIdent("ghosts"))  { out.all_ghosts = true; }
                else {
                    diags.error(ErrorCode::E_PARSE,
                                "expected 'cuts', 'assumes' or 'ghosts' after 'all'",
                                at());
                    return false;
                }
                eat();
            } else {
                // Solver-selection hints (algebra/range/qfbv solver, variable
                // and monomial orders, algebra args, eqfirst) select HOW the
                // reference tool discharges the predicate, not WHAT it means:
                // skip to the next top-level ',' or ']'. Note: solver string
                // arguments are not lexed, so a comma inside one would
                // mislead this skip.
                unsigned depth = 0;
                for (;;) {
                    if (tok().kind == Tok::END) {
                        diags.error(ErrorCode::E_PARSE,
                                    "unterminated 'prove with' list", loc);
                        return false;
                    }
                    if (isPunct("[")) { ++depth; eat(); continue; }
                    if (isPunct("]")) {
                        if (depth == 0) { break; }
                        --depth; eat(); continue;
                    }
                    if (isPunct(",") && depth == 0) { break; }
                    eat();
                }
            }
            if (isPunct(",")) { eat(); continue; }
            break;
        }
        if (!expect("]", diags)) { return false; }
        return true;
    }

    /** One side of a condition: a comma-separated list of predicates, each
     *  with optional prove-with hints (parsers: ebexp_prove_with_list /
     *  rbexp_prove_with_list). */
    bool conditionSide(bool algebraic, bool allow_hints,
                       std::vector<PredClause>& out, Uir::Diagnostics& diags) {
        for (;;) {
            PredClause clause;
            clause.algebraic = algebraic;
            clause.expr = conditionHalf(diags, algebraic, &clause.algebraic);
            if (!clause.expr) { return false; }
            if (!proveWith(clause.hints, allow_hints, diags)) { return false; }
            out.push_back(std::move(clause));
            if (isPunct(",")) { eat(); continue; }
            break;
        }
        return true;
    }

    /** `{ side && side }` (the specification form, braced) or `side && side`
     *  (the instruction form, bare). */
    bool conditionParts(bool braced, bool allow_hints,
                        std::vector<PredClause>& out, Uir::Diagnostics& diags) {
        if (!braced) {
            if (!conditionSide(true, allow_hints, out, diags)) { return false; }
            if (!expect("&&", diags)) { return false; }
            return conditionSide(false, allow_hints, out, diags);
        }
        if (!expect("{", diags)) { return false; }
        std::size_t half_index = 0;
        for (;;) {
            if (isPunct("}")) { break; }
            if (!conditionSide(half_index == 0, allow_hints, out, diags)) {
                return false;
            }
            ++half_index;
            if (isPunct("&&")) { eat(); continue; }
            break;
        }
        return expect("}", diags);
    }

    /** `{ eqn ... && rng ... }`. In the PRECONDITION and ASSUME roles the
     *  halves extend the path on their own side; in the OBLIGATION role each
     *  half's failure becomes a separate prefix branch.
     *
     *  **assume versus assert is the whole of the fourth obligation.** A
     *  precondition asserted as an obligation makes the query ask whether the
     *  caller's hypothesis is provable, which it is not and was never meant to
     *  be; a postcondition assumed rather than negated makes the verification
     *  vacuous -- every procedure "passes". */
    bool condition(Role role, bool allow_hints, Uir::Diagnostics& diags) {
        const Uir::SourceLoc loc = at();
        std::vector<PredClause> parts;
        if (!conditionParts(true, allow_hints, parts, diags)) { return false; }
        applyCondition(parts, role, loc, diags);
        return !diags.hasErrors();
    }

    /** Instruction predicates omit the procedure specification's braces:
     *  `assert <algebraic> && <range> [prove with ...];`. The two halves use
     *  different interpretations even when their surface equality is the same. */
    bool instructionCondition(Role role, Uir::Diagnostics& diags) {
        const Uir::SourceLoc loc = at();
        std::vector<PredClause> parts;
        if (!conditionParts(isPunct("{"), true, parts, diags)) { return false; }
        applyCondition(parts, role, loc, diags);
        return !diags.hasErrors();
    }

    /** `eqn <int expr>` or `rng <bv expr>`, a bare `true`, or a predicate
     *  under the connectives. The two halves have different connective sets:
     *  the range half is a Boolean combination (ast/cryptoline.mli: Rneg,
     *  Rand, Ror -- negation, conjunction, disjunction) while the algebraic
     *  half is conjunction-only (ebexp has no Rneg/Ror counterpart). */
    H::ExprPtr conditionHalf(Uir::Diagnostics& diags,
                             std::optional<bool> default_algebraic = std::nullopt,
                             bool* side = nullptr) {
        if (isIdent("true"))  { eat(); return H::mkBool(true, at()); }
        if (isIdent("false")) { eat(); return H::mkBool(false, at()); }
        bool algebraic = default_algebraic.value_or(false);
        if (isIdent("eqn"))      { algebraic = true;  eat(); }
        else if (isIdent("rng")) { algebraic = false; eat(); }
        if (side != nullptr) { *side = algebraic; }
        rng_width_ = algebraic ? 0 : halfWidth();
        return predOr(algebraic, diags);
    }

    /** `p \/ q` -- range-predicate disjunction (parsers: LOROP infix). */
    H::ExprPtr predOr(bool algebraic, Uir::Diagnostics& diags) {
        H::ExprPtr lhs = predAnd(algebraic, diags);
        while (lhs && isPunct("\\/")) {
            const Uir::SourceLoc loc = at();
            if (algebraic) {
                diags.error(ErrorCode::E_TYPE,
                            "disjunction is a range-predicate form; the algebraic half "
                            "of a condition is conjunction-only", loc);
                return nullptr;
            }
            eat();
            H::ExprPtr rhs = predAnd(algebraic, diags);
            if (!rhs) { return nullptr; }
            lhs = H::mkOp(H::Op::OR, {lhs, rhs}, loc);
        }
        return lhs;
    }

    /** `p /\ q` -- infix predicate conjunction (parsers: LANDOP infix). */
    H::ExprPtr predAnd(bool algebraic, Uir::Diagnostics& diags) {
        H::ExprPtr lhs = predUnary(algebraic, diags);
        while (lhs && isPunct("/\\")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr rhs = predUnary(algebraic, diags);
            if (!rhs) { return nullptr; }
            lhs = H::mkOp(H::Op::AND, {lhs, rhs}, loc);
        }
        return lhs;
    }

    /** `~ p` / `neg p` -- range-predicate negation (ast/cryptoline.mli: Rneg).
     *  The predicate form applies only to a predicate PRIMARY (`true`,
     *  `false`, a parenthesized predicate, another negation); `~x = y` with a
     *  variable x is the two's-complement EXPRESSION negation inside a
     *  comparison (Rnegb), read by the expression parser. */
    H::ExprPtr predUnary(bool algebraic, Uir::Diagnostics& diags) {
        if (isPunct("~") || isIdent("neg")) {
            const Tok& next = pos_ + 1 < toks_.size() ? toks_[pos_ + 1] : toks_.back();
            const bool predicate_operand =
                (next.kind == Tok::IDENT
                 && (next.text == "true" || next.text == "false"
                     || next.text == "neg"))
                || (next.kind == Tok::PUNCT && next.text == "~")
                || (next.kind == Tok::PUNCT && next.text == "("
                    && parenStartsPredicateAt(pos_ + 1));
            if (predicate_operand) {
                const Uir::SourceLoc loc = at();
                if (algebraic) {
                    diags.error(ErrorCode::E_TYPE,
                                "negation is a range-predicate form; the algebraic half "
                                "of a condition is conjunction-only", loc);
                    return nullptr;
                }
                eat();
                H::ExprPtr inner = predUnary(algebraic, diags);
                return inner ? H::mkOp(H::Op::NOT, {inner}, loc) : nullptr;
            }
        }
        return predAtom(algebraic, diags);
    }

    H::ExprPtr predAtom(bool algebraic, Uir::Diagnostics& diags) {
        if (parenStartsPredicate()) {
            eat();
            H::ExprPtr nested = conditionHalf(diags, algebraic);
            return nested && expect(")", diags) ? nested : nullptr;
        }
        // `and [ p1, p2, ... ]` -- CryptoLine's conjunction over a LIST of
        // predicates, which is how a postcondition states several facts at
        // once. Left unhandled, `and` was read as an operand and reported as
        // "'and' is used before it is defined": a name the LANGUAGE provides,
        // blamed on the model for not declaring it. Alongside the list form
        // there are the binary prefix connectives `and p q` / `or p q` and the
        // disjunction list `or [ ... ]` (parsers: AND/OR both binary and
        // list). A connective is only a connective where a predicate is
        // expected AND the next token can start one (`[`, `(`, `true`,
        // `false`, `~`, `neg`); `and x y` at this position is the bit-wise
        // EXPRESSION operator and falls through to the relation parser.
        if (isIdent("and") || isIdent("or") || isPunct("/\\") || isPunct("\\/")) {
            const bool disjunction = isIdent("or") || isPunct("\\/");
            const Uir::SourceLoc loc = at();
            const Tok& next = pos_ + 1 < toks_.size() ? toks_[pos_ + 1] : toks_.back();
            const bool connective =
                next.kind == Tok::PUNCT
                    ? (next.text == "[" || next.text == "(" || next.text == "~")
                    : next.kind == Tok::IDENT
                          && (next.text == "true" || next.text == "false"
                              || next.text == "neg");
            if (!connective) { return relation(algebraic, diags); }
            if (disjunction && algebraic) {
                diags.error(ErrorCode::E_TYPE,
                            "disjunction is a range-predicate form; the algebraic half "
                            "of a condition is conjunction-only", loc);
                return nullptr;
            }
            eat();
            std::vector<H::ExprPtr> parts;
            if (isPunct("[")) {
                eat();
                while (!isPunct("]")) {
                    H::ExprPtr one = conditionHalf(diags, algebraic);
                    if (!one) { return nullptr; }
                    parts.push_back(one);
                    if (isPunct(",")) { eat(); continue; }
                    break;
                }
                if (!expect("]", diags)) { return nullptr; }
            } else {
                H::ExprPtr first = predUnary(algebraic, diags);
                if (!first) { return nullptr; }
                H::ExprPtr second = predUnary(algebraic, diags);
                if (!second) { return nullptr; }
                parts.push_back(first);
                parts.push_back(second);
            }
            // An empty list is the connective's unit. `and []` appears in the
            // corpus, where a half has nothing to say.
            if (parts.empty()) { return H::mkBool(!disjunction, loc); }
            if (parts.size() == 1) { return parts[0]; }
            return H::mkOp(disjunction ? H::Op::OR : H::Op::AND, parts, loc);
        }
        if (isIdent("true"))  { eat(); return H::mkBool(true, at()); }
        if (isIdent("false")) { eat(); return H::mkBool(false, at()); }
        if (isIdent("eq")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr lhs = algebraic ? sum(true, diags) : rangeExpr(diags);
            H::ExprPtr rhs = algebraic ? sum(true, diags) : rangeExpr(diags);
            return lhs && rhs ? H::mkOp(H::Op::EQ, {lhs, rhs}, loc) : nullptr;
        }
        if (isIdent("eqmod") && algebraic) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr lhs = sum(true, diags);
            H::ExprPtr rhs = sum(true, diags);
            std::vector<H::ExprPtr> moduli;
            if (isPunct("[")) {
                // `eqmod e1 e2 [m1, ..., mn]` -- equality modulo a LIST of
                // moduli (ast/cryptoline.mli: Eeqmod of eexp * eexp *
                // eexp list).
                eat();
                while (!isPunct("]")) {
                    H::ExprPtr m = sum(true, diags);
                    if (!m) { return nullptr; }
                    moduli.push_back(m);
                    if (isPunct(",")) { eat(); continue; }
                    break;
                }
                if (!expect("]", diags)) { return nullptr; }
                if (moduli.empty()) {
                    diags.error(ErrorCode::E_PARSE,
                                "eqmod needs at least one modulus", loc);
                    return nullptr;
                }
            } else {
                H::ExprPtr m = sum(true, diags);
                if (!m) { return nullptr; }
                moduli.push_back(m);
            }
            if (!lhs || !rhs) { return nullptr; }
            return modularEquality(lhs, rhs, moduli, loc);
        }
        // In a range predicate `eqmod` is the unsigned modular equality
        // (parsers/cryptolineParser.mly: EQMOD rexp rexp rexp -> equmod).
        if (isIdent("equmod") || isIdent("eqsmod") || isIdent("eqsrem")
            || (isIdent("eqmod") && !algebraic)) {
            if (algebraic) {
                diags.error(ErrorCode::E_TYPE,
                            "range modular equality cannot appear in the algebraic half",
                            at());
                return nullptr;
            }
            const std::string op = tok().text;
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr lhs = rangeExpr(diags);
            H::ExprPtr rhs = rangeExpr(diags);
            H::ExprPtr modulus = rangeExpr(diags);
            if (!lhs || !rhs || !modulus) { return nullptr; }
            return rangeModularEquality(op == "eqsrem" ? "srem"
                                        : op == "eqsmod" ? "smod" : "umod",
                                        lhs, rhs, modulus, loc, diags);
        }
        // The prefix comparisons `ult e1 e2`, ..., `sge e1 e2`
        // (parsers: cmpop_prefix), the range half only.
        if (!algebraic) {
            static const std::unordered_map<std::string, H::Op> kCmp = {
                {"ult", H::Op::BV_ULT}, {"ule", H::Op::BV_ULE},
                {"ugt", H::Op::BV_UGT}, {"uge", H::Op::BV_UGE},
                {"slt", H::Op::BV_SLT}, {"sle", H::Op::BV_SLE},
                {"sgt", H::Op::BV_SGT}, {"sge", H::Op::BV_SGE},
            };
            const auto it = kCmp.find(tok().text);
            if (tok().kind == Tok::IDENT && it != kCmp.end()) {
                const Uir::SourceLoc loc = at();
                eat();
                H::ExprPtr lhs = rangeExpr(diags);
                H::ExprPtr rhs = rangeExpr(diags);
                return lhs && rhs ? H::mkOp(it->second, {lhs, rhs}, loc) : nullptr;
            }
        }
        return relation(algebraic, diags);
    }

    /** Algebraic `e1 = e2 (mod m1, ...)`: ideal membership over Z, encoded as
     *  one existential multiplier per modulus -- e1-e2 = sum_i k_i*m_i. */
    H::ExprPtr modularEquality(const H::ExprPtr& lhs, const H::ExprPtr& rhs,
                               const std::vector<H::ExprPtr>& moduli,
                               const Uir::SourceLoc& loc) {
        std::vector<H::Binder> binders;
        H::ExprPtr combination;
        for (const H::ExprPtr& modulus : moduli) {
            H::Binder k;
            k.name = "eqmod!" + std::to_string(eqmod_binder_++);
            k.sort = H::Sort::integer();
            const H::ExprPtr term =
                H::mkOp(H::Op::MUL, {H::mkBoundVar(k.name, k.sort, loc), modulus}, loc);
            combination = combination ? H::mkOp(H::Op::ADD, {combination, term}, loc)
                                      : term;
            binders.push_back(k);
        }
        const H::ExprPtr equation = H::mkOp(
            H::Op::EQ, {H::mkOp(H::Op::SUB, {lhs, rhs}, loc), combination}, loc);
        return H::mkExists(binders, equation, loc);
    }

    /** Range modular equality. Official CryptoLine semantics
     *  (ast/cryptoline.ml): perform the subtraction and modulus in w+1 bits.
     *  `umod` zero-extends its operands; the signed forms sign-extend them.
     *  This extra bit is essential because the mathematical difference need
     *  not fit in w. `srem` is deliberately remainder rather than modulo. */
    H::ExprPtr rangeModularEquality(const std::string& kind, const H::ExprPtr& lhs,
                                    const H::ExprPtr& rhs, const H::ExprPtr& modulus,
                                    const Uir::SourceLoc& loc,
                                    Uir::Diagnostics& diags) {
        if (lhs->sort.kind != H::SortKind::BITVEC
            || rhs->sort.kind != H::SortKind::BITVEC
            || modulus->sort.kind != H::SortKind::BITVEC
            || rhs->sort.width != lhs->sort.width
            || modulus->sort.width != lhs->sort.width) {
            diags.error(ErrorCode::E_TYPE,
                        "range modular equality operands must have one bit-vector "
                        "width", loc);
            return nullptr;
        }
        const H::Op extend =
            kind == "umod" ? H::Op::BV_ZERO_EXTEND : H::Op::BV_SIGN_EXTEND;
        const H::ExprPtr difference = H::mkOp(
            H::Op::BV_SUB,
            {H::mkBvExtend(extend, lhs, 1, loc),
             H::mkBvExtend(extend, rhs, 1, loc)}, loc);
        const H::ExprPtr divisor = H::mkBvExtend(extend, modulus, 1, loc);
        const H::ExprPtr remainder = H::mkOp(
            kind == "srem" ? H::Op::BV_SREM : H::Op::BV_SMOD,
            {difference, divisor}, loc);
        return H::mkOp(H::Op::EQ,
                       {remainder, bvZero(lhs->sort.width + 1, loc)}, loc);
    }

    H::ExprPtr relation(bool algebraic, Uir::Diagnostics& diags) {
        H::ExprPtr l = algebraic ? sum(true, diags) : rangeExpr(diags);
        if (!l) { return nullptr; }
        const Uir::SourceLoc loc = at();
        struct { const char* text; H::Op signed_op; H::Op unsigned_op; } kOps[] = {
            {"=",  H::Op::EQ, H::Op::EQ},
            {"<=u", H::Op::LE, H::Op::BV_ULE},
            {">=u", H::Op::GE, H::Op::BV_UGE},
            {"<u",  H::Op::LT, H::Op::BV_ULT},
            {">u",  H::Op::GT, H::Op::BV_UGT},
            {"<=s", H::Op::LE, H::Op::BV_SLE},
            {">=s", H::Op::GE, H::Op::BV_SGE},
            {"<s",  H::Op::LT, H::Op::BV_SLT},
            {">s",  H::Op::GT, H::Op::BV_SGT},
            {"<=", H::Op::LE, H::Op::BV_ULE},
            {">=", H::Op::GE, H::Op::BV_UGE},
            {"<",  H::Op::LT, H::Op::BV_ULT},
            {">",  H::Op::GT, H::Op::BV_UGT},
        };
        for (const auto& o : kOps) {
            if (!isPunct(o.text)) { continue; }
            eat();
            H::ExprPtr r = algebraic ? sum(true, diags) : rangeExpr(diags);
            if (!r) { return nullptr; }
            // In the algebraic half both sides are Int. Range comparisons carry
            // their signedness in the operator (`<u`, `<s`, ...); the plain
            // legacy spellings are unsigned.
            H::ExprPtr compared =
                H::mkOp(algebraic ? o.signed_op : o.unsigned_op, {l, r}, loc);
            if (std::string(o.text) != "=") { return compared; }
            // An equality may carry a modulus suffix: `e1 = e2 (mod m)` or
            // `(mod [m1, ...])` in the algebraic half (parsers: eq_suffix),
            // `e1 = e2 (umod m)` / `(smod m)` / `(srem m)` -- and plain
            // `(mod m)`, which is the unsigned form -- in the range half
            // (parsers: req_suffix).
            if (!isPunct("(")) { return compared; }
            const bool mod_keyword = pos_ + 1 < toks_.size()
                                     && toks_[pos_ + 1].kind == Tok::IDENT
                                     && toks_[pos_ + 1].text == "mod";
            const std::string kind =
                pos_ + 1 < toks_.size() && toks_[pos_ + 1].kind == Tok::IDENT
                    ? toks_[pos_ + 1].text
                    : std::string();
            const bool range_kind =
                kind == "umod" || kind == "smod" || kind == "srem";
            if (algebraic && !mod_keyword) { return compared; }
            if (!algebraic && !range_kind && !mod_keyword) { return compared; }
            eat();  // '('
            eat();  // mod / umod / smod / srem
            if (algebraic) {
                std::vector<H::ExprPtr> moduli;
                if (isPunct("[")) {
                    eat();
                    while (!isPunct("]")) {
                        H::ExprPtr m = sum(true, diags);
                        if (!m) { return nullptr; }
                        moduli.push_back(m);
                        if (isPunct(",")) { eat(); continue; }
                        break;
                    }
                    if (!expect("]", diags)) { return nullptr; }
                    if (moduli.empty()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a mod suffix needs at least one modulus", loc);
                        return nullptr;
                    }
                } else {
                    H::ExprPtr m = sum(true, diags);
                    if (!m) { return nullptr; }
                    moduli.push_back(m);
                }
                if (!expect(")", diags)) { return nullptr; }
                return modularEquality(l, r, moduli, loc);
            }
            H::ExprPtr modulus = rangeExpr(diags);
            if (!modulus) { return nullptr; }
            if (!expect(")", diags)) { return nullptr; }
            return rangeModularEquality(range_kind ? kind : "umod", l, r, modulus, loc,
                                        diags);
        }
        diags.error(ErrorCode::E_PARSE,
                    "expected a relational operator in the condition, got '" + tok().text
                        + "'", loc);
        return nullptr;
    }

    H::ExprPtr rangeExpr(Uir::Diagnostics& diags) { return rangeOr(diags); }

    H::ExprPtr rangeOr(Uir::Diagnostics& diags) {
        H::ExprPtr lhs = rangeXor(diags);
        while (lhs && isPunct("|")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr rhs = rangeXor(diags);
            if (!rhs) { return nullptr; }
            lhs = H::mkOp(H::Op::BV_OR, {lhs, rhs}, loc);
        }
        return lhs;
    }

    H::ExprPtr rangeXor(Uir::Diagnostics& diags) {
        H::ExprPtr lhs = rangeAnd(diags);
        while (lhs && isPunct("^")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr rhs = rangeAnd(diags);
            if (!rhs) { return nullptr; }
            lhs = H::mkOp(H::Op::BV_XOR, {lhs, rhs}, loc);
        }
        return lhs;
    }

    H::ExprPtr rangeAnd(Uir::Diagnostics& diags) {
        H::ExprPtr lhs = rangeShift(diags);
        while (lhs && isPunct("&")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr rhs = rangeShift(diags);
            if (!rhs) { return nullptr; }
            lhs = H::mkOp(H::Op::BV_AND, {lhs, rhs}, loc);
        }
        return lhs;
    }

    H::ExprPtr rangeShift(Uir::Diagnostics& diags) {
        H::ExprPtr lhs = sum(false, diags);
        while (lhs && (isPunct("<<") || isPunct(">>") || isPunct(">>a"))) {
            const Uir::SourceLoc loc = at();
            // `>>a` is the infix arithmetic shift (parsers: SAROP).
            const H::Op op = isPunct("<<")   ? H::Op::BV_SHL
                             : isPunct(">>") ? H::Op::BV_LSHR
                                             : H::Op::BV_ASHR;
            eat();
            H::ExprPtr rhs = sum(false, diags);
            if (!rhs) { return nullptr; }
            lhs = H::mkOp(op, {lhs, rhs}, loc);
        }
        return lhs;
    }

    H::ExprPtr sum(bool algebraic, Uir::Diagnostics& diags) {
        H::ExprPtr l = product(algebraic, diags);
        if (!l) { return nullptr; }
        while (isPunct("+") || isPunct("-")) {
            const bool plus = isPunct("+");
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr r = product(algebraic, diags);
            if (!r) { return nullptr; }
            l = H::mkOp(algebraic ? (plus ? H::Op::ADD : H::Op::SUB)
                                  : (plus ? H::Op::BV_ADD : H::Op::BV_SUB),
                        {l, r}, loc);
        }
        return l;
    }

    H::ExprPtr product(bool algebraic, Uir::Diagnostics& diags) {
        H::ExprPtr l = atom(algebraic, diags);
        if (!l) { return nullptr; }
        while (isPunct("*")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr r = atom(algebraic, diags);
            if (!r) { return nullptr; }
            l = H::mkOp(algebraic ? H::Op::MUL : H::Op::BV_MUL, {l, r}, loc);
        }
        return l;
    }

    /** `e ** n` with a literal exponent n: exponentiation of an expression by
     *  a constant (parsers: eexp POWOP eexp_primary_as_const). A literal base
     *  is exponentiated exactly as decimal text inside atomPrimary; an
     *  expression base folds into a multiplication chain here. The algebraic
     *  half only -- the range-expression grammar has no exponentiation. */
    H::ExprPtr atom(bool algebraic, Uir::Diagnostics& diags) {
        H::ExprPtr e = atomPrimary(algebraic, diags);
        if (!e || !algebraic || !isPunct("**")) { return e; }
        const Uir::SourceLoc loc = at();
        eat();
        if (tok().kind != Tok::NUM
            || tok().text.find_first_not_of("0123456789") != std::string::npos) {
            diags.error(ErrorCode::E_PARSE, "'**' needs a numeric exponent", loc);
            return nullptr;
        }
        const std::string exp = tok().text;
        eat();
        unsigned long long n = 0;
        const char* first = exp.data();
        const auto parsed = std::from_chars(first, first + exp.size(), n);
        if (parsed.ec != std::errc() || parsed.ptr != first + exp.size() || n > 8192) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "exponentiation of an expression by a constant is bounded at "
                        "8192; the literal-base form is exact at any size", loc);
            return nullptr;
        }
        if (n == 0) { return H::mkInt(1, loc); }
        H::ExprPtr result = e;
        for (unsigned long long k = 1; k < n; ++k) {
            result = H::mkOp(H::Op::MUL, {result, e}, loc);
        }
        return result;
    }

    H::ExprPtr atomPrimary(bool algebraic, Uir::Diagnostics& diags) {
        if (isPunct("-")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr inner = atom(algebraic, diags);
            return inner ? H::mkOp(algebraic ? H::Op::NEG : H::Op::BV_NEG,
                                   {inner}, loc)
                         : nullptr;
        }
        if (isIdent("limbs") || isIdent("ulimbs") || isIdent("slimbs")) {
            const bool signed_top = isIdent("slimbs");
            const Uir::SourceLoc loc = at();
            eat();
            if (tok().kind != Tok::NUM
                || tok().text.find_first_not_of("0123456789") != std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "limbs needs a decimal limb width", loc);
                return nullptr;
            }
            unsigned long long limb_width = 0;
            const char* first = tok().text.data();
            const char* last = first + tok().text.size();
            const auto parsed = std::from_chars(first, last, limb_width);
            eat();
            if (parsed.ec != std::errc() || parsed.ptr != last || limb_width == 0
                || limb_width > 4096 || !expect("[", diags)) {
                if (parsed.ec == std::errc() && parsed.ptr == last
                    && (limb_width == 0 || limb_width > 4096)) {
                    diags.error(ErrorCode::E_PARSE, "limbs has an invalid width", loc);
                }
                return nullptr;
            }
            std::vector<H::ExprPtr> limbs;
            while (!isPunct("]")) {
                H::ExprPtr limb = algebraic ? sum(true, diags) : rangeExpr(diags);
                if (!limb) { return nullptr; }
                if (!algebraic && limb->sort.kind != H::SortKind::BITVEC) {
                    diags.error(ErrorCode::E_TYPE,
                                "a range limb must be a bit-vector", loc);
                    return nullptr;
                }
                limbs.push_back(limb);
                if (isPunct(",")) { eat(); continue; }
                break;
            }
            if (!expect("]", diags)) { return nullptr; }
            if (limbs.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "limbs needs at least one limb", loc);
                return nullptr;
            }
            if (algebraic) {
                // `slimbs` exists only in the range-expression grammar
                // (parsers: SLIMBS appears in rexp, not in eexp).
                if (signed_top) {
                    diags.error(ErrorCode::E_PARSE,
                                "'slimbs' is a range-expression form; the algebraic "
                                "half has limbs/ulimbs only", loc);
                    return nullptr;
                }
                H::ExprPtr result = limbs.front();
                for (std::size_t i = 1; i < limbs.size(); ++i) {
                    const std::string factor =
                        power("2", std::to_string(limb_width * i));
                    result = H::mkOp(
                        H::Op::ADD,
                        {result, H::mkOp(H::Op::MUL,
                                         {limbs[i], H::mkInt(factor, loc)}, loc)}, loc);
                }
                return result;
            }
            // Official range limbs (parsers/common.ml: parse_rexp_limbs): the
            // result width is max_i(width(e_i) + i*w), every limb is extended
            // to it -- zero extension, except that slimbs sign-extends the
            // LAST limb -- and the result is the sum e_i * 2^(i*w) computed at
            // that width. Limbs of exactly w bits make the sum a
            // concatenation; the general form admits mixed widths.
            unsigned tw = 0;
            for (std::size_t i = 0; i < limbs.size(); ++i) {
                tw = std::max(tw, limbs[i]->sort.width
                                      + static_cast<unsigned>(limb_width * i));
            }
            H::ExprPtr result;
            for (std::size_t i = 0; i < limbs.size(); ++i) {
                const unsigned w_i = limbs[i]->sort.width;
                H::ExprPtr extended = limbs[i];
                if (w_i < tw) {
                    const bool sign = signed_top && i + 1 == limbs.size();
                    extended = H::mkBvExtend(sign ? H::Op::BV_SIGN_EXTEND
                                                  : H::Op::BV_ZERO_EXTEND,
                                             limbs[i], tw - w_i, loc);
                }
                H::ExprPtr term = extended;
                if (i != 0) {
                    const std::string factor = power("2", std::to_string(limb_width * i));
                    term = H::mkOp(H::Op::BV_MUL,
                                   {extended, H::mkBitVec(binaryOf(factor, tw), tw, loc)},
                                   loc);
                }
                result = result ? H::mkOp(H::Op::BV_ADD, {result, term}, loc) : term;
            }
            return result;
        }
        if (!algebraic && (isIdent("uext") || isIdent("sext"))) {
            const bool sign = isIdent("sext");
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr value = atom(false, diags);
            if (!value || tok().kind != Tok::NUM
                || tok().text.find_first_not_of("0123456789") != std::string::npos) {
                if (value) {
                    diags.error(ErrorCode::E_PARSE,
                                "uext/sext needs a literal extension amount", loc);
                }
                return nullptr;
            }
            unsigned long long amount = 0;
            const char* first = tok().text.data();
            const char* last = first + tok().text.size();
            const auto parsed = std::from_chars(first, last, amount);
            eat();
            if (parsed.ec != std::errc() || parsed.ptr != last || amount == 0
                || amount > 4096) {
                diags.error(ErrorCode::E_PARSE,
                            "uext/sext has an invalid extension amount", loc);
                return nullptr;
            }
            return H::mkBvExtend(sign ? H::Op::BV_SIGN_EXTEND
                                      : H::Op::BV_ZERO_EXTEND,
                                 value, static_cast<unsigned>(amount), loc);
        }
        if (!algebraic && (isIdent("shl") || isIdent("shr") || isIdent("sar")
                           || isIdent("and") || isIdent("or") || isIdent("xor")
                           || isIdent("umod") || isIdent("srem")
                           || isIdent("smod") || isIdent("udiv")
                           || isIdent("sdiv") || isIdent("add") || isIdent("sub")
                           || isIdent("mul"))) {
            const std::string op = tok().text;
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr lhs = atom(false, diags);
            H::ExprPtr rhs = atom(false, diags);
            if (!lhs || !rhs) { return nullptr; }
            static const std::unordered_map<std::string, H::Op> ops = {
                {"shl", H::Op::BV_SHL},   {"shr", H::Op::BV_LSHR},
                {"sar", H::Op::BV_ASHR}, {"and", H::Op::BV_AND},
                {"or", H::Op::BV_OR},     {"xor", H::Op::BV_XOR},
                {"umod", H::Op::BV_UREM}, {"srem", H::Op::BV_SREM},
                {"smod", H::Op::BV_SMOD}, {"udiv", H::Op::BV_UDIV},
                {"sdiv", H::Op::BV_SDIV}, {"add", H::Op::BV_ADD},
                {"sub", H::Op::BV_SUB},   {"mul", H::Op::BV_MUL},
            };
            if ((op == "udiv" || op == "sdiv") && report_ != nullptr
                && div_recorded_.insert(op).second) {
                // RECORDED (docs/languages/cryptoline.md §4.5): the machine
                // division operators map DIRECTLY onto SMT-LIB's bvudiv/bvsdiv,
                // including the total behaviour at zero -- bvudiv(x, 0) is all
                // ones and bvsdiv(x, 0) is 1 for nonnegative x, all ones
                // otherwise. No convention decision exists to take (SMT-LIB
                // FixedSizeBitVectors is the machine semantics), but the
                // assumption profile records that the translation relies on it.
                Uir::EncodingChoice ch;
                ch.site       = "rng " + op;
                ch.unified_op = op == "udiv" ? "bvudiv" : "bvsdiv";
                ch.strategy   = "direct-smtlib-bitvector-division";
                ch.fidelity   = Uir::Fidelity::exact();
                ch.rationale =
                    "CryptoLine's range '" + op + "' is the machine "
                    + std::string(op == "udiv" ? "unsigned" : "signed")
                    + " division; SMT-LIB's " + (op == "udiv" ? "bvudiv" : "bvsdiv")
                    + " has exactly that semantics and is TOTAL at a zero divisor"
                    + " (bvudiv x 0 = all ones; bvsdiv x 0 = 1 if x is nonnegative,"
                      " all ones otherwise), so no auxiliary axiom or convention"
                      " decision is needed -- the recording exists because the"
                      " assumption profile's division semantics relies on the"
                      " total-at-zero behaviour";
                report_->addChoice(std::move(ch));
            }
            return H::mkOp(ops.at(op), {lhs, rhs}, loc);
        }
        if (!algebraic && (isIdent("rol") || isIdent("ror"))) {
            const bool left_rotate = isIdent("rol");
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr value = atom(false, diags);
            H::ExprPtr amount = atom(false, diags);
            if (!value || !amount || value->sort.kind != H::SortKind::BITVEC
                || amount->sort.kind != H::SortKind::BITVEC
                || value->sort.width != amount->sort.width) {
                if (value && amount) {
                    diags.error(ErrorCode::E_TYPE,
                                "rotate operands must have the same bit-vector width", loc);
                }
                return nullptr;
            }
            const unsigned w = value->sort.width;
            const H::ExprPtr width =
                H::mkBitVec(binaryOf(std::to_string(w), w), w, loc);
            const H::ExprPtr normalized =
                H::mkOp(H::Op::BV_UREM, {amount, width}, loc);
            const H::ExprPtr complement =
                H::mkOp(H::Op::BV_SUB, {width, normalized}, loc);
            const H::ExprPtr shifted_left = H::mkOp(
                H::Op::BV_SHL,
                {value, left_rotate ? normalized : complement}, loc);
            const H::ExprPtr shifted_right = H::mkOp(
                H::Op::BV_LSHR,
                {value, left_rotate ? complement : normalized}, loc);
            return H::mkOp(H::Op::BV_OR, {shifted_left, shifted_right}, loc);
        }
        if (!algebraic && isIdent("not")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr value = atom(false, diags);
            return value ? H::mkOp(H::Op::BV_NOT, {value}, loc) : nullptr;
        }
        // `! e` is the other spelling of bit-wise NOT (parsers: NOTOP).
        if (!algebraic && isPunct("!")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr value = atom(false, diags);
            return value ? H::mkOp(H::Op::BV_NOT, {value}, loc) : nullptr;
        }
        // `neg e` / `~ e` at EXPRESSION level: two's-complement negation
        // (ast/cryptoline.mli: Rnegb), distinct from the `~`/`neg` PREDICATE
        // negation handled in predUnary.
        if (isIdent("neg") || isPunct("~")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr value = atom(algebraic, diags);
            return value ? H::mkOp(algebraic ? H::Op::NEG : H::Op::BV_NEG,
                                   {value}, loc)
                         : nullptr;
        }
        // `sq e` squares its operand (ast/cryptoline.mli: esq / rsq).
        if (isIdent("sq")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr value = atom(algebraic, diags);
            return value ? H::mkOp(algebraic ? H::Op::MUL : H::Op::BV_MUL,
                                   {value, value}, loc)
                         : nullptr;
        }
        // `pow e n`: prefix exponentiation by a constant, algebraic half
        // (parsers: POW eexp_primary eexp_primary).
        if (algebraic && isIdent("pow")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr base = atom(true, diags);
            if (!base) { return nullptr; }
            if (tok().kind != Tok::NUM
                || tok().text.find_first_not_of("0123456789") != std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "'pow' needs a numeric exponent", loc);
                return nullptr;
            }
            const std::string exp = tok().text;
            eat();
            unsigned long long n = 0;
            const char* first = exp.data();
            const auto parsed = std::from_chars(first, first + exp.size(), n);
            if (parsed.ec != std::errc() || parsed.ptr != first + exp.size()
                || n > 8192) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "exponentiation of an expression by a constant is bounded "
                            "at 8192; the literal-base form is exact at any size", loc);
                return nullptr;
            }
            if (n == 0) { return H::mkInt(1, loc); }
            H::ExprPtr result = base;
            for (unsigned long long k = 1; k < n; ++k) {
                result = H::mkOp(H::Op::MUL, {result, base}, loc);
            }
            return result;
        }
        // `poly p [e1, ..., en]` is e1 + e2*p + ... + en*p^(n-1), algebraic
        // half (ast/cryptoline.mli: poly).
        if (algebraic && isIdent("poly")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr p = sum(true, diags);
            if (!p || !expect("[", diags)) { return nullptr; }
            std::vector<H::ExprPtr> coeffs;
            while (!isPunct("]")) {
                H::ExprPtr c = sum(true, diags);
                if (!c) { return nullptr; }
                coeffs.push_back(c);
                if (isPunct(",")) { eat(); continue; }
                break;
            }
            if (!expect("]", diags)) { return nullptr; }
            if (coeffs.empty()) {
                diags.error(ErrorCode::E_PARSE, "poly needs at least one coefficient",
                            loc);
                return nullptr;
            }
            H::ExprPtr result = coeffs.front();
            H::ExprPtr power_of_p = p;
            for (std::size_t i = 1; i < coeffs.size(); ++i) {
                result = H::mkOp(H::Op::ADD,
                                 {result, H::mkOp(H::Op::MUL, {coeffs[i], power_of_p},
                                                  loc)},
                                 loc);
                power_of_p = H::mkOp(H::Op::MUL, {power_of_p, p}, loc);
            }
            return result;
        }
        // `adds [e1, ..., en]` / `muls [e1, ..., en]`: list folds. Over Int the
        // empty list is the unit 0 resp. 1 (ast/cryptoline.mli: eadds/emuls);
        // over bit-vectors an empty list has no width to take and is rejected
        // (parsers/common.ml: parse_rlistop).
        if (isIdent("adds") || isIdent("muls")) {
            const bool multiply = isIdent("muls");
            const Uir::SourceLoc loc = at();
            eat();
            if (!expect("[", diags)) { return nullptr; }
            std::vector<H::ExprPtr> items;
            while (!isPunct("]")) {
                H::ExprPtr e = algebraic ? sum(true, diags) : rangeExpr(diags);
                if (!e) { return nullptr; }
                items.push_back(e);
                if (isPunct(",")) { eat(); continue; }
                break;
            }
            if (!expect("]", diags)) { return nullptr; }
            const H::Op op = algebraic ? (multiply ? H::Op::MUL : H::Op::ADD)
                                       : (multiply ? H::Op::BV_MUL : H::Op::BV_ADD);
            if (items.empty()) {
                if (!algebraic) {
                    diags.error(ErrorCode::E_PARSE,
                                "an empty list of range expressions is not allowed",
                                loc);
                    return nullptr;
                }
                return H::mkInt(multiply ? "1" : "0", loc);
            }
            if (!algebraic) {
                for (const H::ExprPtr& item : items) {
                    if (item->sort.kind != H::SortKind::BITVEC
                        || item->sort.width != items.front()->sort.width) {
                        diags.error(ErrorCode::E_TYPE,
                                    "a list expression folds operands of one bit-vector "
                                    "width", loc);
                        return nullptr;
                    }
                }
            }
            H::ExprPtr result = items.front();
            for (std::size_t i = 1; i < items.size(); ++i) {
                result = H::mkOp(op, {result, items[i]}, loc);
            }
            return result;
        }
        // `const w n` / `const typ n`: a range constant with an explicit width
        // (parsers: CONST const_exp const_exp / CONST typ const_exp).
        if (!algebraic && isIdent("const")) {
            const Uir::SourceLoc loc = at();
            eat();
            VarType const_type;
            if (tok().kind == Tok::IDENT
                && (tok().text == "bit" || tok().text.rfind("uint", 0) == 0
                    || tok().text.rfind("sint", 0) == 0
                    || tok().text.rfind("int", 0) == 0)) {
                if (!typeName(const_type, diags)) { return nullptr; }
            } else {
                if (tok().kind != Tok::NUM
                    || tok().text.find_first_not_of("0123456789") != std::string::npos) {
                    diags.error(ErrorCode::E_PARSE,
                                "'const' needs a width or a type and then a value", loc);
                    return nullptr;
                }
                unsigned long long w = 0;
                const char* first = tok().text.data();
                const auto parsed =
                    std::from_chars(first, first + tok().text.size(), w);
                if (parsed.ec != std::errc() || parsed.ptr != first + tok().text.size()
                    || w == 0 || w > 4096) {
                    diags.error(ErrorCode::E_PARSE, "'const' has an invalid width", loc);
                    return nullptr;
                }
                eat();
                const_type = VarType{static_cast<unsigned>(w), false};
            }
            bool negative = false;
            if (isPunct("-")) { negative = true; eat(); }
            if (tok().kind != Tok::NUM) {
                diags.error(ErrorCode::E_PARSE, "'const' needs a value", loc);
                return nullptr;
            }
            const std::string literal = tok().text;
            eat();
            std::string bits;
            if (!literalBits(literal, negative, const_type, bits, diags, loc)) {
                return nullptr;
            }
            return H::mkBitVec(bits, const_type.width, loc);
        }
        if (!algebraic && isIdent("concat")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr high = atom(false, diags);
            H::ExprPtr low = atom(false, diags);
            return high && low ? H::mkOp(H::Op::BV_CONCAT, {high, low}, loc)
                               : nullptr;
        }
        if (isPunct("(")) {
            const Uir::SourceLoc loc = at();
            eat();
            H::ExprPtr e = algebraic ? sum(true, diags) : rangeExpr(diags);
            if (!e) { return nullptr; }
            if (!expect(")", diags)) { return nullptr; }
            if (!algebraic && isPunct("@")) {
                eat();
                VarType annotation;
                if (!typeAnnotation(annotation, diags)) { return nullptr; }
                if (e->sort.kind != H::SortKind::BITVEC) {
                    diags.error(ErrorCode::E_TYPE,
                                "only a bit-vector constant expression can carry a range "
                                "width annotation", loc);
                    return nullptr;
                }
                if (e->sort.width < annotation.width) {
                    e = H::mkBvExtend(H::Op::BV_ZERO_EXTEND, e,
                                      annotation.width - e->sort.width, loc);
                } else if (e->sort.width > annotation.width) {
                    if (e->kind != H::ExprKind::LIT_BITVEC) {
                        diags.error(ErrorCode::E_TYPE,
                                    "a non-constant range expression cannot be narrowed by "
                                    "a constant annotation", loc);
                        return nullptr;
                    }
                    const std::size_t first_one = e->name.find('1');
                    const std::size_t significant = first_one == std::string::npos
                                                        ? 1
                                                        : e->name.size() - first_one;
                    if (significant > annotation.width) {
                        diags.error(ErrorCode::E_TYPE,
                                    "parenthesized constant is outside its annotated width",
                                    loc);
                        return nullptr;
                    }
                    e = H::mkBvExtract(e, annotation.width - 1, 0, loc);
                }
            }
            return e;
        }
        if (tok().kind == Tok::NUM) {
            std::string digits = tok().text;
            const Uir::SourceLoc loc = at();
            eat();
            if (isPunct("**")) {                    // `2**64`
                eat();
                if (tok().kind != Tok::NUM) {
                    diags.error(ErrorCode::E_PARSE, "'**' needs a numeric exponent", loc);
                    return nullptr;
                }
                const std::string exp = tok().text;
                eat();
                if (digits.rfind("0x", 0) == 0 || digits.rfind("0X", 0) == 0
                    || digits.rfind("0b", 0) == 0 || digits.rfind("0B", 0) == 0) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "non-decimal bases in exponentiation are not implemented", loc);
                    return nullptr;
                }
                digits = power(digits, exp);
            }
            if (algebraic) {
                if (digits.rfind("0x", 0) == 0 || digits.rfind("0X", 0) == 0
                    || digits.rfind("0b", 0) == 0 || digits.rfind("0B", 0) == 0) {
                    const std::string bits = magnitudeBits(digits);
                    std::string decimal = "0";
                    for (char bit : bits) {
                        decimal = mulDecimal(decimal, "2");
                        if (bit == '1') {
                            int carry = 1;
                            for (std::size_t i = decimal.size(); i-- > 0 && carry != 0;) {
                                const int value = decimal[i] - '0' + carry;
                                decimal[i] = static_cast<char>('0' + (value % 10));
                                carry = value / 10;
                            }
                            if (carry != 0) { decimal.insert(decimal.begin(), '1'); }
                        }
                    }
                    digits = decimal;
                }
                return H::mkInt(digits, loc);
            }
            std::optional<VarType> annotation;
            if (isPunct("@")) {
                eat();
                VarType type;
                if (!typeAnnotation(type, diags)) { return nullptr; }
                annotation = type;
            }
            // In the range half a literal takes the width of the variable it is
            // written against -- `rng x <= 4` compares two 8-bit values when x
            // is uint8. Refusing it outright, which this did first, turns
            // ordinary CryptoLine into an unsupported construct.
            const unsigned required_bits =
                static_cast<unsigned>(magnitudeBits(digits).size());
            const unsigned width = annotation
                                       ? annotation->width
                                       : std::max(rng_width_, required_bits);
            if (width == 0) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a decimal literal in a range condition that mentions no "
                            "declared variable has no width to take", loc);
                return nullptr;
            }
            const VarType literal_type = annotation.value_or(VarType{width, false});
            std::string bits;
            if (!literalBits(digits, false, literal_type, bits, diags, loc)) {
                return nullptr;
            }
            return H::mkBitVec(bits, width, loc);
        }
        if (tok().kind != Tok::IDENT) {
            if (isPunct("%")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "vector expressions (`%v`, `%v[i]`) are an implementation "
                            "extension the manual's grammar does not define; the "
                            "scalar core refuses them", at());
                return nullptr;
            }
            if (isPunct("$")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "named integer constants (`const id = ...`, read back as "
                            "'$id') are not implemented", at());
                return nullptr;
            }
            diags.error(ErrorCode::E_PARSE, "expected a term, got '" + tok().text + "'", at());
            return nullptr;
        }
        const std::string name = tok().text;
        const Uir::SourceLoc loc = at();
        // Under an `inline`, a formal parameter bound to a constant actual is
        // the literal; one bound to a variable resolves through the binding.
        const InlineBinding* binding = inlineBinding(name);
        if (binding != nullptr && binding->is_const) {
            eat();
            const H::ExprPtr& literal = binding->literal;
            if (!algebraic) { return literal; }
            return H::mkOp(binding->type.is_signed ? H::Op::BV_TO_INT
                                                   : H::Op::BV_TO_NAT,
                           {literal}, loc);
        }
        const std::string resolved = binding != nullptr ? binding->actual : name;
        const std::string ssa = current(resolved);
        if (ssa.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "'" + name + "' is used before it is defined", loc);
            return nullptr;
        }
        eat();
        if (!algebraic) { return ref(ssa); }
        // **The conversion the signedness declaration decides.** bv2nat reads
        // the bits as [0, 2^w) and bv2int as [-2^(w-1), 2^(w-1)); both are
        // BitVec -> Int, so a wrong choice shifts every negative value by 2^w
        // with nothing downstream able to tell. The declaration is the only
        // evidence, and it is used here rather than any property of the context.
        const bool is_signed = types_.at(ssa).is_signed;
        // RECORDED, because nothing downstream can see it. Both operators are
        // BitVec -> Int, so the emitted script does not say which reading of the
        // bits was taken -- and a wrong one shifts every negative value by 2^w
        // while type-checking perfectly. The declaration is the only evidence,
        // which is exactly the situation EncodingChoice exists for: a decision a
        // later stage cannot see being made.
        //
        // Once per VARIABLE rather than per occurrence: the declaration decides
        // it, so one entry per declared name is the granularity at which a
        // reader can check it, and per-occurrence entries would be the same
        // fact repeated.
        if (report_ != nullptr && lift_recorded_.insert(resolved).second) {
            Uir::EncodingChoice ch;
            ch.site       = resolved;
            ch.unified_op = is_signed ? "bv2int" : "bv2nat";
            ch.strategy   = is_signed ? "signed-lift-from-declaration"
                                      : "unsigned-lift-from-declaration";
            ch.fidelity   = Uir::Fidelity::exact();
            ch.rationale =
                "'" + resolved + "' is declared "
                + (is_signed ? "sint" : "uint")
                + std::to_string(types_.at(ssa).width)
                + ", so its value in the algebraic half of a condition is read as "
                + (is_signed ? "[-2^(w-1), 2^(w-1)) by bv2int"
                             : "[0, 2^w) by bv2nat")
                + ". Both are BitVec -> Int and the script does not record which, "
                  "so the declaration is the only evidence for the reading; the "
                  "other one shifts every negative value by exactly 2^w";
            report_->addChoice(std::move(ch));
        }
        return H::mkOp(is_signed ? H::Op::BV_TO_INT : H::Op::BV_TO_NAT,
                       {ref(ssa)}, loc);
    }

    /** `base ** exp` as decimal text. Exact: the exponents in this format are
     *  word sizes, so the result is routinely larger than 64 bits and a
     *  `long long` would silently wrap -- which is the one thing an overflow
     *  specification must not do. */
    static std::string power(const std::string& base, const std::string& exp) {
        unsigned long long e = 0;
        const char* first = exp.data();
        std::from_chars(first, first + exp.size(), e);
        std::string acc = "1";
        for (unsigned long long k = 0; k < e && k < 8192; ++k) { acc = mulDecimal(acc, base); }
        return acc;
    }
    static std::string mulDecimal(const std::string& a, const std::string& b) {
        std::vector<int> out(a.size() + b.size(), 0);
        for (std::size_t i = a.size(); i-- > 0;) {
            for (std::size_t j = b.size(); j-- > 0;) {
                const int p = (a[i] - '0') * (b[j] - '0') + out[i + j + 1];
                out[i + j + 1] = p % 10;
                out[i + j] += p / 10;
            }
        }
        std::string s;
        for (int d : out) { if (!(s.empty() && d == 0)) { s += static_cast<char>('0' + d); } }
        return s.empty() ? "0" : s;
    }

    // ---- instructions ----------------------------------------------------

    struct AtomValue {
        H::ExprPtr value;
        VarType    type;
    };

    /** Read one typed CryptoLine atom. An unannotated literal is legal only when
     * its type is fixed by the instruction context. */
    std::optional<AtomValue> atomValue(const std::optional<VarType>& expected,
                                       Uir::Diagnostics& diags) {
        const Uir::SourceLoc loc = at();
        bool negative = false;
        if (isPunct("-")) {
            negative = true;
            eat();
        }

        if (tok().kind == Tok::NUM) {
            const std::string literal = tok().text;
            eat();
            std::optional<VarType> annotated;
            if (isPunct("@")) {
                eat();
                VarType type;
                if (!typeAnnotation(type, diags)) { return std::nullopt; }
                annotated = type;
            }
            if (!annotated && !expected) {
                diags.error(ErrorCode::E_TYPE,
                            "literal '" + std::string(negative ? "-" : "") + literal
                                + "' needs a type annotation in this position", loc);
                return std::nullopt;
            }
            const VarType type = annotated ? *annotated : *expected;
            if (expected && !sameType(type, *expected)) {
                diags.error(ErrorCode::E_TYPE,
                            "literal annotation is "
                                + std::string(type.is_signed ? "sint" : "uint")
                                + std::to_string(type.width) + " where "
                                + std::string(expected->is_signed ? "sint" : "uint")
                                + std::to_string(expected->width) + " is required", loc);
                return std::nullopt;
            }
            std::string bits;
            if (!literalBits(literal, negative, type, bits, diags, loc)) {
                return std::nullopt;
            }
            return AtomValue{H::mkBitVec(bits, type.width, loc), type};
        }

        if (negative) {
            diags.error(ErrorCode::E_PARSE, "unary '-' must precede a typed constant", loc);
            return std::nullopt;
        }
        if (tok().kind != Tok::IDENT) {
            // `%v` starts a vector expression and `$c` a named-constant
            // dereference; both are named refusals, not generic parse errors.
            if (isPunct("%")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "vector expressions (`%v`, `%v[i]`) are an implementation "
                            "extension the manual's grammar does not define; the "
                            "scalar core refuses them", loc);
                return std::nullopt;
            }
            if (isPunct("$")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "named integer constants (`const id = ...`, read back as "
                            "'$id') are not implemented", loc);
                return std::nullopt;
            }
            diags.error(ErrorCode::E_PARSE,
                        "expected an operand, got '" + tok().text + "'", loc);
            return std::nullopt;
        }
        std::string source_name = tok().text;
        // Under an `inline`, a formal parameter stands for its actual:
        // a variable (resolved dynamically, so an actual that is also an
        // output sees its own updates) or a typed constant.
        if (const InlineBinding* binding = inlineBinding(source_name)) {
            if (binding->is_const) {
                eat();
                if (isPunct("@")) {
                    eat();
                    VarType annotated;
                    if (!typeAnnotation(annotated, diags)) { return std::nullopt; }
                    if (!sameType(binding->type, annotated)) {
                        diags.error(ErrorCode::E_TYPE,
                                    "annotation on '" + source_name
                                        + "' disagrees with its declared type", loc);
                        return std::nullopt;
                    }
                }
                if (expected && !sameType(binding->type, *expected)) {
                    diags.error(ErrorCode::E_TYPE,
                                "'" + source_name + "' has type "
                                    + std::string(binding->type.is_signed ? "sint" : "uint")
                                    + std::to_string(binding->type.width) + " where "
                                    + std::string(expected->is_signed ? "sint" : "uint")
                                    + std::to_string(expected->width)
                                    + " is required; CryptoLine has no implicit "
                                      "conversion", loc);
                    return std::nullopt;
                }
                return AtomValue{binding->literal, binding->type};
            }
            source_name = binding->actual;
        }
        // A ghost variable is specification-only: never an instruction
        // operand (typecheck/std.ml: defined_atom draws from program
        // variables only).
        if (ghosts_.count(source_name) != 0) {
            diags.error(ErrorCode::E_TYPE,
                        "'" + source_name
                            + "' is a ghost variable: it can appear only in "
                              "specifications (assert/assume/cut/ghost/postconditions), "
                              "not as an instruction operand", loc);
            return std::nullopt;
        }
        const std::string ssa = current(source_name);
        if (ssa.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "'" + source_name + "' is used before it is defined", loc);
            return std::nullopt;
        }
        VarType type = types_.at(ssa);
        eat();
        if (isPunct("@")) {
            eat();
            VarType annotated;
            if (!typeAnnotation(annotated, diags)) { return std::nullopt; }
            if (!sameType(type, annotated)) {
                diags.error(ErrorCode::E_TYPE,
                            "annotation on '" + source_name
                                + "' disagrees with its declared type", loc);
                return std::nullopt;
            }
        }
        if (expected && !sameType(type, *expected)) {
            diags.error(ErrorCode::E_TYPE,
                        "'" + source_name + "' has type "
                            + std::string(type.is_signed ? "sint" : "uint")
                            + std::to_string(type.width) + " where "
                            + std::string(expected->is_signed ? "sint" : "uint")
                            + std::to_string(expected->width)
                            + " is required; CryptoLine has no implicit conversion", loc);
            return std::nullopt;
        }
        return AtomValue{ref(ssa), type};
    }

    static std::string magnitudeBits(const std::string& literal) {
        if (literal.size() > 2 && literal[0] == '0'
            && (literal[1] == 'b' || literal[1] == 'B')) {
            std::string bits = literal.substr(2);
            const std::size_t one = bits.find('1');
            return one == std::string::npos ? "0" : bits.substr(one);
        }
        if (literal.size() > 2 && literal[0] == '0'
            && (literal[1] == 'x' || literal[1] == 'X')) {
            std::string bits;
            for (std::size_t i = 2; i < literal.size(); ++i) {
                const char c = literal[i];
                const unsigned value = c >= '0' && c <= '9'
                                           ? static_cast<unsigned>(c - '0')
                                           : static_cast<unsigned>(10 + std::tolower(c) - 'a');
                for (int bit = 3; bit >= 0; --bit) {
                    bits += ((value >> bit) & 1U) != 0U ? '1' : '0';
                }
            }
            const std::size_t one = bits.find('1');
            return one == std::string::npos ? "0" : bits.substr(one);
        }
        std::string digits = literal;
        std::string bits;
        while (!(digits.size() == 1 && digits[0] == '0')) {
            std::string q;
            int rem = 0;
            for (char c : digits) {
                const int cur = rem * 10 + (c - '0');
                q += static_cast<char>('0' + cur / 2);
                rem = cur % 2;
            }
            std::size_t nz = q.find_first_not_of('0');
            digits = nz == std::string::npos ? "0" : q.substr(nz);
            bits += static_cast<char>('0' + rem);
        }
        std::reverse(bits.begin(), bits.end());
        return bits.empty() ? "0" : bits;
    }

    static bool literalBits(const std::string& literal, bool negative,
                            const VarType& type, std::string& out,
                            Uir::Diagnostics& diags, const Uir::SourceLoc& loc) {
        std::string magnitude = magnitudeBits(literal);
        bool fits = false;
        if (!negative) {
            fits = type.is_signed ? magnitude.size() < type.width
                                  : magnitude.size() <= type.width;
        } else if (type.is_signed) {
            fits = magnitude.size() < type.width;
            if (magnitude.size() == type.width && magnitude.front() == '1') {
                fits = magnitude.find('1', 1) == std::string::npos;
            }
        }
        if (!fits) {
            diags.error(ErrorCode::E_TYPE,
                        "constant '" + std::string(negative ? "-" : "") + literal
                            + "' is outside "
                            + std::string(type.is_signed ? "sint" : "uint")
                            + std::to_string(type.width), loc);
            return false;
        }
        while (magnitude.size() < type.width) { magnitude.insert(magnitude.begin(), '0'); }
        if (negative && magnitude.find('1') != std::string::npos) {
            for (char& bit : magnitude) { bit = bit == '0' ? '1' : '0'; }
            for (std::size_t i = magnitude.size(); i-- > 0;) {
                if (magnitude[i] == '0') { magnitude[i] = '1'; break; }
                magnitude[i] = '0';
            }
        }
        out = "#b" + magnitude;
        return true;
    }

    static std::string binaryOf(const std::string& literal, unsigned width) {
        std::string bits = magnitudeBits(literal);
        while (bits.size() < width) { bits.insert(bits.begin(), '0'); }
        if (bits.size() > width) { bits.erase(0, bits.size() - width); }
        return "#b" + bits;
    }

    /** The destination name of an instruction, at a type taken from a source
     *  operand's. Reading it before the sources are read is what makes
     *  `mov x x` mean "the old x", which SSA requires. */
    bool destination(Dest& out, Uir::Diagnostics& diags) {
        if (tok().kind != Tok::IDENT) {
            if (isPunct("%")) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "vector destinations (`%v`) are an implementation "
                            "extension the manual's grammar does not define; the "
                            "scalar core refuses them", at());
                return false;
            }
            diags.error(ErrorCode::E_PARSE, "expected a destination variable", at());
            return false;
        }
        out.name = tok().text;
        // A ghost variable cannot become a program variable
        // (parsers/common.ml: resolve_lv_with) -- the layers stay apart.
        if (ghosts_.count(out.name) != 0 && inlineBinding(out.name) == nullptr) {
            diags.error(ErrorCode::E_TYPE,
                        "'" + out.name
                            + "' has been defined as a ghost variable; an instruction "
                              "destination is a program variable", at());
            return false;
        }
        eat();
        if (isPunct("@")) {
            eat();
            VarType type;
            if (!typeAnnotation(type, diags)) { return false; }
            out.annotation = type;
        }
        return true;
    }

    std::optional<VarType> exactDestinationType(const Dest& dest,
                                                const VarType& inferred,
                                                Uir::Diagnostics& diags) const {
        if (dest.annotation && !sameType(*dest.annotation, inferred)) {
            diags.error(ErrorCode::E_TYPE,
                        "destination '" + dest.name + "' is annotated "
                            + std::string(dest.annotation->is_signed ? "sint" : "uint")
                            + std::to_string(dest.annotation->width) + " but this instruction "
                              "requires "
                            + std::string(inferred.is_signed ? "sint" : "uint")
                            + std::to_string(inferred.width), at());
            return std::nullopt;
        }
        return dest.annotation ? *dest.annotation : inferred;
    }

    /** The operand type a `u*`/`s*` prefix FIXES: the first operand's width at
     *  the prefix's signedness. The operand must already have it -- the prefix
     *  selects the unsigned/signed reading of the operation and never converts
     *  (parsers/common.ml: parse_uadd_at hints typ_to_unsigned of the operand's
     *  type; typecheck/std.ml: check_same_typ makes destination and operands
     *  share it). Without a prefix this is the identity. */
    std::optional<VarType> variantType(const std::optional<bool>& forced,
                                       const std::string& op, const VarType& operand,
                                       Uir::Diagnostics& diags,
                                       const Uir::SourceLoc& loc) const {
        if (!forced) { return operand; }
        const VarType fixed{operand.width, *forced};
        if (!sameType(operand, fixed)) {
            diags.error(ErrorCode::E_TYPE,
                        "'" + op + "' is the explicit "
                            + std::string(*forced ? "signed" : "unsigned")
                            + " variant: its operands must be declared "
                            + (*forced ? "sint" : "uint") + std::to_string(fixed.width)
                            + " already; the prefix selects the interpretation, it does "
                              "not convert",
                        loc);
            return std::nullopt;
        }
        return fixed;
    }

    bool literalShiftAmount(unsigned width, unsigned& amount,
                            Uir::Diagnostics& diags,
                            const Uir::SourceLoc& loc) {
        if (tok().kind != Tok::NUM
            || tok().text.find_first_not_of("0123456789") != std::string::npos) {
            diags.error(ErrorCode::E_PARSE,
                        "this instruction needs a literal shift amount", loc);
            return false;
        }
        unsigned long long parsed_amount = 0;
        const char* first = tok().text.data();
        const char* last = first + tok().text.size();
        const auto parsed = std::from_chars(first, last, parsed_amount);
        eat();
        if (parsed.ec != std::errc() || parsed.ptr != last || parsed_amount >= width) {
            diags.error(ErrorCode::E_TYPE,
                        "shift amount must be smaller than the "
                            + std::to_string(width) + "-bit source width", loc);
            return false;
        }
        amount = static_cast<unsigned>(parsed_amount);
        return true;
    }

    // ---- procedures ------------------------------------------------------
    //
    // The official semantics (parsers/common.ml: parse_call_at /
    // parse_inline_at / parse_inlinespec_at):
    //
    //   * `call p(a...)` is a REAL call replaced by the contract: the callee's
    //     precondition (over the inputs) is ASSERTED at the call site, the
    //     actual outputs are havocked (nondet), and the callee's
    //     postcondition is ASSUMED. An actual used as input AND output gets
    //     its entry value captured by a fresh ghost variable so the assumed
    //     postcondition can relate the output to the input's call-time value
    //     (mk_ghost_instr_for_actuals). The body never enters the encoding --
    //     the callee is trusted against its contract, which is why the manual
    //     says call "is currently incompatible with equivalence checking".
    //   * `inline p(a...)` splices the BODY at the call site, formals
    //     substituted by actuals; pre/postconditions are ignored. Local
    //     variables are NOT renamed by default (Options.Std.rename_local is
    //     false) -- textual splicing, which our SSA versioning makes exact.
    //   * `inlinespec p(a...)` is semantically inline but verified through the
    //     contract: like call, plus nondet over the body's assigned variables
    //     (not only the outputs), so later reads of them see a defined value.
    //
    // Shared requirements: the callee is an earlier-declared, non-main
    // procedure; actual and formal counts and types match exactly
    // (is_type_compatible); input actuals that are variables must be defined;
    // output actuals must be variables and distinct; and a formal input that
    // is assigned in the body must not appear in the postcondition
    // (check_updated_formal_inputs -- else the postcondition's reading of the
    // input would mean two different values at the call site).

    struct ActualArg {
        bool is_var = true;
        std::string name;                  // var: its source name
        H::ExprPtr literal;                // const: the bit-vector literal
        VarType type;
        bool defined = false;              // var: currently defined
    };

    /** One actual parameter, typed against its formal. An input actual is an
     *  atom (a defined variable or a typed constant); an output actual must
     *  be a variable (parsers/common.ml: resolve_output_atom_with rejects
     *  constants), need not be defined yet, and takes the formal's type. */
    std::optional<ActualArg> actualArg(const VarType& formal, bool output,
                                       const std::string& fname,
                                       Uir::Diagnostics& diags) {
        const Uir::SourceLoc loc = at();
        ActualArg arg;
        arg.type = formal;
        if (tok().kind == Tok::IDENT
            && (tok().text == "bit" || tok().text.rfind("uint", 0) == 0
                || tok().text.rfind("sint", 0) == 0
                || tok().text.rfind("int", 0) == 0)
            && pos_ + 1 < toks_.size()
            && (toks_[pos_ + 1].kind == Tok::NUM
                || (toks_[pos_ + 1].kind == Tok::PUNCT
                    && toks_[pos_ + 1].text == "-"))) {
            // `typ const` -- the typed-constant spelling of an input actual.
            VarType ty;
            if (!typeName(ty, diags)) { return std::nullopt; }
            arg.type = ty;
            return finishConstActual(arg, formal, output, fname, diags, loc);
        }
        if (tok().kind == Tok::NUM
            || (tok().kind == Tok::PUNCT && tok().text == "-")) {
            return finishConstActual(arg, formal, output, fname, diags, loc);
        }
        if (tok().kind != Tok::IDENT) {
            diags.error(ErrorCode::E_PARSE,
                        "expected an actual parameter, got '" + tok().text + "'", loc);
            return std::nullopt;
        }
        // A variable actual, optionally annotated.
        arg.name = tok().text;
        arg.is_var = true;
        // A ghost can be an INPUT actual (it is a specification-level value)
        // but never an output; current() resolves inline bindings.
        arg.defined = ghosts_.count(arg.name) != 0 || !current(arg.name).empty();
        eat();
        if (isPunct("@")) {
            eat();
            VarType annotated;
            if (!typeAnnotation(annotated, diags)) { return std::nullopt; }
            if (!sameType(annotated, formal)) {
                diags.error(ErrorCode::E_TYPE,
                            "the actual parameter '" + arg.name + "' is annotated "
                                + std::string(annotated.is_signed ? "sint" : "uint")
                                + std::to_string(annotated.width)
                                + " where the formal parameter of '" + fname + "' is "
                                + std::string(formal.is_signed ? "sint" : "uint")
                                + std::to_string(formal.width), loc);
                return std::nullopt;
            }
        }
        if (arg.defined) {
            const VarType actual_type = types_.at(current(arg.name));
            if (!sameType(actual_type, formal)) {
                diags.error(ErrorCode::E_TYPE,
                            "the type of the actual parameter '" + arg.name
                                + "' is not compatible with the type of the formal "
                                  "parameter ("
                                + std::string(formal.is_signed ? "sint" : "uint")
                                + std::to_string(formal.width) + ")", loc);
                return std::nullopt;
            }
        }
        return arg;
    }

    std::optional<ActualArg> finishConstActual(ActualArg arg,
                                               const VarType& formal, bool output,
                                               const std::string& fname,
                                               Uir::Diagnostics& diags,
                                               const Uir::SourceLoc& loc) {
        if (output) {
            diags.error(ErrorCode::E_PARSE,
                        "a constant cannot be used as an output actual parameter of '"
                            + fname + "'", loc);
            return std::nullopt;
        }
        bool negative = false;
        if (isPunct("-")) { negative = true; eat(); }
        if (tok().kind != Tok::NUM) {
            diags.error(ErrorCode::E_PARSE, "expected a constant actual parameter",
                        loc);
            return std::nullopt;
        }
        const std::string literal = tok().text;
        eat();
        if (isPunct("@")) {
            eat();
            VarType annotated;
            if (!typeAnnotation(annotated, diags)) { return std::nullopt; }
            if (!sameType(annotated, arg.type)) {
                diags.error(ErrorCode::E_TYPE,
                            "the actual constant's annotation disagrees with the "
                            "formal parameter's type",
                            loc);
                return std::nullopt;
            }
        }
        arg.is_var = false;
        std::string bits;
        if (!literalBits(literal, negative, arg.type, bits, diags, loc)) {
            return std::nullopt;
        }
        arg.literal = H::mkBitVec(bits, arg.type.width, loc);
        return arg;
    }

    bool callLike(const std::string& kind, Uir::Diagnostics& diags,
                  const Uir::SourceLoc& loc) {
        if (tok().kind != Tok::IDENT) {
            diags.error(ErrorCode::E_PARSE,
                        "expected a procedure name after '" + kind + "'", at());
            return false;
        }
        const std::string fname = tok().text;
        eat();
        if (fname == "main") {
            diags.error(ErrorCode::E_PARSE,
                        "the main procedure cannot be " + kind + "ed", loc);
            return false;
        }
        const auto it = procs_.find(fname);
        if (it == procs_.end() || it->second.ordinal >= current_ordinal_) {
            diags.error(ErrorCode::E_PARSE,
                            "cannot " + kind + " an undefined procedure '" + fname
                                + "'; a call names an earlier-declared procedure", loc);
            return false;
        }
        const ProcDecl& callee = it->second;
        if (!expect("(", diags)) { return false; }
        std::vector<ActualArg> actuals;
        const std::vector<std::pair<std::string, VarType>>* formals = &callee.ins;
        std::size_t formal_index = 0;
        bool now_outputs = false;
        if (!isPunct(")")) {
            for (;;) {
                if (formal_index >= formals->size()) {
                    if (now_outputs || formals == &callee.outs) {
                        diags.error(ErrorCode::E_PARSE,
                                    "the number of actual parameters exceeds the "
                                    "number of formal parameters of '" + fname + "'",
                                    loc);
                        return false;
                    }
                    formals = &callee.outs;
                    formal_index = 0;
                    now_outputs = true;
                    if (formals->empty()) { break; }
                }
                const auto& formal = (*formals)[formal_index];
                std::optional<ActualArg> arg =
                    actualArg(formal.second, now_outputs, fname, diags);
                if (!arg) { return false; }
                actuals.push_back(std::move(*arg));
                ++formal_index;
                if (isPunct(",")) { eat(); continue; }
                break;
            }
        }
        if (formals->size() != formal_index
            || (formals == &callee.ins && !callee.outs.empty())) {
            diags.error(ErrorCode::E_PARSE,
                        "the number of actual parameters of '" + fname
                            + "' does not match its " + std::to_string(callee.ins.size())
                            + " input and " + std::to_string(callee.outs.size())
                            + " output formal parameters", loc);
            return false;
        }
        if (!expect(")", diags)) { return false; }
        // Input actuals that are variables must be defined; output actuals
        // must be distinct (parsers/common.ml: check_undefined_actuals,
        // check_distinct_actual_outputs).
        std::unordered_set<std::string> output_names;
        for (std::size_t i = 0; i < callee.ins.size(); ++i) {
            if (actuals[i].is_var && !actuals[i].defined) {
                diags.error(ErrorCode::E_PARSE,
                            "undefined program variable used as an input actual: '"
                                + actuals[i].name + "'", loc);
                return false;
            }
        }
        for (std::size_t j = 0; j < callee.outs.size(); ++j) {
            const std::string& oname = actuals[callee.ins.size() + j].name;
            if (!output_names.insert(oname).second) {
                diags.error(ErrorCode::E_PARSE,
                            "output actual parameters must be distinct in a " + kind
                                + ": '" + oname + "'", loc);
                return false;
            }
        }
        // A formal input assigned in the body cannot appear in the
        // postcondition; and for inline, its actual must be a variable.
        for (const std::string& f : callee.assigned_inputs) {
            if (kind != "inline" && callee.post_formals.count(f) != 0) {
                diags.error(ErrorCode::E_PARSE,
                            "the formal input parameter '" + f
                                + "' is assigned in the body of '" + fname
                                + "' and used in its postcondition; its call-site "
                                  "value would be ambiguous", loc);
                return false;
            }
        }
        for (std::size_t i = 0; i < callee.ins.size(); ++i) {
            if (kind == "inline"
                && callee.assigned_inputs.count(callee.ins[i].first) != 0
                && !actuals[i].is_var) {
                diags.error(ErrorCode::E_TYPE,
                            "an actual parameter must be a variable if the "
                            "corresponding formal parameter is assigned in the "
                            "procedure to be inlined: formal '"
                                + callee.ins[i].first + "'", loc);
                return false;
            }
        }
        if (kind == "inline") { return doInline(callee, actuals, diags); }
        return doCallSpec(callee, actuals, kind == "inlinespec", diags, loc, pos_);
    }

    /** The contract replacement shared by `call` and `inlinespec`. */
    bool doCallSpec(const ProcDecl& callee, const std::vector<ActualArg>& actuals,
                    bool inlinespec, Uir::Diagnostics& diags,
                    const Uir::SourceLoc& loc, std::size_t site) {
        const std::size_t nin = callee.ins.size();
        // Inout actuals: capture each one's entry value with a fresh ghost,
        // named deterministically by call site and formal (the body is also
        // validated at registration, and the two passes must agree).
        std::unordered_map<std::string, H::ExprPtr> inout_ghosts;
        for (std::size_t i = 0; i < nin; ++i) {
            if (!actuals[i].is_var) { continue; }
            bool also_output = false;
            for (std::size_t j = 0; j < callee.outs.size(); ++j) {
                if (actuals[nin + j].name == actuals[i].name) { also_output = true; }
            }
            if (!also_output) { continue; }
            const VarType ty = callee.ins[i].second;
            const std::string gname =
                "callghost!" + std::to_string(site) + "!" + std::to_string(i);
            ghosts_.insert(gname);   // before define(): ghosts are not
            define(gname, ty);       // "assigned in the body"
            const H::ExprPtr g = ref(gname);
            const H::ExprPtr a = ref(current(actuals[i].name));
            // The capture predicate is assumed on both halves, exactly like a
            // ghost instruction (mk_ghost_instr_for_actuals).
            prefix_e_.push_back(H::mkOp(H::Op::EQ, {integerValue(g, ty, loc),
                                                    integerValue(a, ty, loc)}, loc));
            prefix_r_.push_back(H::mkOp(H::Op::EQ, {g, a}, loc));
            ghosts_e_.push_back(prefix_e_.back());
            ghosts_r_.push_back(prefix_r_.back());
            inout_ghosts[callee.ins[i].first] = g;
        }
        // Assert the precondition over the inputs at their call-time values.
        std::unordered_map<std::string, H::ExprPtr> pre_map;
        for (std::size_t i = 0; i < nin; ++i) {
            const H::ExprPtr actual_expr =
                actuals[i].is_var ? ref(current(actuals[i].name)) : actuals[i].literal;
            for (const std::string& v : callee.formal_versions.at(callee.ins[i].first)) {
                pre_map[v] = actual_expr;
            }
        }
        for (const PredClause& p : callee.pre) {
            if (p.expr->kind == H::ExprKind::LIT_BOOL && p.expr->bool_value) {
                continue;
            }
            addObligation(substIdents(p.expr, pre_map), p.algebraic, ProveWith{}, loc);
        }
        // Havoc the outputs (nondet), then assume the postcondition -- with
        // the inout inputs read through their entry-value ghosts.
        for (std::size_t j = 0; j < callee.outs.size(); ++j) {
            define(actuals[nin + j].name, callee.outs[j].second);
        }
        if (inlinespec) {
            // inlinespec is semantically inline: the body's assigned
            // variables exist afterwards, havocked like the outputs.
            for (const auto& [assigned, ty] : callee.assigned) {
                std::string target = assigned;
                const auto f = std::find_if(
                    callee.ins.begin(), callee.ins.end(),
                    [&assigned = assigned](const std::pair<std::string, VarType>& formal) {
                        return formal.first == assigned;
                    });
                if (f != callee.ins.end()) {
                    const std::size_t i =
                        static_cast<std::size_t>(f - callee.ins.begin());
                    if (!actuals[i].is_var) { continue; }
                    target = actuals[i].name;
                }
                bool is_output = false;
                for (std::size_t j = 0; j < callee.outs.size(); ++j) {
                    if (actuals[nin + j].name == target) { is_output = true; }
                }
                if (!is_output && ghosts_.count(target) == 0) {
                    define(target, ty);
                }
            }
        }
        std::unordered_map<std::string, H::ExprPtr> post_map;
        for (std::size_t i = 0; i < nin; ++i) {
            H::ExprPtr actual_expr;
            const auto g = inout_ghosts.find(callee.ins[i].first);
            if (g != inout_ghosts.end()) {
                actual_expr = g->second;
            } else {
                actual_expr =
                    actuals[i].is_var ? ref(current(actuals[i].name)) : actuals[i].literal;
            }
            for (const std::string& v : callee.formal_versions.at(callee.ins[i].first)) {
                post_map[v] = actual_expr;
            }
        }
        for (std::size_t j = 0; j < callee.outs.size(); ++j) {
            const H::ExprPtr out_expr = ref(current(actuals[nin + j].name));
            for (const std::string& v :
                 callee.formal_versions.at(callee.outs[j].first)) {
                post_map[v] = out_expr;
            }
        }
        for (const PredClause& p : callee.post) {
            if (p.expr->kind == H::ExprKind::LIT_BOOL && p.expr->bool_value) {
                continue;
            }
            (p.algebraic ? prefix_e_ : prefix_r_).push_back(substIdents(p.expr, post_map));
        }
        return true;
    }

    /** inline splices the callee body at the call site: the body's token
     *  range is re-translated with the formals bound to the actuals. */
    bool doInline(const ProcDecl& callee, const std::vector<ActualArg>& actuals,
                  Uir::Diagnostics& diags) {
        std::unordered_map<std::string, InlineBinding> map;
        for (std::size_t i = 0; i < callee.ins.size(); ++i) {
            InlineBinding b;
            b.type = callee.ins[i].second;
            if (actuals[i].is_var) {
                b.actual = actuals[i].name;
            } else {
                b.is_const = true;
                b.literal = actuals[i].literal;
            }
            map.emplace(callee.ins[i].first, std::move(b));
        }
        for (std::size_t j = 0; j < callee.outs.size(); ++j) {
            InlineBinding b;
            b.type = callee.outs[j].second;
            b.actual = actuals[callee.ins.size() + j].name;
            map.emplace(callee.outs[j].first, std::move(b));
        }
        inline_maps_.push_back(std::move(map));
        const std::size_t caller_pos = pos_;
        pos_ = callee.body_begin;
        bool ok = true;
        while (pos_ < callee.body_end && tok().kind != Tok::END) {
            if (!instruction(diags)) { ok = false; break; }
        }
        if (ok && pos_ != callee.body_end) {
            diags.error(ErrorCode::E_INTERNAL,
                        "inline of '" + callee.name
                            + "' did not consume its body exactly", at());
            ok = false;
        }
        pos_ = caller_pos;
        inline_maps_.pop_back();
        return ok;
    }

    bool instruction(Uir::Diagnostics& diags) {
        if (tok().kind != Tok::IDENT) {
            diags.error(ErrorCode::E_PARSE, "expected an instruction, got '" + tok().text
                                                + "'", at());
            return false;
        }
        const std::string op = tok().text;
        const Uir::SourceLoc loc = at();
        eat();

        // **The explicit signedness variants are typing contracts, not new
        // instruction graphs.** `uadd`/`sadd` and friends share the graph of
        // the unprefixed instruction; the prefix fixes the interpretation by
        // hinting the destination at the unsigned/signed version of the first
        // operand's type, and the well-formedness rule that destination and
        // operands share one type (typecheck/std.ml: check_same_typ) then
        // forces the OPERANDS to carry that signedness already. `uadd v a b`
        // on a sint operand is ill-formed, not coerced (parsers/common.ml:
        // parse_uadd_at hints typ_to_unsigned; Fu et al., CCS 2019,
        // doi:10.1145/3319535.3354199: "uadd v a0 a1 expects v, a0, a1 to have
        // the same unsigned type"). Which signedness an instruction's safety
        // predicate and its algebraic lift take follows from the operand types,
        // so once the types are checked the encoding is the base one.
        std::optional<bool> forced;   // u* -> false (unsigned), s* -> true (signed)
        std::string base = op;
        if (op.size() > 1 && (op.front() == 'u' || op.front() == 's')) {
            static const std::unordered_set<std::string> kVariantBases = {
                "add", "adds", "adc", "adcs", "sub", "subs", "subc", "subb",
                "sbc", "sbcs", "sbb", "sbbs", "mul", "muls", "mull", "mulj",
                "split", "spl"};
            const std::string rest = op.substr(1);
            if (kVariantBases.count(rest) != 0) {
                forced = op.front() == 's';
                base = rest;
            }
        }

        auto finish = [&]() {
            if (isPunct(";")) { eat(); }
            return true;
        };

        // ---- the ghost layer ---------------------------------------------
        if (base == "assume") {
            // A hypothesis the proof may use: asserted as it stands.
            if (!instructionCondition(Role::ASSUME, diags)) { return false; }
            return finish();
        }
        if (base == "assert") {
            // An obligation at this prefix. It is not assumed afterwards, and
            // a later `assume` must not suppress a counterexample already found.
            if (!instructionCondition(Role::OBLIGATION, diags)) { return false; }
            return finish();
        }
        if (base == "eassert" || base == "rassert") {
            // `eassert`/`rassert` assert one side only (parsers:
            // EASSERT/RASSERT take an ebexp resp. rbexp clause list).
            std::vector<PredClause> parts;
            if (!conditionSide(base == "eassert", true, parts, diags)) {
                return false;
            }
            applyCondition(parts, Role::OBLIGATION, loc, diags);
            return !diags.hasErrors() && finish();
        }
        if (base == "cut" || base == "ecut" || base == "rcut") {
            // **A cut is a proof structure, and the chaining is the whole
            // point.** Each cut predicate is verified as an obligation of the
            // current fragment; then its side "starts afresh with the
            // predicate assumed" (doc/cryptoline.pdf) -- the next fragment's
            // ONLY precondition is the cut's predicates, and the earlier
            // instructions and assumes are not carried
            // (ast/cryptoline.ml: evisit_with_pwss/rvisit_with_pwss reset the
            // visited program and collect it into a per-cut specification).
            // `cut e && r` is one ecut e followed by one rcut r; ecut and rcut
            // are numbered separately, from 0, per side.
            std::vector<PredClause> parts;
            if (base == "ecut") {
                if (!conditionSide(true, true, parts, diags)) { return false; }
            } else if (base == "rcut") {
                if (!conditionSide(false, true, parts, diags)) { return false; }
            } else if (isIdent("true") && pos_ + 1 < toks_.size()
                       && toks_[pos_ + 1].kind == Tok::PUNCT
                       && (toks_[pos_ + 1].text == ";" || toks_[pos_ + 1].text == "}")) {
                // `cut true` cuts both sides with the trivial predicate.
                eat();
                parts.push_back(PredClause{H::mkBool(true, loc), true, {}});
                parts.push_back(PredClause{H::mkBool(true, loc), false, {}});
            } else if (!conditionParts(isPunct("{"), true, parts, diags)) {
                return false;
            }
            std::vector<PredClause> ecuts, rcuts;
            for (auto& p : parts) {
                (p.algebraic ? ecuts : rcuts).push_back(std::move(p));
            }
            if (!applyCut(ecuts, true, diags, loc)
                || !applyCut(rcuts, false, diags, loc)) {
                return false;
            }
            ++fragment_;
            return finish();
        }
        if (base == "ghost") {
            // **Ghost variables are logical constants that live only in
            // specifications, and their predicate is always ASSUMED**
            // (doc/cryptoline.pdf). The declaration checks are the official
            // ones: the names must be disjoint from the program variables and
            // from earlier ghosts (typecheck/std.ml: ghost_disjoint,
            // defined_ghost), and every conjunct of the predicate must
            // mention at least one of the NEW ghosts (parsers/common.ml:
            // parse_ghost_at -- otherwise the instruction is an assume that
            // introduces no logical variable).
            std::vector<std::pair<std::string, VarType>> gvars;
            for (;;) {
                if (isPunct("%")) { return vectorTypeRefused(diags); }
                std::string gname;
                VarType gty;
                if (!typedName(gname, gty, diags)) { return false; }
                if (ghosts_.count(gname) != 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "redefined ghost variable '" + gname + "'", loc);
                    return false;
                }
                if (version_.find(gname) != version_.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "ghost variable '" + gname
                                    + "' collides with a program variable; the layers "
                                      "stay apart (typecheck/std.ml: ghost_disjoint)",
                                loc);
                    return false;
                }
                gvars.emplace_back(gname, gty);
                if (isPunct(",")) { eat(); continue; }
                break;
            }
            if (!expect(":", diags)) { return false; }
            for (const auto& [gname, gty] : gvars) {
                ghosts_.insert(gname);   // before define(): ghosts are not
                define(gname, gty);      // "assigned in the body"
            }
            std::vector<PredClause> parts;
            if (!conditionParts(isPunct("{"), false, parts, diags)) { return false; }
            for (const PredClause& p : parts) {
                std::vector<H::ExprPtr> conjuncts;
                splitConjuncts(p.expr, conjuncts);
                for (const H::ExprPtr& conjunct : conjuncts) {
                    if (conjunct->kind == H::ExprKind::LIT_BOOL
                        && conjunct->bool_value) {
                        continue;
                    }
                    std::unordered_set<std::string> mentioned;
                    collectIdents(conjunct, mentioned);
                    bool mentions_ghost = false;
                    for (const auto& [gname, gty] : gvars) {
                        if (mentioned.count(gname) != 0) { mentions_ghost = true; }
                    }
                    if (!mentions_ghost) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a ghost predicate conjunct is defined without "
                                    "using any of the ghost variables it introduces "
                                    "(parsers/common.ml: parse_ghost_at)", loc);
                        return false;
                    }
                }
                // The predicate is always assumed, on its own side.
                (p.algebraic ? prefix_e_ : prefix_r_).push_back(p.expr);
                (p.algebraic ? ghosts_e_ : ghosts_r_).push_back(p.expr);
            }
            return finish();
        }
        if (base == "call" || base == "inline" || base == "inlinespec") {
            return callLike(base, diags, loc) && finish();
        }

        // ---- data movement and arithmetic --------------------------------
        if (op == "nondet") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            std::optional<VarType> type = dst.annotation;
            if (!type) {
                const std::string old = current(dst.name);
                if (!old.empty()) { type = types_.at(old); }
            }
            if (!type) {
                diags.error(ErrorCode::E_TYPE,
                            "a new nondeterministic destination must declare its type", loc);
                return false;
            }
            define(dst.name, *type); // deliberately unconstrained
            return finish();
        }
        if (op == "mov") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> src = atomValue(dst.annotation, diags);
            if (!src) { return false; }
            const std::optional<VarType> ty = exactDestinationType(dst, src->type, diags);
            if (!ty) { return false; }
            const std::string d = define(dst.name, *ty);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), src->value}, loc));
            return finish();
        }
        if (base == "add" || base == "sub" || base == "mul" || base == "and"
            || base == "or" || base == "xor" || base == "shl" || base == "shr"
            || base == "sar") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> a = atomValue(dst.annotation, diags);
            if (!a) { return false; }
            const std::optional<VarType> operand_type =
                variantType(forced, op, a->type, diags, loc);
            if (!operand_type) { return false; }
            const std::optional<AtomValue> b = atomValue(*operand_type, diags);
            if (!b) { return false; }
            static const std::unordered_map<std::string, H::Op> kMap = {
                {"add", H::Op::BV_ADD}, {"sub", H::Op::BV_SUB}, {"mul", H::Op::BV_MUL},
                {"and", H::Op::BV_AND}, {"or", H::Op::BV_OR},   {"xor", H::Op::BV_XOR},
                {"shl", H::Op::BV_SHL}, {"shr", H::Op::BV_LSHR},
                {"sar", H::Op::BV_ASHR},
            };
            if (base == "add") {
                addObligation(noOverflowAdd(a->value, b->value, *operand_type, loc));
            } else if (base == "sub") {
                addObligation(noOverflowSub(a->value, b->value, *operand_type, loc));
            } else if (base == "mul") {
                addObligation(noOverflowMul(a->value, b->value, *operand_type, loc));
            } else if (base == "shl" || base == "shr" || base == "sar") {
                addObligation(shiftSafety(base, a->value, b->value, *operand_type, loc));
            }
            const std::optional<VarType> ty = exactDestinationType(dst, *operand_type, diags);
            if (!ty) { return false; }
            const std::string d = define(dst.name, *ty);
            assertFormula(H::mkOp(H::Op::EQ,
                                  {ref(d), H::mkOp(kMap.at(base), {a->value, b->value}, loc)},
                                  loc));
            return finish();
        }
        if (op == "shls" || op == "shrs" || op == "sars") {
            Dest value_dest, lost_dest;
            if (op == "shls") {
                if (!destination(lost_dest, diags) || !destination(value_dest, diags)) {
                    return false;
                }
            } else if (!destination(value_dest, diags)
                       || !destination(lost_dest, diags)) {
                return false;
            }
            const std::optional<AtomValue> source = atomValue(value_dest.annotation, diags);
            if (!source) { return false; }
            unsigned amount = 0;
            if (!literalShiftAmount(source->type.width, amount, diags, loc)
                || amount == 0) {
                if (amount == 0 && !diags.hasErrors()) {
                    diags.error(ErrorCode::E_TYPE,
                                "a shift-output instruction cannot produce a zero-width "
                                "lost-bit destination", loc);
                }
                return false;
            }
            const std::optional<VarType> value_type =
                exactDestinationType(value_dest, source->type, diags);
            const VarType lost_inferred{
                amount, op == "shls" ? source->type.is_signed : false};
            const std::optional<VarType> lost_type =
                exactDestinationType(lost_dest, lost_inferred, diags);
            if (!value_type || !lost_type || value_dest.name == lost_dest.name) {
                if (value_dest.name == lost_dest.name) {
                    diags.error(ErrorCode::E_TYPE,
                                "value and lost-bit destinations must be different", loc);
                }
                return false;
            }
            const unsigned w = source->type.width;
            const H::ExprPtr shift = H::mkBitVec(binaryOf(std::to_string(amount), w), w,
                                                  loc);
            const H::Op shift_op = op == "shls" ? H::Op::BV_SHL
                                   : op == "shrs" ? H::Op::BV_LSHR
                                                  : H::Op::BV_ASHR;
            const H::ExprPtr value_expr =
                H::mkOp(shift_op, {source->value, shift}, loc);
            const H::ExprPtr lost_expr = op == "shls"
                                             ? H::mkBvExtract(source->value, w - 1,
                                                              w - amount, loc)
                                             : H::mkBvExtract(source->value, amount - 1,
                                                              0, loc);
            const std::string value = define(value_dest.name, *value_type);
            const std::string lost = define(lost_dest.name, *lost_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(value), value_expr}, loc));
            assertFormula(H::mkOp(H::Op::EQ, {ref(lost), lost_expr}, loc));
            return finish();
        }
        if (op == "cshl" || op == "cshls" || op == "cshr" || op == "cshrs") {
            const bool left = op == "cshl" || op == "cshls";
            const bool has_lost = op == "cshls" || op == "cshrs";
            Dest high_dest, low_dest, lost_dest;
            if (op == "cshls") {
                if (!destination(lost_dest, diags) || !destination(high_dest, diags)
                    || !destination(low_dest, diags)) {
                    return false;
                }
            } else {
                if (!destination(high_dest, diags) || !destination(low_dest, diags)) {
                    return false;
                }
                if (op == "cshrs" && !destination(lost_dest, diags)) { return false; }
            }
            const std::optional<AtomValue> high_source =
                atomValue(high_dest.annotation, diags);
            if (!high_source) { return false; }
            const unsigned w = high_source->type.width;
            const std::optional<AtomValue> low_source =
                atomValue(VarType{w, false}, diags);
            if (!low_source) { return false; }
            unsigned amount = 0;
            if (!literalShiftAmount(w, amount, diags, loc)) { return false; }
            if (has_lost && amount == 0) {
                diags.error(ErrorCode::E_TYPE,
                            "a combined shift-output instruction cannot produce a "
                            "zero-width lost-bit destination", loc);
                return false;
            }
            const std::optional<VarType> high_type =
                exactDestinationType(high_dest, high_source->type, diags);
            const std::optional<VarType> low_type =
                exactDestinationType(low_dest, VarType{w, false}, diags);
            std::optional<VarType> lost_type;
            if (has_lost) {
                lost_type = exactDestinationType(
                    lost_dest,
                    VarType{amount, left ? high_source->type.is_signed : false}, diags);
            }
            if (!high_type || !low_type || (has_lost && !lost_type)
                || high_dest.name == low_dest.name
                || (has_lost && (lost_dest.name == high_dest.name
                                 || lost_dest.name == low_dest.name))) {
                if (high_dest.name == low_dest.name
                    || (has_lost && (lost_dest.name == high_dest.name
                                     || lost_dest.name == low_dest.name))) {
                    diags.error(ErrorCode::E_TYPE,
                                "combined-shift destinations must be distinct", loc);
                }
                return false;
            }
            const H::ExprPtr amount_w = H::mkBitVec(
                binaryOf(std::to_string(amount), w), w, loc);
            H::ExprPtr high_expr;
            H::ExprPtr low_expr;
            H::ExprPtr lost_expr;
            if (left) {
                const H::ExprPtr joined = H::mkOp(
                    H::Op::BV_CONCAT, {high_source->value, low_source->value}, loc);
                const H::ExprPtr amount_2w = H::mkBitVec(
                    binaryOf(std::to_string(amount), 2 * w), 2 * w, loc);
                const H::ExprPtr shifted =
                    H::mkOp(H::Op::BV_SHL, {joined, amount_2w}, loc);
                high_expr = H::mkBvExtract(shifted, 2 * w - 1, w, loc);
                low_expr = H::mkOp(
                    H::Op::BV_LSHR,
                    {H::mkBvExtract(shifted, w - 1, 0, loc), amount_w}, loc);
                if (has_lost) {
                    lost_expr = H::mkBvExtract(high_source->value, w - 1,
                                               w - amount, loc);
                } else {
                    addObligation(shiftSafety("shl", high_source->value, amount_w,
                                              high_source->type, loc));
                }
            } else {
                high_expr = H::mkOp(H::Op::BV_LSHR,
                                    {high_source->value, amount_w}, loc);
                if (amount == 0) {
                    low_expr = low_source->value;
                } else {
                    low_expr = H::mkOp(
                        H::Op::BV_CONCAT,
                        {H::mkBvExtract(high_source->value, amount - 1, 0, loc),
                         H::mkBvExtract(low_source->value, w - 1, amount, loc)}, loc);
                }
                if (has_lost) {
                    lost_expr = H::mkBvExtract(low_source->value, amount - 1, 0, loc);
                } else if (amount != 0) {
                    H::ExprPtr safe = H::mkOp(
                        H::Op::EQ,
                        {H::mkBvExtract(low_source->value, amount - 1, 0, loc),
                         bvZero(amount, loc)}, loc);
                    if (high_source->type.is_signed) {
                        const H::ExprPtr sign = H::mkBvExtract(
                            high_source->value, w - 1, w - 1, loc);
                        safe = H::mkOp(
                            H::Op::AND,
                            {safe, H::mkOp(H::Op::EQ,
                                           {sign, H::mkBitVec("#b0", 1, loc)}, loc)},
                            loc);
                    }
                    addObligation(safe);
                }
            }
            const std::string high = define(high_dest.name, *high_type);
            const std::string low = define(low_dest.name, *low_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(high), high_expr}, loc));
            assertFormula(H::mkOp(H::Op::EQ, {ref(low), low_expr}, loc));
            if (has_lost) {
                const std::string lost = define(lost_dest.name, *lost_type);
                assertFormula(H::mkOp(H::Op::EQ, {ref(lost), lost_expr}, loc));
            }
            return finish();
        }
        if (op == "rol" || op == "ror") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> source = atomValue(dst.annotation, diags);
            if (!source) { return false; }
            const std::optional<AtomValue> amount = atomValue(source->type, diags);
            if (!amount) { return false; }
            const std::optional<VarType> result_type =
                exactDestinationType(dst, source->type, diags);
            if (!result_type) { return false; }
            const unsigned w = source->type.width;
            const H::ExprPtr width = H::mkBitVec(binaryOf(std::to_string(w), w), w, loc);
            const H::ExprPtr normalized =
                H::mkOp(H::Op::BV_UREM, {amount->value, width}, loc);
            const H::ExprPtr complement =
                H::mkOp(H::Op::BV_SUB, {width, normalized}, loc);
            const H::ExprPtr left = H::mkOp(
                H::Op::BV_SHL,
                {source->value, op == "rol" ? normalized : complement}, loc);
            const H::ExprPtr right = H::mkOp(
                H::Op::BV_LSHR,
                {source->value, op == "rol" ? complement : normalized}, loc);
            const H::ExprPtr rotated =
                H::mkOp(H::Op::BV_OR, {left, right}, loc);
            const std::string d = define(dst.name, *result_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), rotated}, loc));
            return finish();
        }
        if (op == "not") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> a = atomValue(dst.annotation, diags);
            if (!a) { return false; }
            const std::optional<VarType> ty = exactDestinationType(dst, a->type, diags);
            if (!ty) { return false; }
            const std::string d = define(dst.name, *ty);
            assertFormula(
                H::mkOp(H::Op::EQ,
                        {ref(d), H::mkOp(H::Op::BV_NOT, {a->value}, loc)}, loc));
            return finish();
        }
        if (base == "adds" || base == "subs" || base == "subc" || base == "subb") {
            // **The carry obligation.** `adds carry sum x y` produces the carry
            // as DATA the rest of the program reads. It is computed by doing the
            // arithmetic one bit wider and taking the top bit: dropping it would
            // leave `carry` declared and undefined, and the postcondition that
            // mentions it would then be trivially satisfiable.
            Dest carry_dest, sum_dest;
            if (!destination(carry_dest, diags) || !destination(sum_dest, diags)) {
                return false;
            }
            const std::optional<AtomValue> a = atomValue(sum_dest.annotation, diags);
            if (!a) { return false; }
            const std::optional<VarType> operand_type =
                variantType(forced, op, a->type, diags, loc);
            if (!operand_type) { return false; }
            const std::optional<AtomValue> b = atomValue(*operand_type, diags);
            if (!b) { return false; }
            const unsigned w = a->type.width;
            const std::optional<VarType> sum_type =
                exactDestinationType(sum_dest, *operand_type, diags);
            const std::optional<VarType> carry_type =
                exactDestinationType(carry_dest, VarType{1, false}, diags);
            if (!sum_type || !carry_type || carry_dest.name == sum_dest.name) {
                if (carry_dest.name == sum_dest.name) {
                    diags.error(ErrorCode::E_TYPE,
                                "carry and value destinations must be different", loc);
                }
                return false;
            }
            const H::ExprPtr za = H::mkBvExtend(H::Op::BV_ZERO_EXTEND, a->value, 1, loc);
            const H::ExprPtr zb = H::mkBvExtend(H::Op::BV_ZERO_EXTEND, b->value, 1, loc);
            H::ExprPtr wide;
            if (base == "adds") {
                wide = H::mkOp(H::Op::BV_ADD, {za, zb}, loc);
            } else if (base == "subs" || base == "subc") {
                // `subs` is the official alias of `subc`: c=1 means no borrow.
                const H::ExprPtr not_b = H::mkOp(H::Op::BV_NOT, {b->value}, loc);
                const H::ExprPtr znot_b =
                    H::mkBvExtend(H::Op::BV_ZERO_EXTEND, not_b, 1, loc);
                const H::ExprPtr one = H::mkBitVec(binaryOf("1", w + 1), w + 1, loc);
                wide = H::mkOp(H::Op::BV_ADD,
                               {H::mkOp(H::Op::BV_ADD, {za, znot_b}, loc), one}, loc);
            } else {
                // `subb` exposes the borrow bit: the high bit of unsigned
                // w+1 subtraction is one exactly when a < b.
                wide = H::mkOp(H::Op::BV_SUB, {za, zb}, loc);
            }
            const std::string s = define(sum_dest.name, *sum_type);
            const std::string c = define(carry_dest.name, *carry_type);
            assertFormula(H::mkOp(H::Op::EQ,
                                  {ref(s), H::mkBvExtract(wide, w - 1, 0, loc)}, loc));
            assertFormula(H::mkOp(H::Op::EQ,
                                  {ref(c), H::mkBvExtract(wide, w, w, loc)}, loc));
            return finish();
        }
        if (base == "adc" || base == "sbc" || base == "sbb") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> a = atomValue(dst.annotation, diags);
            if (!a) { return false; }
            const std::optional<VarType> operand_type =
                variantType(forced, op, a->type, diags, loc);
            if (!operand_type) { return false; }
            const std::optional<AtomValue> b = atomValue(*operand_type, diags);
            const std::optional<AtomValue> carry =
                atomValue(VarType{1, false}, diags);
            if (!b || !carry) { return false; }
            const std::optional<VarType> result_type =
                exactDestinationType(dst, *operand_type, diags);
            if (!result_type) { return false; }
            const H::ExprPtr carry_w = H::mkBvExtend(
                H::Op::BV_ZERO_EXTEND, carry->value, a->type.width - 1, loc);
            H::ExprPtr result;
            if (base == "adc") {
                const H::ExprPtr rhs =
                    H::mkOp(H::Op::BV_ADD, {b->value, carry_w}, loc);
                addObligation(H::mkOp(
                    H::Op::AND,
                    {noOverflowAdd(b->value, carry_w, a->type, loc),
                     noOverflowAdd(a->value, rhs, a->type, loc)}, loc));
                result = H::mkOp(
                    H::Op::BV_ADD,
                    {H::mkOp(H::Op::BV_ADD, {a->value, b->value}, loc), carry_w}, loc);
            } else if (base == "sbc") {
                const H::ExprPtr borrow = H::mkOp(
                    H::Op::BV_SUB, {bvOne(a->type.width, loc), carry_w}, loc);
                const H::ExprPtr rhs =
                    H::mkOp(H::Op::BV_ADD, {b->value, borrow}, loc);
                addObligation(H::mkOp(
                    H::Op::AND,
                    {noOverflowAdd(b->value, borrow, a->type, loc),
                     noOverflowSub(a->value, rhs, a->type, loc)}, loc));
                result = H::mkOp(
                    H::Op::BV_ADD,
                    {H::mkOp(H::Op::BV_ADD,
                             {a->value, H::mkOp(H::Op::BV_NOT, {b->value}, loc)}, loc),
                     carry_w}, loc);
            } else {
                const H::ExprPtr rhs =
                    H::mkOp(H::Op::BV_ADD, {b->value, carry_w}, loc);
                addObligation(H::mkOp(
                    H::Op::AND,
                    {noOverflowAdd(b->value, carry_w, a->type, loc),
                     noOverflowSub(a->value, rhs, a->type, loc)}, loc));
                result = H::mkOp(
                    H::Op::BV_SUB,
                    {a->value, rhs}, loc);
            }
            const std::string d = define(dst.name, *result_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), result}, loc));
            return finish();
        }
        if (base == "adcs" || base == "sbcs" || base == "sbbs") {
            Dest flag_dest, value_dest;
            if (!destination(flag_dest, diags) || !destination(value_dest, diags)) {
                return false;
            }
            const std::optional<AtomValue> a = atomValue(value_dest.annotation, diags);
            if (!a) { return false; }
            const std::optional<VarType> operand_type =
                variantType(forced, op, a->type, diags, loc);
            if (!operand_type) { return false; }
            const std::optional<AtomValue> b = atomValue(*operand_type, diags);
            const std::optional<AtomValue> carry =
                atomValue(VarType{1, false}, diags);
            if (!b || !carry) { return false; }
            const std::optional<VarType> value_type =
                exactDestinationType(value_dest, *operand_type, diags);
            const std::optional<VarType> flag_type =
                exactDestinationType(flag_dest, VarType{1, false}, diags);
            if (!value_type || !flag_type || flag_dest.name == value_dest.name) {
                if (flag_dest.name == value_dest.name) {
                    diags.error(ErrorCode::E_TYPE,
                                "flag and value destinations must be different", loc);
                }
                return false;
            }
            const unsigned w = a->type.width;
            const H::ExprPtr za = H::mkBvExtend(H::Op::BV_ZERO_EXTEND, a->value, 1, loc);
            const H::ExprPtr zb = H::mkBvExtend(H::Op::BV_ZERO_EXTEND, b->value, 1, loc);
            const H::ExprPtr carry_wide =
                H::mkBvExtend(H::Op::BV_ZERO_EXTEND, carry->value, w, loc);
            H::ExprPtr wide;
            if (base == "adcs") {
                wide = H::mkOp(
                    H::Op::BV_ADD,
                    {H::mkOp(H::Op::BV_ADD, {za, zb}, loc), carry_wide}, loc);
            } else if (base == "sbcs") {
                const H::ExprPtr znot_b = H::mkBvExtend(
                    H::Op::BV_ZERO_EXTEND,
                    H::mkOp(H::Op::BV_NOT, {b->value}, loc), 1, loc);
                wide = H::mkOp(
                    H::Op::BV_ADD,
                    {H::mkOp(H::Op::BV_ADD, {za, znot_b}, loc), carry_wide}, loc);
            } else {
                wide = H::mkOp(H::Op::BV_SUB,
                               {za, H::mkOp(H::Op::BV_ADD, {zb, carry_wide}, loc)}, loc);
            }
            const std::string value = define(value_dest.name, *value_type);
            const std::string flag = define(flag_dest.name, *flag_type);
            assertFormula(H::mkOp(
                H::Op::EQ, {ref(value), H::mkBvExtract(wide, w - 1, 0, loc)}, loc));
            assertFormula(H::mkOp(
                H::Op::EQ, {ref(flag), H::mkBvExtract(wide, w, w, loc)}, loc));
            return finish();
        }
        if (op == "cmov") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> condition =
                atomValue(VarType{1, false}, diags);
            const std::optional<AtomValue> when_true = atomValue(dst.annotation, diags);
            if (!condition || !when_true) { return false; }
            const std::optional<AtomValue> when_false = atomValue(when_true->type, diags);
            if (!when_false) { return false; }
            const std::optional<VarType> result_type =
                exactDestinationType(dst, when_true->type, diags);
            if (!result_type) { return false; }
            const H::ExprPtr one = H::mkBitVec("#b1", 1, loc);
            const H::ExprPtr is_one =
                H::mkOp(H::Op::EQ, {condition->value, one}, loc);
            const H::ExprPtr selected = H::mkOp(
                H::Op::ITE, {is_one, when_true->value, when_false->value}, loc);
            const std::string d = define(dst.name, *result_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), selected}, loc));
            return finish();
        }
        if (op == "seteq" || op == "setne") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            VarType result_type = dst.annotation.value_or(VarType{1, false});
            if (result_type.is_signed) {
                diags.error(ErrorCode::E_TYPE,
                            "seteq/setne destination must be unsigned", loc);
                return false;
            }
            const std::optional<AtomValue> a = atomValue(std::nullopt, diags);
            if (!a) { return false; }
            const std::optional<AtomValue> b = atomValue(a->type, diags);
            if (!b) { return false; }
            H::ExprPtr equal = H::mkOp(H::Op::EQ, {a->value, b->value}, loc);
            if (op == "setne") { equal = H::mkOp(H::Op::NOT, {equal}, loc); }
            const H::ExprPtr ones = H::mkBitVec(
                "#b" + std::string(result_type.width, '1'), result_type.width, loc);
            const H::ExprPtr zero =
                H::mkBitVec(binaryOf("0", result_type.width), result_type.width, loc);
            const H::ExprPtr result = H::mkOp(H::Op::ITE, {equal, ones, zero}, loc);
            const std::string d = define(dst.name, result_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), result}, loc));
            return finish();
        }
        if (base == "muls") {
            Dest flag_dest, value_dest;
            if (!destination(flag_dest, diags) || !destination(value_dest, diags)) {
                return false;
            }
            const std::optional<AtomValue> a = atomValue(value_dest.annotation, diags);
            if (!a) { return false; }
            const std::optional<VarType> operand_type =
                variantType(forced, op, a->type, diags, loc);
            if (!operand_type) { return false; }
            const std::optional<AtomValue> b = atomValue(*operand_type, diags);
            if (!b) { return false; }
            const std::optional<VarType> value_type =
                exactDestinationType(value_dest, *operand_type, diags);
            const std::optional<VarType> flag_type =
                exactDestinationType(flag_dest, VarType{1, false}, diags);
            if (!value_type || !flag_type || flag_dest.name == value_dest.name) {
                if (flag_dest.name == value_dest.name) {
                    diags.error(ErrorCode::E_TYPE,
                                "flag and value destinations must be different", loc);
                }
                return false;
            }
            const unsigned w = a->type.width;
            const H::Op extension = a->type.is_signed ? H::Op::BV_SIGN_EXTEND
                                                       : H::Op::BV_ZERO_EXTEND;
            const H::ExprPtr full = H::mkOp(
                H::Op::BV_MUL,
                {H::mkBvExtend(extension, a->value, w, loc),
                 H::mkBvExtend(extension, b->value, w, loc)}, loc);
            const H::ExprPtr low = H::mkBvExtract(full, w - 1, 0, loc);
            H::ExprPtr fits;
            if (a->type.is_signed) {
                fits = H::mkOp(H::Op::EQ,
                               {full, H::mkBvExtend(H::Op::BV_SIGN_EXTEND, low, w, loc)},
                               loc);
            } else {
                const H::ExprPtr high = H::mkBvExtract(full, 2 * w - 1, w, loc);
                fits = H::mkOp(
                    H::Op::EQ, {high, H::mkBitVec(binaryOf("0", w), w, loc)}, loc);
            }
            const H::ExprPtr flag_value = H::mkOp(
                H::Op::ITE,
                {fits, H::mkBitVec("#b0", 1, loc), H::mkBitVec("#b1", 1, loc)}, loc);
            const std::string value = define(value_dest.name, *value_type);
            const std::string flag = define(flag_dest.name, *flag_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(value), low}, loc));
            assertFormula(H::mkOp(H::Op::EQ, {ref(flag), flag_value}, loc));
            return finish();
        }
        if (base == "mull") {
            // The full double-width product as two registers. Same shape as the
            // carry: the high half is data, not an overflow flag to discard.
            Dest hi_dest, lo_dest;
            if (!destination(hi_dest, diags) || !destination(lo_dest, diags)) {
                return false;
            }
            const std::optional<AtomValue> a = atomValue(hi_dest.annotation, diags);
            if (!a) { return false; }
            const std::optional<VarType> operand_type =
                variantType(forced, op, a->type, diags, loc);
            if (!operand_type) { return false; }
            const std::optional<AtomValue> b = atomValue(*operand_type, diags);
            if (!b) { return false; }
            const unsigned w = a->type.width;
            const bool sgn = operand_type->is_signed;
            const std::optional<VarType> hi_type =
                exactDestinationType(hi_dest, *operand_type, diags);
            const std::optional<VarType> lo_type =
                exactDestinationType(lo_dest, VarType{w, false}, diags);
            if (!hi_type || !lo_type || hi_dest.name == lo_dest.name) {
                if (hi_dest.name == lo_dest.name) {
                    diags.error(ErrorCode::E_TYPE,
                                "high and low destinations must be different", loc);
                }
                return false;
            }
            const H::Op extend = sgn ? H::Op::BV_SIGN_EXTEND : H::Op::BV_ZERO_EXTEND;
            H::ExprPtr wide = H::mkOp(H::Op::BV_MUL,
                                      {H::mkBvExtend(extend, a->value, w, loc),
                                       H::mkBvExtend(extend, b->value, w, loc)}, loc);
            const std::string h = define(hi_dest.name, *hi_type);
            const std::string l = define(lo_dest.name, *lo_type);
            assertFormula(H::mkOp(H::Op::EQ,
                                  {ref(h), H::mkBvExtract(wide, 2 * w - 1, w, loc)}, loc));
            assertFormula(H::mkOp(H::Op::EQ,
                                  {ref(l), H::mkBvExtract(wide, w - 1, 0, loc)}, loc));
            return finish();
        }
        if (base == "mulj") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> a = atomValue(std::nullopt, diags);
            if (!a) { return false; }
            const std::optional<VarType> operand_type =
                variantType(forced, op, a->type, diags, loc);
            if (!operand_type) { return false; }
            const std::optional<AtomValue> b = atomValue(*operand_type, diags);
            if (!b) { return false; }
            const unsigned w = a->type.width;
            const VarType inferred{2 * w, operand_type->is_signed};
            const std::optional<VarType> result_type =
                exactDestinationType(dst, inferred, diags);
            if (!result_type) { return false; }
            const H::Op extension = a->type.is_signed ? H::Op::BV_SIGN_EXTEND
                                                       : H::Op::BV_ZERO_EXTEND;
            const H::ExprPtr full = H::mkOp(
                H::Op::BV_MUL,
                {H::mkBvExtend(extension, a->value, w, loc),
                 H::mkBvExtend(extension, b->value, w, loc)}, loc);
            const std::string d = define(dst.name, *result_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), full}, loc));
            return finish();
        }
        if (op == "join") {
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            const std::optional<AtomValue> high = atomValue(std::nullopt, diags);
            const std::optional<AtomValue> low = atomValue(std::nullopt, diags);
            if (!high || !low) { return false; }
            if (low->type.is_signed) {
                diags.error(ErrorCode::E_TYPE,
                            "the low operand of join must be unsigned", loc);
                return false;
            }
            const VarType inferred{high->type.width + low->type.width,
                                   high->type.is_signed};
            const std::optional<VarType> result_type =
                exactDestinationType(dst, inferred, diags);
            if (!result_type) { return false; }
            const H::ExprPtr joined =
                H::mkOp(H::Op::BV_CONCAT, {high->value, low->value}, loc);
            const std::string d = define(dst.name, *result_type);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), joined}, loc));
            return finish();
        }
        if (base == "split") {
            // **The split identity.** `split hi lo x n` redistributes one value
            // across two, and `x = hi * 2^n + lo` has to be ASSERTED. Declaring
            // hi and lo and moving on leaves them unconstrained, and every
            // postcondition about them then proves nothing. Asserted here as the
            // two extractions, which is the same statement and is exact.
            Dest hi_dest, lo_dest;
            if (!destination(hi_dest, diags) || !destination(lo_dest, diags)) {
                return false;
            }
            const std::optional<AtomValue> x = atomValue(hi_dest.annotation, diags);
            if (!x) { return false; }
            // usplit/ssplit fix the source's signedness (typecheck/std.ml:
            // check_same_typ ties the high destination to the source, and the
            // parser hints the destination at the forced sign).
            const std::optional<VarType> source_type =
                variantType(forced, op, x->type, diags, loc);
            if (!source_type) { return false; }
            const unsigned w = x->type.width;
            if (tok().kind != Tok::NUM) {
                diags.error(ErrorCode::E_PARSE, "'split' needs a literal bit position", loc);
                return false;
            }
            unsigned long long n = 0;
            const char* first = tok().text.data();
            std::from_chars(first, first + tok().text.size(), n);
            eat();
            if (n == 0 || n >= w) {
                diags.error(ErrorCode::E_PARSE,
                            "'split' at bit " + std::to_string(n) + " of a "
                                + std::to_string(w) + "-bit value leaves an empty half",
                            loc);
                return false;
            }
            const bool sgn = source_type->is_signed;
            const unsigned k = static_cast<unsigned>(n);
            // `split`, unlike `spl`, extends BOTH results back to the source
            // width. The high part follows source signedness; the low part is
            // always unsigned and zero-extended.
            const std::optional<VarType> hi_type =
                exactDestinationType(hi_dest, VarType{w, sgn}, diags);
            const std::optional<VarType> lo_type =
                exactDestinationType(lo_dest, VarType{w, false}, diags);
            if (!hi_type || !lo_type || hi_dest.name == lo_dest.name) {
                if (hi_dest.name == lo_dest.name) {
                    diags.error(ErrorCode::E_TYPE,
                                "high and low destinations must be different", loc);
                }
                return false;
            }
            const H::ExprPtr high = H::mkBvExtract(x->value, w - 1, k, loc);
            const H::ExprPtr low = H::mkBvExtract(x->value, k - 1, 0, loc);
            const H::ExprPtr extended_high = H::mkBvExtend(
                sgn ? H::Op::BV_SIGN_EXTEND : H::Op::BV_ZERO_EXTEND, high, k, loc);
            const H::ExprPtr extended_low =
                H::mkBvExtend(H::Op::BV_ZERO_EXTEND, low, w - k, loc);
            const std::string h = define(hi_dest.name, *hi_type);
            const std::string l = define(lo_dest.name, *lo_type);
            assertFormula(H::mkOp(H::Op::EQ,
                                  {ref(h), extended_high}, loc));
            assertFormula(H::mkOp(H::Op::EQ,
                                  {ref(l), extended_low}, loc));
            return finish();
        }
        if (base == "spl") {
            Dest hi_dest, lo_dest;
            if (!destination(hi_dest, diags) || !destination(lo_dest, diags)) {
                return false;
            }
            const std::optional<AtomValue> x = atomValue(std::nullopt, diags);
            if (!x) { return false; }
            const std::optional<VarType> source_type =
                variantType(forced, op, x->type, diags, loc);
            if (!source_type) { return false; }
            const unsigned w = x->type.width;
            if (tok().kind != Tok::NUM
                || tok().text.find_first_not_of("0123456789") != std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "'spl' needs a literal bit position", loc);
                return false;
            }
            unsigned long long n = 0;
            const char* first = tok().text.data();
            const char* last = first + tok().text.size();
            const auto parsed = std::from_chars(first, last, n);
            eat();
            if (parsed.ec != std::errc() || parsed.ptr != last || n == 0 || n >= w) {
                diags.error(ErrorCode::E_PARSE,
                            "'spl' bit position must be strictly inside the source width", loc);
                return false;
            }
            const unsigned k = static_cast<unsigned>(n);
            const std::optional<VarType> hi_type = exactDestinationType(
                hi_dest, VarType{w - k, source_type->is_signed}, diags);
            const std::optional<VarType> lo_type =
                exactDestinationType(lo_dest, VarType{k, false}, diags);
            if (!hi_type || !lo_type || hi_dest.name == lo_dest.name) {
                if (hi_dest.name == lo_dest.name) {
                    diags.error(ErrorCode::E_TYPE,
                                "high and low destinations must be different", loc);
                }
                return false;
            }
            const std::string h = define(hi_dest.name, *hi_type);
            const std::string l = define(lo_dest.name, *lo_type);
            assertFormula(H::mkOp(
                H::Op::EQ, {ref(h), H::mkBvExtract(x->value, w - 1, k, loc)}, loc));
            assertFormula(H::mkOp(
                H::Op::EQ, {ref(l), H::mkBvExtract(x->value, k - 1, 0, loc)}, loc));
            return finish();
        }
        if (op == "cast" || op == "vpc") {
            // `cast uint128 wide x`: a widening or narrowing whose direction and
            // sign-behaviour come from the DECLARED types, never from the value.
            Dest dst;
            std::optional<VarType> prefix_type;
            if (tok().kind == Tok::IDENT
                && (tok().text == "bit" || tok().text.rfind("uint", 0) == 0
                    || tok().text.rfind("sint", 0) == 0)) {
                VarType type;
                if (!typeName(type, diags)) { return false; }
                prefix_type = type;
            }
            if (!destination(dst, diags)) { return false; }
            if (prefix_type && dst.annotation && !sameType(*prefix_type, *dst.annotation)) {
                diags.error(ErrorCode::E_TYPE,
                            op + " destination has conflicting type annotations", loc);
                return false;
            }
            const std::optional<VarType> target = dst.annotation ? dst.annotation : prefix_type;
            if (!target) {
                diags.error(ErrorCode::E_TYPE,
                            op + " destination must carry its target type", loc);
                return false;
            }
            const std::optional<AtomValue> x = atomValue(std::nullopt, diags);
            if (!x) { return false; }
            const unsigned w = x->type.width;
            const bool src_signed = x->type.is_signed;
            H::ExprPtr converted;
            if (target->width == w) {
                converted = x->value;
            } else if (target->width > w) {
                converted = H::mkBvExtend(
                    src_signed ? H::Op::BV_SIGN_EXTEND : H::Op::BV_ZERO_EXTEND,
                    x->value, target->width - w, loc);
            } else {
                converted = H::mkBvExtract(x->value, target->width - 1, 0, loc);
            }
            if (op == "vpc") {
                // `vpc` has the same bit-vector assignment as `cast`, plus a
                // proof obligation that the signed/unsigned integer readings
                // selected by the declared source and target types agree.
                addObligation(H::mkOp(
                    H::Op::EQ,
                    {integerValue(converted, *target, loc),
                     integerValue(x->value, x->type, loc)}, loc));
            }
            const std::string d = define(dst.name, *target);
            assertFormula(H::mkOp(H::Op::EQ, {ref(d), converted}, loc));
            return finish();
        }

        if (base == "set" || base == "clear") {
            // `set x` is `mov x 1@bit` and `clear x` is `mov x 0@bit`
            // (parsers/common.ml: parse_set_at/parse_clear_at resolve the
            // destination as a carry, so an explicit annotation must be `bit`).
            Dest dst;
            if (!destination(dst, diags)) { return false; }
            if (dst.annotation
                && (dst.annotation->width != 1 || dst.annotation->is_signed)) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + op + "' defines a bit; the destination is annotated "
                                + std::string(dst.annotation->is_signed ? "sint" : "uint")
                                + std::to_string(dst.annotation->width), loc);
                return false;
            }
            const std::string d = define(dst.name, VarType{1, false});
            assertFormula(H::mkOp(
                H::Op::EQ,
                {ref(d), H::mkBitVec(base == "set" ? "#b1" : "#b0", 1, loc)}, loc));
            return finish();
        }
        if (base == "nop") { return finish(); }

        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "the instruction '" + op + "' is not implemented; skipping it would "
                    "leave its destination undefined and the verification vacuous", loc);
        return false;
    }

    std::vector<Tok> toks_;
    std::size_t pos_ = 0;
    std::string file_;
    Uir::TranslationReport* report_ = nullptr;
    /** Variables whose Int lift has been recorded, so the report carries one
     *  entry per declared name rather than one per occurrence. */
    std::unordered_set<std::string> lift_recorded_;
    /** Range division operators whose direct SMT-LIB mapping (and its
     *  total-at-zero behaviour) has been recorded once per parse. */
    std::unordered_set<std::string> div_recorded_;
    H::ConstraintModelPtr model_;
    std::vector<ObligationBranch> obligation_branches_;
    /** The per-side fragment prefixes: the algebraic half and the range half
     *  are verified as SEPARATE runs in the reference (verify/std.ml:
     *  verify_espec vs verify_rspec), and a cut starts each side afresh with
     *  that side's cut predicates. Instruction equations are pushed to both. */
    std::vector<H::ExprPtr> prefix_e_;
    std::vector<H::ExprPtr> prefix_r_;
    /** The procedure precondition's halves, for the `precondition` hint. */
    std::vector<H::ExprPtr> pre_e_;
    std::vector<H::ExprPtr> pre_r_;
    /** Per-side conjunctions of the cut instructions seen so far, numbered
     *  separately per side from 0 (doc/cryptoline.pdf) -- the facts the
     *  `cuts [i]` and `all cuts` hints select. */
    std::vector<H::ExprPtr> cuts_e_;
    std::vector<H::ExprPtr> cuts_r_;
    /** The assume (resp. ghost) predicates seen so far per side -- the facts
     *  the `all assumes` (resp. `all ghosts`) hints select. They accumulate
     *  ACROSS cuts (ast/cryptoline.ml: eprove_with_filter draws from every
     *  earlier fragment), unlike the fragment prefixes. */
    std::vector<H::ExprPtr> assumes_e_;
    std::vector<H::ExprPtr> assumes_r_;
    std::vector<H::ExprPtr> ghosts_e_;
    std::vector<H::ExprPtr> ghosts_r_;
    /** The current verification fragment: cut instructions delimit fragments
     *  in file order, and each obligation is tagged with the fragment it
     *  belongs to. check_index (the VMT/MoXI selector idiom) restricts the
     *  emitted query to one fragment. */
    std::size_t fragment_ = 0;
    std::optional<std::size_t> check_index_;
    /** Ghost variables declared in the current scope (doc/cryptoline.pdf:
     *  logical variables that must only be used in specifications). Ghosts
     *  are per-procedure -- the reference resets the ghost map at each proc
     *  (parsers/common.ml: parse_proc) -- so this set is part of the swapped
     *  scope. */
    std::unordered_set<std::string> ghosts_;
    /** The inline binding stack (formal -> actual), innermost last; nested
     *  inlines compose by walking from the back. */
    std::vector<std::unordered_map<std::string, InlineBinding>> inline_maps_;
    /** While a procedure body is being REGISTERED (validated in a scratch
     *  scope), its assigned variables are recorded here -- call/inlinespec
     *  need them for the nondet sets and the updated-formal-inputs check. */
    bool record_assigned_ = false;
    std::unordered_map<std::string, VarType> assigned_in_body_;
    /** The procedure table (name -> declaration) in file order, and the
     *  ordinal of the procedure whose body is being translated -- a call
     *  names an earlier procedure. */
    /** The procedure table (name -> declaration) in file order, and the
     *  ordinal of the procedure whose body is being translated -- a call
     *  names an earlier procedure. */
    std::unordered_map<std::string, ProcDecl> procs_;
    std::vector<std::string> procs_order_;
    std::size_t current_ordinal_ = 0;
    std::unordered_map<std::string, std::string> version_;   // source name -> SSA name
    std::unordered_map<std::string, unsigned>    counter_;    // source name -> version
    std::unordered_map<std::string, VarType>     types_;      // SSA name -> type
    unsigned eqmod_binder_ = 0;
    unsigned rng_width_ = 0;      // the width the current range half is written at

    /** The mutable per-procedure scope: registration of a non-entry procedure
     *  runs in a scratch scope (its constraints and declarations belong to
     *  the callers or to the contract, never to this translation directly),
     *  and the real scope is restored afterwards. */
    struct ScopeState {
        H::ConstraintModelPtr model;
        std::vector<ObligationBranch> obligation_branches;
        std::vector<H::ExprPtr> prefix_e, prefix_r, pre_e, pre_r, cuts_e, cuts_r,
            assumes_e, assumes_r, ghosts_e, ghosts_r;
        std::unordered_map<std::string, std::string> version;
        std::unordered_map<std::string, unsigned> counter;
        std::unordered_map<std::string, VarType> types;
        std::unordered_set<std::string> ghosts;
        std::vector<std::unordered_map<std::string, InlineBinding>> inline_maps;
        std::unordered_map<std::string, VarType> assigned_in_body;
        std::unordered_set<std::string> lift_recorded, div_recorded;
        bool record_assigned = false;
        std::size_t fragment = 0;
    };

    ScopeState saveScope() {
        ScopeState s;
        s.model = std::exchange(model_, std::make_shared<H::ConstraintModel>());
        s.obligation_branches = std::exchange(obligation_branches_, {});
        s.prefix_e = std::exchange(prefix_e_, {});
        s.prefix_r = std::exchange(prefix_r_, {});
        s.pre_e = std::exchange(pre_e_, {});
        s.pre_r = std::exchange(pre_r_, {});
        s.cuts_e = std::exchange(cuts_e_, {});
        s.cuts_r = std::exchange(cuts_r_, {});
        s.assumes_e = std::exchange(assumes_e_, {});
        s.assumes_r = std::exchange(assumes_r_, {});
        s.ghosts_e = std::exchange(ghosts_e_, {});
        s.ghosts_r = std::exchange(ghosts_r_, {});
        s.version = std::exchange(version_, {});
        s.counter = std::exchange(counter_, {});
        s.types = std::exchange(types_, {});
        s.ghosts = std::exchange(ghosts_, {});
        s.inline_maps = std::exchange(inline_maps_, {});
        s.assigned_in_body = std::exchange(assigned_in_body_, {});
        s.record_assigned = std::exchange(record_assigned_, false);
        s.lift_recorded = std::exchange(lift_recorded_, {});
        s.div_recorded = std::exchange(div_recorded_, {});
        s.fragment = std::exchange(fragment_, 0);
        return s;
    }

    void restoreScope(ScopeState s) {
        model_ = std::exchange(s.model, model_);
        obligation_branches_ = std::exchange(s.obligation_branches, obligation_branches_);
        prefix_e_ = std::exchange(s.prefix_e, prefix_e_);
        prefix_r_ = std::exchange(s.prefix_r, prefix_r_);
        pre_e_ = std::exchange(s.pre_e, pre_e_);
        pre_r_ = std::exchange(s.pre_r, pre_r_);
        cuts_e_ = std::exchange(s.cuts_e, cuts_e_);
        cuts_r_ = std::exchange(s.cuts_r, cuts_r_);
        assumes_e_ = std::exchange(s.assumes_e, assumes_e_);
        assumes_r_ = std::exchange(s.assumes_r, assumes_r_);
        ghosts_e_ = std::exchange(s.ghosts_e, ghosts_e_);
        ghosts_r_ = std::exchange(s.ghosts_r, ghosts_r_);
        version_ = std::exchange(s.version, version_);
        counter_ = std::exchange(s.counter, counter_);
        types_ = std::exchange(s.types, types_);
        ghosts_ = std::exchange(s.ghosts, ghosts_);
        inline_maps_ = std::exchange(s.inline_maps, inline_maps_);
        assigned_in_body_ = std::exchange(s.assigned_in_body, assigned_in_body_);
        record_assigned_ = std::exchange(s.record_assigned, record_assigned_);
        lift_recorded_ = std::exchange(s.lift_recorded, lift_recorded_);
        div_recorded_ = std::exchange(s.div_recorded, div_recorded_);
        fragment_ = std::exchange(s.fragment, fragment_);
    }
};

class CryptoLineLanguage : public Language {
public:
    CryptoLineLanguage() {
        // Semantic families, not token counts. The accepted scalar core has
        // reference-derived instruction graphs and safety obligations, the
        // explicit u*/s* signedness variants with set/clear/nop, the full
        // predicate-expression catalogue including range division, cut
        // fragmentation with prove-with fact selection, and procedures with
        // call/inline/inlinespec plus the ghost layer.
        coverage_.total = 15;
        coverage_.supported = 14;
        coverage_.missing = {
            "vector variable forms (`%v`, `uint64[4]`) -- an implementation "
            "extension outside the manual's grammar"};
    }

    std::string id() const override { return "cryptoline"; }
    std::string displayName() const override { return "CryptoLine"; }
    std::string version() const override { return "core"; }
    std::vector<std::string> extensions() const override { return {".cl"}; }
    const OpCoverage& coverage() const override { return coverage_; }

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
        // Without a selector the query aggregates every cut-delimited fragment
        // as "find any counterexample"; check_index=<n> restricts it to one
        // fragment (file order), which is how a harness gets an independent
        // verdict per fragment -- the VMT/MoXI idiom.
        std::optional<std::size_t> check_index;
        const auto check_it = opts.options.find("check_index");
        if (check_it != opts.options.end()) {
            for (const char c : check_it->second) {
                if (!std::isdigit(static_cast<unsigned char>(c))) {
                    out.diagnostics.error(
                        ErrorCode::E_PARSE,
                        "check_index must be a non-negative base-10 integer");
                    return out;
                }
            }
            errno = 0;
            char* end = nullptr;
            const unsigned long long value =
                std::strtoull(check_it->second.c_str(), &end, 10);
            if (check_it->second.empty() || errno == ERANGE || end == check_it->second.c_str()
                || *end != '\0') {
                out.diagnostics.error(ErrorCode::E_PARSE,
                                      "check_index must be a non-negative base-10 integer");
                return out;
            }
            check_index = static_cast<std::size_t>(value);
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            ClParser p(src, name, check_index);
            out.model = p.parse(out.diagnostics, out.report);
            if (out.model) {
                out.semantics.add(Uir::Sem::cryptoLineToRelationalContract(
                    *out.model, out.report.fidelity(), p.finalProjection()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("cryptoline frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkCryptoLineLanguage() { return std::make_shared<CryptoLineLanguage>(); }

} // namespace SOMTParser::Lang
