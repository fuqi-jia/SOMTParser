/* -*- Source -*-
 * Boogie frontend — the structured verification core.
 *
 * The format is docs/languages/boogie.md; its `implicit-constraints` block is
 * the specification this file implements, and each entry has a fixture in
 * languages/boogie/instances.
 *
 * Boogie is a verification-condition language: a file is a program plus its
 * contract, and the question is whether the contract holds. So the translation
 * is a VC generator, and the obligations are about what a VC must contain.
 *
 * **The one that governs everything: a contract is TWO-SIDED** (§2.3, §4.2).
 *
 *     clause       at the body        at each call site
 *     ---------    ---------------    -----------------
 *     requires     ASSUMED            ASSERTED
 *     ensures      ASSERTED           ASSUMED
 *
 * Doing one side and not the other is not a partial translation, it is a wrong
 * one, and it is wrong in a way that still produces a verdict. Assume a
 * `requires` at the body and forget to assert it at the call site, and a caller
 * may violate the contract with nothing failing. Assert an `ensures` at the
 * body and forget to assume it at the call site, and the caller must re-prove
 * what the callee guarantees -- reported as a verification failure in code that
 * is correct.
 *
 * **`havoc x` introduces a fresh variable** (§2.2). It is the language's
 * non-determinism primitive, and translating it as a no-op is a soundness error
 * with no symptom: the old value simply persists, so the VC proves a property
 * of a program that cannot happen.
 *
 * **A negated proof obligation is what makes the query a refutation.** The
 * procedure verifies exactly when every source-point counterexample branch is
 * unsatisfiable. Each branch contains the prefix in force at that obligation
 * and its negation; asserting an `ensures` positively would invert the answer.
 *
 * **Calls are the two-sided contract, not inlining** (§2.3, §4.2; This is
 * Boogie 2 §8.2/§9.9). At each call site the callee's checked `requires` are
 * asserted -- each its own refutation branch, so a violated precondition
 * reports sat -- the callee's checked `modifies` globals and the out-parameter
 * targets are havoc'd, every `ensures` (checked and free) is assumed with
 * actuals substituted for formals and `old()` resolved against the
 * call-entry versions, and a global outside the `modifies` clause keeps its
 * version, which is the frame. `free requires` are ignored by the caller and
 * `free ensures` are assumed but never asserted at the body; a `free call`
 * skips the precondition assertion. A call to a procedure whose `modifies`
 * exceeds the caller's own is a type error, exactly as the reference
 * implementation's CheckAssignments reports it.
 *
 * **`old` distributes to the leaves and is the identity on non-globals**
 * (This is Boogie 2 §4.3): `old(a + b + c)` with global a, local b and
 * out-parameter c is `old(a) + b + c`. Only a mutable global gets an entry
 * alias. A precondition may not use `old` at all (§8).
 *
 * **Branching is the two-edge join** (This is Boogie 2 §9.7): `if`/`else
 * if`/`else` and `if (*)` process each branch under its guard and join the
 * versions that disagree with an `ite` -- exact because the edges are
 * exclusive by construction. `return` obligatorifies the checked ensures at
 * every exit point, and code after a transfer is parsed and type-checked but
 * has no VC effect, matching the reference's pruning of unreachable blocks.
 *
 * **General control flow is the edge join at a label** (This is Boogie 2
 * §9.5): a syntactic pre-scan of the body splits each statement list into
 * segments at labels and transfer commands, classifies every `goto`
 * (forward: an edge into the target's join; backward: a loop header's back
 * edge), and computes each cycle's assigned variables. At a label, the
 * incoming edges join with fresh GATE booleans -- one per edge, each implying
 * its source's path condition -- because arbitrary goto edges are not
 * exclusive, so a plain ite over the guards could pick the wrong path's
 * value. A backward edge is CUT: the reference verifies a goto loop with an
 * implicit `invariant true` at the header (RemoveBackEdges.cs), which here is
 * the same havoc-and-continue as a no-invariant `while`. `break` (plain or
 * labeled) is a forward edge to the enclosing construct's join (§9.5's
 * desugaring), and an edge escaping a `while` body carries the head context
 * -- invariants and guard -- because the body's constraints leave the model
 * with the preservation check.
 *
 * What is refused, and why each is refused rather than approximated:
 *
 *   * **A `goto` into a structured statement's body, or a goto loop that
 *     crosses a `while` boundary.** The encoding joins control at construct
 *     boundaries; the while's checked-invariant encoding and a goto loop's
 *     implicit-true cut do not compose. Write the loop as one construct.
 *   * **Multi-index maps.** They are Boogie's heap encoding (§4.4), while the
 *     HIR array sort is single-index. Currying or tuple keys are semantic
 *     choices and are not made silently.
 *   * **`async call`.** Its semantics is a refinement question (the caller
 *     does not get the postcondition), not a contract instantiation.
 *   * **`where` clauses and procedure type parameters.** A `where` is a free
 *     pre/postcondition on a variable; dropping it admits states the source
 *     excludes.
 *     excludes.
 *
 * docs/languages/boogie.md §4.6 recommends routing Boogie through CHC rather
 * than to SMT directly, which would make the intermediate a checkable artefact.
 * That route now exists as the D7 CROSS-CHECK: the `chc` parse option emits
 * Horn clauses from this same parse (per-procedure summary relations, a
 * relation per program point, loop-head relations for inferred invariants,
 * the error! query), and test/python/test_boogie_chc_crosscheck.py asserts
 * verdict agreement between the two routes on the whole corpus. See
 * docs/open-questions-2026-08-13.md D7.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/boogie.h"

#include <algorithm>
#include <cctype>
#include <filesystem>
#include <fstream>
#include <limits>
#include <map>
#include <memory>
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

struct Token {
    enum Kind { IDENT, INT, PUNCT, STRING, END } kind = END;
    std::string text;
    int         line = 1;
    /** Offset of the token's first character -- the key the body pre-scan
     *  uses to name a statement list by its `{`. */
    std::size_t pos = 0;
};

/** Boogie's lexer. `//` line comments; the operators that matter are `:=`,
 *  `==`, `!=`, `<=`, `>=`, `&&`, `||`, `==>`. */
class Lexer {
public:
    Lexer(std::string src) : src_(std::move(src)) {}

    static bool isIdentifierStart(char c) {
        return std::isalpha(static_cast<unsigned char>(c))
            || std::string("'~#$^_.?`").find(c) != std::string::npos;
    }

    Token next() {
        skipTrivia();
        Token t;
        t.line = line_;
        t.pos = pos_;
        if (pos_ >= src_.size()) { t.kind = Token::END; return t; }
        const char c = src_[pos_];
        if (isIdentifierStart(c)) {
            const std::size_t s = pos_;
            while (pos_ < src_.size()
                   && (isIdentifierStart(src_[pos_])
                       || std::isdigit(static_cast<unsigned char>(src_[pos_])))) {
                advance();
            }
            t.kind = Token::IDENT;
            t.text = src_.substr(s, pos_ - s);
            return t;
        }
        if (c == '"') {
            // A string appears only inside an attribute (`{:captureState "..."}`)
            // and is never part of a term, but it must be LEXED: a `{` or `}`
            // inside one would otherwise be counted as a brace and throw the
            // attribute skipper's depth off.
            advance();
            const std::size_t s0 = pos_;
            while (pos_ < src_.size() && src_[pos_] != '"') {
                if (src_[pos_] == '\\' && pos_ + 1 < src_.size()) { advance(); }
                advance();
            }
            t.kind = Token::STRING;
            t.text = src_.substr(s0, pos_ - s0);
            if (pos_ < src_.size()) { advance(); }
            return t;
        }
        if (std::isdigit(static_cast<unsigned char>(c))) {
            const std::size_t s = pos_;
            while (pos_ < src_.size() && std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
                advance();
            }
            t.kind = Token::INT;
            t.text = src_.substr(s, pos_ - s);
            return t;
        }
        // Longest match first: `==>` before `==`, `==` before `=`.
        static const char* kMulti[] = {"==>", "<==>", ":=", "==", "!=", "<=", ">=",
                                       "&&", "||", "++", nullptr};
        for (int i = 0; kMulti[i] != nullptr; ++i) {
            const std::string m = kMulti[i];
            if (src_.compare(pos_, m.size(), m) == 0) {
                for (std::size_t k = 0; k < m.size(); ++k) { advance(); }
                t.kind = Token::PUNCT;
                t.text = m;
                return t;
            }
        }
        advance();
        t.kind = Token::PUNCT;
        t.text = std::string(1, c);
        return t;
    }

    /** Whether the next character after the token already taken is a `:`.
     *
     *  One character of lookahead, which is all two decisions need: `f(x: int)`
     *  against `f(int)`, and `{:attribute}` against a function's `{ body }`.
     *  Reading the character rather than buffering a token keeps the lexer's
     *  state the three scalars it is. */
    bool nextIsColon() {
        const std::size_t save_pos = pos_;
        const int save_line = line_;
        skipTrivia();
        const bool yes = pos_ < src_.size() && src_[pos_] == ':';
        pos_ = save_pos;
        line_ = save_line;
        return yes;
    }
    bool peekIsColon() { return nextIsColon(); }
    /** `:=` rather than a bare `:`, which is what separates an assignment from
     *  a label. */
    bool peekIsAssign() {
        const std::size_t save_pos = pos_;
        const int save_line = line_;
        skipTrivia();
        const bool yes = pos_ + 1 < src_.size() && src_[pos_] == ':' && src_[pos_ + 1] == '=';
        pos_ = save_pos;
        line_ = save_line;
        return yes;
    }
    bool peekIsColonAfterBrace() { return nextIsColon(); }

    /** Whether the parameter list starting here is `a, b: T` and not `T, T`.
     *
     *  `function f(int, int): int` and `function f(a, b: int): int` are both
     *  Boogie and cannot be told apart by one token: the difference is whether
     *  a `:` or the closing `)` comes first. So this scans ahead for the first
     *  of the two at parenthesis depth 0 -- arbitrary lookahead over raw
     *  characters, which costs nothing and needs no token buffer.
     *
     *  Commas are irrelevant to the decision and deliberately not consulted;
     *  the `:` is the only thing that makes a name a name. */
    bool namedGroupAhead() const {
        std::size_t p = pos_;
        int depth = 0;
        while (p < src_.size()) {
            const char c = src_[p];
            if (c == '(' || c == '[') { ++depth; }
            else if (c == ')' || c == ']') {
                if (depth == 0) { return false; }   // the list ended: bare types
                --depth;
            } else if (c == ':' && depth == 0) {
                return true;                        // `a, b: T`
            } else if (c == ';' || c == '{') {
                return false;                       // ran out of the list
            }
            ++p;
        }
        return false;
    }

    /** The whole lexer position, so the file can be walked twice -- Boogie
     *  declarations are not ordered and pass 1 must see all of them. */
    struct State {
        std::size_t pos = 0;
        int         line = 1;
    };
    State state() const { return {pos_, line_}; }
    void setState(const State& s) { pos_ = s.pos; line_ = s.line; }

private:
    void advance() {
        if (src_[pos_] == '\n') { ++line_; }
        ++pos_;
    }
    void skipTrivia() {
        while (pos_ < src_.size()) {
            const char c = src_[pos_];
            if (c == '/' && pos_ + 1 < src_.size() && src_[pos_ + 1] == '/') {
                while (pos_ < src_.size() && src_[pos_] != '\n') { advance(); }
            } else if (c == '/' && pos_ + 1 < src_.size() && src_[pos_ + 1] == '*') {
                // Boogie has both comment syntaxes, and this lexer knew only
                // `//` -- the same shape as MiniZinc's missing `/* */`, which
                // made sixteen upstream files fail at line 1 column 1.
                advance();
                advance();
                while (pos_ + 1 < src_.size()
                       && !(src_[pos_] == '*' && src_[pos_ + 1] == '/')) {
                    advance();
                }
                if (pos_ + 1 < src_.size()) { advance(); advance(); }
                else { pos_ = src_.size(); }
            } else if (std::isspace(static_cast<unsigned char>(c))) {
                advance();
            } else {
                return;
            }
        }
    }

    std::string src_;
    std::size_t pos_ = 0;
    int         line_ = 1;
};

class BoogieParser {
public:
    BoogieParser(std::string src, std::string file)
        : lex_(std::move(src)), file_(std::move(file)) {
        tok_ = lex_.next();
    }

    /** D7's Horn route: emit constrained Horn clauses from the same parse
     *  instead of the formula VC (boogie.md §4.6). */
    void setChcMode(bool on) { chc_mode_ = on; }

    /** Explicit /doModSetAnalysis-style preprocessing, never the default. */
    void setInferModifies(bool on) { infer_modifies_ = on; }

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        report_ = &report;
        model_ = std::make_shared<H::ConstraintModel>();

        // ---- Pass 1: declarations only. ------------------------------------
        //
        // **Boogie declarations are not ordered.** TuringFactorial.bpl uses
        // `Factorial(n)` in a postcondition on line 9 and declares the function
        // on line 31, which is a perfectly legal Boogie program that this
        // frontend rejected as "'Factorial' is not declared" -- a legal input
        // refused, not a construct declined.
        //
        // So declarations are collected first and procedure bodies are skipped;
        // pass 2 skips the declarations it already has and does the real work.
        // One rewind, using the same lexer mark the whole file is parsed from.
        const Mark start = mark();
        // Type declarations are unordered too. Resolve nominal types and
        // non-parameterized aliases before reading variable/function signatures.
        if (!collectNamedTypes(diags)) { return nullptr; }
        reset(start);
        decl_pass_ = true;
        while (tok_.kind != Token::END) {
            if (is("var")) {
                if (!globalDecl(diags)) { return nullptr; }
            } else if (is("const")) {
                if (!constDecl(diags)) { return nullptr; }
            } else if (is("function")) {
                if (!functionDecl(diags)) { return nullptr; }
            } else if (is("type")) {
                skipItem(); // registered and checked by collectNamedTypes
            } else if (is("axiom") || is("implementation")) {
                if (infer_modifies_ && is("implementation")) {
                    inference_implementations_.push_back(mark());
                }
                skipItem();
            } else if (is("procedure")) {
                if (!procedureSignature(diags)) { return nullptr; }
            } else {
                diags.error(ErrorCode::E_PARSE, "unexpected '" + tok_.text + "'", loc());
                return nullptr;
            }
        }

        // Infer frames only after all signatures and globals are available,
        // and before any body or call is encoded against those frames.
        if (infer_modifies_ && !inferProcedureModifies(diags)) { return nullptr; }

        // Definitions may call later functions, just as contracts may. Replay
        // bodies only after every signature (and every mutable global) exists.
        for (const auto& definition : pending_functions_) {
            reset(definition.body);
            if (!readFunctionBody(definition, diags)) { return nullptr; }
        }

        // Every declaration now exists, so the recorded `uses` blocks can be
        // read -- including the forward references that made them wait.
        // Indexed rather than range-for: nothing appends to pending_uses_ here
        // -- readUsesBody does not record -- but the vector is the loop's own
        // input and an index says so.
        for (std::size_t i = 0; i < pending_uses_.size(); ++i) {
            reset(pending_uses_[i]);
            if (!readUsesBody(diags)) { return nullptr; }
        }
        global_sorts_ = sorts_;

        // ---- Pass 2: axioms and procedures. --------------------------------
        reset(start);
        decl_pass_ = false;
        if (chc_mode_) {
            // The Horn route (§4.6): axioms first -- they fold into every
            // clause's body -- then each procedure as its clause set. The
            // refutation query is not one constraint here: the query is the
            // error! relation, asked by the Horn solver.
            while (tok_.kind != Token::END) {
                if (is("axiom")) {
                    if (!axiom(diags)) { return nullptr; }
                } else {
                    skipItem();
                }
            }
            reset(start);
            while (tok_.kind != Token::END) {
                if (is("procedure") || is("implementation")) {
                    if (!chcProcedure(diags)) { return nullptr; }
                } else {
                    skipItem();
                }
            }
            if (!saw_procedure_) {
                diags.error(ErrorCode::E_PARSE,
                            "no procedure with a body: there is nothing to verify",
                            loc());
                return nullptr;
            }
            // The CHC-COMP query clause, final: one false-headed,
            // universally quantified clause whose antecedent is the error!
            // relation. (The conjunct b exists because the format requires a
            // quantified variable.)
            chcRel("error!", {});
            {
                H::Binder q;
                q.name = "q!query";
                q.sort = H::Sort::boolean();
                H::ExprPtr err = chcError();
                H::Constraint qc;
                qc.loc = loc();
                qc.formula = H::mkForall(
                    {q},
                    H::mkOp(H::Op::IMPLIES,
                            {H::mkOp(H::Op::AND,
                                     {err, H::mkBoundVar(q.name, q.sort)}),
                             H::mkBool(false, loc())}));
                model_->constraints.push_back(std::move(qc));
            }
            Uir::EncodingChoice ch;
            ch.site       = file_;
            ch.unified_op = "chc";
            ch.strategy   = "horn-clause-summary-relations";
            ch.fidelity   = Uir::Fidelity::exact();
            ch.rationale =
                "D7's cross-check route: the same parse emits constrained Horn "
                "clauses -- per-procedure summary relations conjoining the "
                "ensures, per-loop-head relations so invariants are inferred, the "
                "error! relation as the query; checked invariants are error "
                "clauses here (never assumed), so a program whose given "
                "invariant is not inductive may still verify on this route; the "
                "corpus keeps them inductive so the routes ask the same "
                "question";
            report_->addChoice(std::move(ch));
            return model_;
        }
        while (tok_.kind != Token::END) {
            if (is("axiom")) {
                if (!axiom(diags)) { return nullptr; }
            } else if (is("procedure") || is("implementation")) {
                if (!procedure(diags)) { return nullptr; }
            } else if (is("var") || is("const") || is("function") || is("type")) {
                skipItem();                       // already registered in pass 1
            } else {
                diags.error(ErrorCode::E_PARSE, "unexpected '" + tok_.text + "'", loc());
                return nullptr;
            }
        }
        if (!saw_procedure_) {
            diags.error(ErrorCode::E_PARSE,
                        "no procedure with a body: there is nothing to verify", loc());
            return nullptr;
        }
        H::ExprPtr any_counterexample = procedure_refutations_.front();
        for (std::size_t i = 1; i < procedure_refutations_.size(); ++i) {
            any_counterexample = H::mkOp(
                H::Op::OR, {any_counterexample, procedure_refutations_[i]});
        }
        H::Constraint query;
        query.formula = std::move(any_counterexample);
        model_->constraints.push_back(std::move(query));
        return model_;
    }

private:
    /** The whole parser position, so a formula can be re-read later against a
     *  different SSA version map -- a loop invariant is a statement about
     *  three states, and a contract clause is a statement about every call
     *  site. */
    struct Mark {
        Lexer::State state;
        Token        tok;
    };
    Mark mark() const { return {lex_.state(), tok_}; }
    void reset(const Mark& m) { lex_.setState(m.state); tok_ = m.tok; }

    struct FunctionBody {
        std::string name;
        std::vector<H::Sort> params;
        std::vector<std::string> param_names;
        H::Sort result;
        Uir::SourceLoc at;
        Mark body;
    };
    struct BuiltinFunction {
        std::string attribute;
        std::string name;
        std::vector<unsigned> indices;
        H::Op op = H::Op::EQ;
        bool remainder = false;
        H::Sort result;
        std::string pointwise_symbol;
    };

    /** A contract clause recorded in pass 1 to be re-read at each use. */
    struct ProcContract {
        Mark mark;
        bool free_clause = false;
    };
    /** A procedure's signature and contract, collected in pass 1 so a call
     *  above the callee's declaration still sees the whole interface. */
    struct ProcSig {
        Mark contract_start;
        std::vector<std::string> in_names;
        std::vector<H::Sort>     in_sorts;
        std::vector<std::string> out_names;
        std::vector<H::Sort>     out_sorts;
        std::vector<ProcContract> requires;
        std::vector<ProcContract> ensures;
        std::unordered_set<std::string> modifies_checked;
        std::unordered_set<std::string> modifies_free;
    };

    /** A control-flow edge into a join point (a label, an if's Done, a
     *  loop's continuation): the path condition in force at the source and
     *  the version map there. */
    struct PendingEdge {
        H::ExprPtr guard;    // null means "true"
        std::unordered_map<std::string, unsigned> versions;
    };

    /** What the body pre-scan learns about one statement list. The scan is
     *  SYNTACTIC: it walks the token stream, splits each list into segments
     *  at its labels and transfer commands, and computes -- for a backward
     *  goto's target -- the variables the cycle assigns, which the reference
     *  havocs under an implicit `invariant true` (RemoveBackEdges.cs). */
    struct LabelScan {
        /** label -> token position, for forward/backward classification. */
        std::unordered_map<std::string, std::size_t> label_pos;
        /** header label -> variables assigned in the cycle(s) through it. */
        std::unordered_map<std::string, std::vector<std::string>> header_havoc;
        /** label -> the leading run of assert expressions after it (as marks).
         *  At a loop header those ARE the invariants: RemoveBackEdges.cs turns
         *  the header block's assert prefix into the loop's invariant set. */
        std::unordered_map<std::string, std::vector<Mark>> label_asserts;
    };
    struct BodyScan {
        /** list id (the `{` token's position) -> scan. */
        std::map<std::size_t, LabelScan> lists;
        /** label -> owning list id. Labels are distinct per body (This is
         *  Boogie 2 §9.5), so this is a function. */
        std::unordered_map<std::string, std::size_t> label_list;
    };

    /** A statement list being processed: its labels' incoming edges and
     *  whether it is a `while` body (whose constraints leave the model, so
     *  an escaping edge must carry them as an expression). */
    struct ListFrame {
        std::size_t list_id = 0;
        const LabelScan* scan = nullptr;
        std::unordered_map<std::string, std::vector<PendingEdge>> edges;
        bool in_while_body = false;
    };

    /** A `break` target: the innermost enclosing while (unnamed entry) or an
     *  enclosing labeled `while`/`if`. */
    struct Breakable {
        std::string label;                  // "" for the innermost-while entry
        bool is_while = false;            // plain `break` skips if-entries
        std::vector<PendingEdge>* collector;
    };
    /** The Horn route's break target: an exit relation plus the break points'
     *  relations, which become clauses into it. */
    struct ChcBreakable {
        std::string label;
        bool is_while = false;
        std::string exit_rel;
        std::vector<std::string> pending;
    };

    Uir::SourceLoc loc() const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = tok_.line;
        return l;
    }
    bool is(const std::string& t) const { return tok_.kind == Token::IDENT && tok_.text == t; }
    bool isP(const std::string& t) const { return tok_.kind == Token::PUNCT && tok_.text == t; }
    void eat() { tok_ = lex_.next(); }
    bool expectP(const std::string& t, Uir::Diagnostics& d) {
        if (!isP(t)) {
            d.error(ErrorCode::E_PARSE, "expected '" + t + "', found '" + tok_.text + "'",
                    loc());
            return false;
        }
        eat();
        return true;
    }

    static bool unsignedDecimal(const std::string& text, unsigned& value) {
        if (text.empty()) { return false; }
        value = 0;
        for (const char c : text) {
            if (c < '0' || c > '9') { return false; }
            const unsigned digit = static_cast<unsigned>(c - '0');
            if (value > (std::numeric_limits<unsigned>::max() - digit) / 10) { return false; }
            value = value * 10 + digit;
        }
        return true;
    }

    // Decimal division avoids host-integer overflow and never silently wraps a
    // source literal. Work depends on the literal length, not 2^width.
    static bool fitsBitVector(std::string value, unsigned width) {
        unsigned bits = 0;
        while (value.find_first_not_of('0') != std::string::npos) {
            if (bits == width) { return false; }
            ++bits;
            unsigned carry = 0;
            for (char& c : value) {
                const unsigned digit = carry * 10 + static_cast<unsigned>(c - '0');
                c = static_cast<char>('0' + digit / 2);
                carry = digit % 2;
            }
        }
        return true;
    }

    bool functionAttributes(BuiltinFunction& builtin, Uir::Diagnostics& d) {
        while (isP("{") && lex_.peekIsColonAfterBrace()) {
            eat();
            if (!expectP(":", d)) { return false; }
            if (is("builtin") || is("bvbuiltin")) {
                if (!builtin.attribute.empty()) {
                    d.error(ErrorCode::E_TYPE, "duplicate semantic function attribute", loc());
                    return false;
                }
                builtin.attribute = tok_.text;
                eat();
                if (tok_.kind != Token::STRING) {
                    d.error(ErrorCode::E_PARSE, "builtin attribute requires one operator string", loc());
                    return false;
                }
                builtin.name = tok_.text;
                eat();
                if (!expectP("}", d)) { return false; }
            } else {
                int depth = 1;
                while (depth > 0) {
                    if (tok_.kind == Token::END) {
                        d.error(ErrorCode::E_PARSE, "unterminated function attribute", loc());
                        return false;
                    }
                    if (isP("{")) { ++depth; }
                    else if (isP("}")) { --depth; }
                    eat();
                }
            }
        }
        return true;
    }

    bool validateBuiltin(BuiltinFunction& builtin, const std::vector<H::Sort>& params,
                           const H::Sort& result, const Uir::SourceLoc& at,
                           Uir::Diagnostics& d) {
        const auto invalid = [&]() {
            d.error(ErrorCode::E_TYPE,
                    "invalid signature or indices for builtin '" + builtin.name + "'", at);
            return false;
        };
        // Indexed operators must have exactly the SMT spelling `(_ op n ...)`.
        if (!builtin.name.empty() && builtin.name.front() == '(') {
            Lexer tokens(builtin.name);
            const auto open = tokens.next();
            const auto underscore = tokens.next();
            const auto operation = tokens.next();
            if (open.text != "(" || underscore.text != "_" || operation.kind != Token::IDENT) {
                return invalid();
            }
            Token token = tokens.next();
            while (token.kind == Token::INT) {
                unsigned index = 0;
                if (!unsignedDecimal(token.text, index)) { return invalid(); }
                builtin.indices.push_back(index);
                token = tokens.next();
            }
            if (token.kind != Token::PUNCT || token.text != ")"
                || tokens.next().kind != Token::END || builtin.indices.empty()) {
                return invalid();
            }
            builtin.name = operation.text;
        }
        const auto all = [&](H::SortKind kind, std::size_t arity) {
            return params.size() == arity
                && std::all_of(params.begin(), params.end(),
                               [&](const H::Sort& sort) { return sort.kind == kind; });
        };
        const auto same_bv = [&](std::size_t arity) {
            return all(H::SortKind::BITVEC, arity)
                && std::all_of(params.begin(), params.end(),
                               [&](const H::Sort& sort) { return H::sameSort(sort, params[0]); });
        };
        const auto& name = builtin.name;
        if (name == "int2bv") {
            builtin.op = H::Op::INT_TO_BV;
            return builtin.indices.size() == 1 && builtin.indices[0] > 0
                && all(H::SortKind::INT, 1) && result.kind == H::SortKind::BITVEC
                && result.width == builtin.indices[0] ? true : invalid();
        }
        if (name == "zero_extend" || name == "sign_extend") {
            builtin.op = name == "zero_extend" ? H::Op::BV_ZERO_EXTEND : H::Op::BV_SIGN_EXTEND;
            if (builtin.indices.size() != 1 || !all(H::SortKind::BITVEC, 1)
                || builtin.indices[0] > std::numeric_limits<unsigned>::max() - params[0].width) {
                return invalid();
            }
            return result.kind == H::SortKind::BITVEC
                && result.width == params[0].width + builtin.indices[0] ? true : invalid();
        }
        if (name == "extract") {
            builtin.op = H::Op::BV_EXTRACT;
            if (builtin.indices.size() != 2 || !all(H::SortKind::BITVEC, 1)
                || builtin.indices[0] < builtin.indices[1]
                || builtin.indices[0] >= params[0].width) { return invalid(); }
            return result.kind == H::SortKind::BITVEC
                && result.width == builtin.indices[0] - builtin.indices[1] + 1 ? true : invalid();
        }
        if (!builtin.indices.empty()) { return invalid(); }
        if (name == "MapConst") {
            builtin.result = result;
            return builtin.attribute == "builtin" && params.size() == 1
                && result.kind == H::SortKind::ARRAY && result.index && result.elem
                && H::sameSort(params[0], *result.elem) ? true : invalid();
        }
        if (name == "MapImp") {
            builtin.result = result;
            return builtin.attribute == "builtin" && params.size() == 2
                && result.kind == H::SortKind::ARRAY && result.index && result.elem
                && result.elem->kind == H::SortKind::BOOL
                && H::sameSort(params[0], result) && H::sameSort(params[1], result)
                ? true : invalid();
        }
        if (name == "bv2int" || name == "bv2nat" || name == "ubv_to_int") {
            // Z3's legacy name `bv2int` denotes the UNSIGNED conversion.
            // HIR's BV_TO_INT is signed and would change high-bit values.
            builtin.op = H::Op::BV_TO_NAT;
            return all(H::SortKind::BITVEC, 1) && result.kind == H::SortKind::INT
                ? true : invalid();
        }
        if (name == "sbv_to_int") {
            builtin.op = H::Op::BV_TO_INT;
            return all(H::SortKind::BITVEC, 1) && result.kind == H::SortKind::INT
                ? true : invalid();
        }
        if (name == "div" || name == "mod" || name == "rem") {
            builtin.op = name == "div" ? H::Op::DIV_EUCLID : H::Op::MOD_EUCLID;
            builtin.remainder = name == "rem";
            return all(H::SortKind::INT, 2) && result.kind == H::SortKind::INT
                ? true : invalid();
        }
        if (name == "concat") {
            builtin.op = H::Op::BV_CONCAT;
            if (!all(H::SortKind::BITVEC, 2)
                || params[0].width > std::numeric_limits<unsigned>::max() - params[1].width) {
                return invalid();
            }
            return result.kind == H::SortKind::BITVEC
                && result.width == params[0].width + params[1].width ? true : invalid();
        }
        static const std::unordered_map<std::string, H::Op> unary = {
            {"bvnot", H::Op::BV_NOT}, {"bvneg", H::Op::BV_NEG}
        };
        static const std::unordered_map<std::string, H::Op> binary = {
            {"bvadd", H::Op::BV_ADD}, {"bvsub", H::Op::BV_SUB}, {"bvmul", H::Op::BV_MUL},
            {"bvudiv", H::Op::BV_UDIV}, {"bvurem", H::Op::BV_UREM},
            {"bvsdiv", H::Op::BV_SDIV}, {"bvsrem", H::Op::BV_SREM}, {"bvsmod", H::Op::BV_SMOD},
            {"bvand", H::Op::BV_AND}, {"bvor", H::Op::BV_OR}, {"bvxor", H::Op::BV_XOR},
            {"bvnand", H::Op::BV_NAND}, {"bvnor", H::Op::BV_NOR}, {"bvxnor", H::Op::BV_XNOR},
            {"bvshl", H::Op::BV_SHL}, {"bvlshr", H::Op::BV_LSHR}, {"bvashr", H::Op::BV_ASHR}
        };
        static const std::unordered_map<std::string, H::Op> predicates = {
            {"bvult", H::Op::BV_ULT}, {"bvule", H::Op::BV_ULE},
            {"bvugt", H::Op::BV_UGT}, {"bvuge", H::Op::BV_UGE},
            {"bvslt", H::Op::BV_SLT}, {"bvsle", H::Op::BV_SLE},
            {"bvsgt", H::Op::BV_SGT}, {"bvsge", H::Op::BV_SGE}
        };
        if (const auto found = unary.find(name); found != unary.end()) {
            builtin.op = found->second;
            return same_bv(1) && H::sameSort(result, params[0]) ? true : invalid();
        }
        if (const auto found = binary.find(name); found != binary.end()) {
            builtin.op = found->second;
            return same_bv(2) && H::sameSort(result, params[0]) ? true : invalid();
        }
        if (const auto found = predicates.find(name); found != predicates.end()) {
            builtin.op = found->second;
            return same_bv(2) && result.kind == H::SortKind::BOOL ? true : invalid();
        }
        d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "semantic function attribute '" + builtin.attribute + "' names unsupported builtin '"
                    + name + "'; it cannot be replaced by an uninterpreted function", at);
        return false;
    }

    H::ExprPtr applyBuiltin(const BuiltinFunction& builtin, const std::vector<H::ExprPtr>& args,
                            const Uir::SourceLoc& at) {
        if (builtin.name == "MapConst") {
            return H::mkConstArray(builtin.result, args[0], at);
        }
        if (builtin.name == "MapImp") {
            if (builtin.result.index->kind == H::SortKind::BOOL) {
                // Bool has exactly two indices. A constant array plus one store
                // defines the complete result without a quantified array axiom.
                // This also preserves calls beneath binders and whole-array equality.
                const auto implicationAt = [&](bool value) {
                    const auto index = H::mkBool(value, at);
                    return H::mkOp(H::Op::IMPLIES,
                        {H::mkOp(H::Op::SELECT, {args[0], index}, at),
                         H::mkOp(H::Op::SELECT, {args[1], index}, at)}, at);
                };
                return H::mkOp(H::Op::STORE,
                    {H::mkConstArray(builtin.result, implicationAt(false), at),
                     H::mkBool(true, at), implicationAt(true)}, at);
            }
            return H::mkApply(builtin.pointwise_symbol, builtin.result, args, at);
        }
        if (builtin.op == H::Op::INT_TO_BV) {
            return H::mkIntToBv(args[0], builtin.indices[0], at);
        }
        if (builtin.op == H::Op::BV_ZERO_EXTEND || builtin.op == H::Op::BV_SIGN_EXTEND) {
            return H::mkBvExtend(builtin.op, args[0], builtin.indices[0], at);
        }
        if (builtin.op == H::Op::BV_EXTRACT) {
            return H::mkBvExtract(args[0], builtin.indices[0], builtin.indices[1], at);
        }
        if (builtin.remainder) {
            // Z3 rem(a,b) = ite(b >= 0, mod(a,b), -mod(a,b)), including
            // its totalized zero-divisor branch. It is NOT truncating rem.
            const auto residue = H::mkOp(H::Op::MOD_EUCLID, args, at);
            return H::mkOp(H::Op::ITE,
                           {H::mkOp(H::Op::GE, {args[1], H::mkInt("0", at)}, at),
                            residue, H::mkOp(H::Op::NEG, {residue}, at)}, at);
        }
        return H::mkOp(builtin.op, args, at);
    }

    struct NamedType {
        H::Sort sort;
        Mark alias_body;
        Uir::SourceLoc location;
        bool alias = false;
        bool resolving = false;
        bool resolved = false;
    };

    bool resolveNamedType(const std::string& name, H::Sort& out,
                           Uir::Diagnostics& diagnostics) {
        auto found = named_types_.find(name);
        if (found == named_types_.end()) { return false; }
        auto& declaration = found->second;
        if (declaration.resolved) { out = declaration.sort; return true; }
        if (declaration.resolving) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "cyclic type alias involving '" + name + "'",
                              declaration.location);
            return false;
        }
        const Mark caller = mark();
        declaration.resolving = true;
        reset(declaration.alias_body);
        const bool ok = type(declaration.sort, diagnostics) && expectP(";", diagnostics);
        declaration.resolving = false;
        declaration.resolved = ok;
        reset(caller);
        if (ok) { out = declaration.sort; }
        return ok;
    }

    bool collectNamedTypes(Uir::Diagnostics& diagnostics) {
        std::vector<std::string> order;
        while (tok_.kind != Token::END) {
            if (!is("type")) { skipItem(); continue; }
            const auto at = loc();
            eat();
            while (isP("{") && lex_.peekIsColonAfterBrace()) {
                eat();
                if (!expectP(":", diagnostics)) { return false; }
                if (is("builtin") || is("datatype")) {
                    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                      "semantic type attribute '" + tok_.text
                                          + "' needs an interpreted type encoding", loc());
                    return false;
                }
                int depth = 1;
                while (depth != 0) {
                    if (tok_.kind == Token::END) {
                        diagnostics.error(ErrorCode::E_PARSE, "unterminated type attribute", loc());
                        return false;
                    }
                    if (isP("{")) { ++depth; }
                    else if (isP("}")) { --depth; }
                    eat();
                }
            }
            std::vector<std::string> names;
            for (;;) {
                if (tok_.kind != Token::IDENT) {
                    diagnostics.error(ErrorCode::E_PARSE, "expected a type name", loc());
                    return false;
                }
                const auto name = tok_.text;
                if (name == "bool" || name == "int" || name == "real"
                    || (name.size() > 2 && name.compare(0, 2, "bv") == 0
                        && std::isdigit(static_cast<unsigned char>(name[2])))) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "cannot redeclare built-in type '" + name + "'", at);
                    return false;
                }
                names.push_back(name);
                eat();
                if (!isP(",")) { break; }
                eat();
            }
            const bool alias = isP("=");
            if (alias && names.size() != 1) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "a type alias declares one name", at);
                return false;
            }
            Mark body;
            if (alias) { eat(); body = mark(); }
            else if (!isP(";")) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "parameterized type declarations are not implemented", at);
                return false;
            }
            for (const auto& name : names) {
                NamedType declaration;
                declaration.location = at;
                declaration.alias = alias;
                declaration.alias_body = body;
                if (!alias) {
                    declaration.sort = H::Sort::uninterpreted(name);
                    declaration.resolved = true;
                }
                if (!named_types_.emplace(name, std::move(declaration)).second) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "duplicate type declaration '" + name + "'", at);
                    return false;
                }
                order.push_back(name);
                if (!alias) {
                    model_->uninterpreted_sorts.push_back(H::UninterpretedSortDecl{name, 0, at});
                }
            }
            // The alias RHS is parsed after every type name has been collected.
            while (!isP(";") && tok_.kind != Token::END) { eat(); }
            if (!expectP(";", diagnostics)) { return false; }
        }
        for (const auto& name : order) {
            H::Sort ignored;
            if (!resolveNamedType(name, ignored, diagnostics)) { return false; }
        }
        return true;
    }

    /** `bool`, `int`, `real`, `bv<n>`, and `[T]U` -- a one-index map.
     *
     *  This frontend's existing map profile is extensional SMT array theory
     *  (Boogie's /useArrayTheory interpretation). Totality alone does not imply
     *  extensionality; no claim is made about the default nonextensional map
     *  interpretation. `select` and `store` implement reads and updates.
     *
     *  A MULTI-index map `[int, int]int` is still refused. It is expressible --
     *  curry it, or index by a tuple -- and both choices change what the
     *  emitted script says a map IS, which is a decision this frontend does not
     *  make silently. Boogie's own textbook examples use only the one-index
     *  form.
     */
    bool type(H::Sort& out, Uir::Diagnostics& d) {
        if (isP("[")) {
            const Uir::SourceLoc at = loc();
            eat();                                  // '['
            H::Sort index;
            if (!type(index, d)) { return false; }
            if (isP(",")) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a multi-index map type is not implemented: an HIR array takes "
                        "one index, so this would have to be curried or indexed by a "
                        "tuple, and the two choices say different things about what the "
                        "map is", at);
                return false;
            }
            if (!expectP("]", d)) { return false; }
            H::Sort value;
            if (!type(value, d)) { return false; }
            out = H::Sort::array(index, value);
            if (!said_map_profile_) {
                said_map_profile_ = true;
                Uir::EncodingChoice choice;
                choice.site = file_;
                choice.unified_op = "map";
                choice.strategy = "extensional-array-theory";
                choice.fidelity = Uir::Fidelity::exact();
                choice.rationale =
                    "the existing Boogie map profile uses extensional SMT array theory, "
                    "corresponding to /useArrayTheory; equivalence to the default "
                    "nonextensional map interpretation is not claimed";
                report_->addChoice(std::move(choice));
            }
            return true;
        }
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE, "expected a type", loc());
            return false;
        }
        const std::string t = tok_.text;
        if (t == "int")       { out = H::Sort::integer(); }
        else if (t == "bool") { out = H::Sort::boolean(); }
        else if (t == "real") { out = H::Sort::real(); }
        else if (named_types_.count(t) != 0) {
            if (!resolveNamedType(t, out, d)) { return false; }
        }
        else if (t.size() > 2 && t.compare(0, 2, "bv") == 0
                 && std::isdigit(static_cast<unsigned char>(t[2]))) {
            unsigned width = 0;
            if (!unsignedDecimal(t.substr(2), width) || width == 0) {
                d.error(ErrorCode::E_TYPE, "invalid bit-vector width '" + t + "'", loc());
                return false;
            }
            out = H::Sort::bitvec(width);
        } else {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "type '" + t + "' is not implemented", loc());
            return false;
        }
        eat();
        return true;
    }

    /** A fresh name for @p base, which is how assignment and havoc are made
     *  static-single-assignment. Without versioning, `x := x + 1` becomes
     *  `x = x + 1` -- unsatisfiable, so the query is trivially "verified".
     *
     *  Two maps on purpose: version_ is the version READ here and is restored
     *  at branch boundaries; mint_ is the highest number ever minted for the
     *  name and never rolls back, so two branches cannot mint the same
     *  `x@2` -- two declarations of one name is what the semantic-contract
     *  layer then rightly calls ambiguous. */
    std::string fresh(const std::string& base) {
        const unsigned n = ++mint_[base];
        version_[base] = n;
        return n == 1 ? base : base + "@" + std::to_string(n);
    }
    std::string current(const std::string& base) const {
        const auto it = version_.find(base);
        if (it == version_.end() || it->second <= 1) { return base; }
        return base + "@" + std::to_string(it->second);
    }

    /** The source name for version @p v of @p base; version 0/1 is the
     *  unversioned declaration. */
    static std::string versionName(const std::string& base, unsigned v) {
        return v <= 1 ? base : base + "@" + std::to_string(v);
    }

    static H::ExprPtr conjoin(const H::ExprPtr& acc, const H::ExprPtr& e) {
        // Null-safe: the absent guard / no-condition case is the empty
        // conjunction, and AND(x, null) is how a null gets into the model.
        if (!acc) { return e; }
        if (!e) { return acc; }
        return H::mkOp(H::Op::AND, {acc, e});
    }

    /** `if (c) { T } else if ... else { E }`, and `if (*)` -- This is Boogie 2
     *  §9.7's desugaring is the edge structure:
     *
     *      if (E) Thn else Els  ===  goto L0, L1;
     *      L0: assume E;  Thn; goto Done;
     *      L1: assume ¬E; Els; goto Done;
     *      Done:
     *
     *  Each branch is processed under its guard -- its assumes and
     *  obligations are wrapped by it, so they hold only where control reaches
     *  them (the same discipline the loop's preservation path uses) -- and
     *  Done is the join of every edge: the branches' fall-throughs and any
     *  `break L` escapes from inside. The guards are path conditions built
     *  from branch decisions, so they are exclusive and the ite chain is
     *  exact. A branch that ends in `return`, `goto` or `break` contributes
     *  no fall-through edge. `L: if ...` makes L a `break L` target. */
    bool ifStatement(Uir::Diagnostics& d) {
        eat();                                    // 'if'
        std::vector<PendingEdge> break_edges;
        std::size_t breakables_added = 0;
        for (const std::string& l : pending_labels_) {
            breakables_.push_back(Breakable{l, false, &break_edges});
            ++breakables_added;
        }
        pending_labels_.clear();
        if (!expectP("(", d)) { return false; }
        H::ExprPtr cond;
        if (isP("*")) {
            eat();
            // A fresh, unconstrained boolean: either alternative may run, and
            // the ite join stays exact because the branches' guards are the
            // boolean and its negation.
            const std::string g = "if*!" + std::to_string(star_++);
            declare(g, H::Sort::boolean());
            cond = H::mkIdent(g, H::Sort::boolean(), loc());
        } else {
            cond = expr(d);
            if (!cond) { return false; }
        }
        if (!expectP(")", d)) { return false; }

        const H::ExprPtr saved_guard = path_guard_;
        const bool entry_dead = dead_;

        dead_ = entry_dead;
        path_guard_ = conjoin(saved_guard, cond);
        if (!statementList(d, false)) { return false; }
        const bool then_live = !dead_;
        std::vector<PendingEdge> edges;
        if (then_live) { edges.push_back(PendingEdge{path_guard_, version_}); }

        dead_ = entry_dead;
        path_guard_ = conjoin(saved_guard, H::mkOp(H::Op::NOT, {cond}));
        if (is("else")) {
            eat();
            if (is("if")) {
                if (!ifStatement(d)) { return false; }   // `else if`
            } else if (!statementList(d, false)) {
                return false;
            }
        }
        // No `else`: the identity edge -- the pre-if state under ¬cond.
        if (!dead_) { edges.push_back(PendingEdge{path_guard_, version_}); }
        for (PendingEdge& e : break_edges) { edges.push_back(std::move(e)); }
        for (std::size_t i = breakables_added; i > 0; --i) { breakables_.pop_back(); }

        // The join. Exclusivity makes the ite exact; one live edge means the
        // continuation simply IS that edge's state under its guard.
        if (edges.empty()) {
            // Both paths left the procedure: the continuation is unreachable.
            dead_ = true;
            path_guard_ = saved_guard;
            return true;
        }
        if (edges.size() == 1) {
            dead_ = false;
            version_ = edges.front().versions;
            path_guard_ = edges.front().guard;
            return true;
        }
        joinEdges(edges, /*gated=*/false);
        dead_ = false;
        return true;
    }

    void declare(const std::string& name, const H::Sort& s) {
        // Dead code (after a transfer, before the next label) is parsed and
        // type-checked but has no VC effect -- the reference prunes
        // unreachable blocks before VC generation. A declaration in dead code
        // would declare a symbol nothing constrains; skipping it is safe
        // because a later join never names a dead version.
        if (dead_) { return; }
        // The Horn route has no free program variables: every component of a
        // state tuple is bound in the clauses that use it, and the relations
        // are the only declarations (chcRel).
        if (chc_mode_) { return; }
        H::VarDecl d;
        d.name = name;
        d.sort = s;
        d.loc = loc();
        model_->decls.push_back(std::move(d));
    }

    bool globalDecl(Uir::Diagnostics& d, bool records_global = true) {
        eat();                                    // 'var'
        if (!attributes(d)) { return false; }
        for (;;) {
            // `var qq, rr: int;` -- names sharing a type are grouped, the same
            // way procedure parameters are. Reading one name per type made
            // every local declaration in DivMod.bpl and TuringFactorial.bpl
            // fail with "expected ':', found ','".
            std::vector<std::string> group;
            for (;;) {
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected a variable name", loc());
                    return false;
                }
                group.push_back(tok_.text);
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(":", d)) { return false; }
            H::Sort s;
            if (!type(s, d)) { return false; }
            if (!whereClauseRefused(d)) { return false; }
            for (const std::string& n : group) {
                if (!records_global && sorts_.count(n) != 0) {
                    // SSA versions are keyed by NAME, so a local that shadows
                    // a global (or another local) would silently version both
                    // together -- and a contract clause re-read at a call site
                    // would bind the local where the global is meant. Boogie
                    // permits the shadowing (ResolutionContext's AddVariable
                    // checks only the current scope); this frontend refuses it
                    // by name rather than version two variables as one.
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a local variable shadowing the already-declared `" + n
                                + "` is not implemented: SSA versions are keyed by "
                                  "name",
                            loc());
                    return false;
                }
                sorts_[n] = s;
                if (records_global) { global_vars_.insert(n); }
                declare(fresh(n), s);
            }
            if (isP(",")) { eat(); continue; }
            break;
        }
        return expectP(";", d);
    }

    /**
     * `const K: int;`, `const unique a, b: bool;`
     *
     * A constant is a global that is never assigned, so unlike `var` it is NOT
     * versioned: `fresh()` exists to give each assignment its own SSA name, and
     * a symbol that cannot be assigned has exactly one. Versioning one anyway
     * would still work here and would break the moment a procedure assigned to
     * something of the same name -- the constant would silently acquire a
     * second version and the axioms about it would refer to the first.
     *
     * `unique` is accepted and recorded as an obligation rather than dropped:
     * Boogie's `unique` asserts that the marked constants are pairwise
     * distinct, and dropping it admits models the source excludes.
     */
    bool constDecl(Uir::Diagnostics& d) {
        eat();                                    // 'const'
        if (!attributes(d)) { return false; }
        bool unique = false;
        if (is("unique")) {
            unique = true;
            eat();
        }
        std::vector<std::string> names;
        for (;;) {
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected a constant name", loc());
                return false;
            }
            names.push_back(tok_.text);
            eat();
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(":", d)) { return false; }
        H::Sort s;
        if (!type(s, d)) { return false; }
        for (const std::string& n : names) {
            if (sorts_.count(n) != 0) {
                d.error(ErrorCode::E_TYPE, "'" + n + "' is already declared", loc());
                return false;
            }
            sorts_[n] = s;
            consts_.insert(n);
            declare(n, s);                        // no version: see above
        }
        if (!usesClause(d)) { return false; }
        if (unique) {
            // Boogie's qualifier ranges over ALL unique constants of the same
            // type, including constants introduced by separate declarations.
            // Reasserting `distinct` over the accumulated set is redundant for
            // earlier pairs but exact, and avoids a quadratic pair expansion.
            std::vector<std::string>& all = unique_constants_[H::toString(s)];
            all.insert(all.end(), names.begin(), names.end());
            if (all.size() > 1 && !chc_mode_) {
                std::vector<H::ExprPtr> terms;
                terms.reserve(all.size());
                for (const std::string& n : all) {
                    terms.push_back(H::mkIdent(n, s, loc()));
                }
                H::Constraint c;
                c.loc = loc();
                c.formula = H::mkOp(H::Op::DISTINCT, terms, loc());
                model_->constraints.push_back(c);
            }
        }
        // A `uses` block ends the declaration: `const N: int uses { ... }`
        // carries no trailing semicolon.
        if (had_uses_) { return true; }
        return expectP(";", d);
    }

    /**
     * `function f(int, int) returns (int);`   -- uninterpreted
     * `function f(x: int): int;`              -- the same, other spelling
     * `function abs(x: int): int { if 0 <= x then x else -x }`  -- a DEFINITION
     *
     * The first two become an HIR `FunDecl`, which is exactly what they are.
     *
     * A definition becomes a declaration **plus an axiom** `forall x. f(x) =
     * body`, rather than being inlined at call sites. Both are exact; the axiom
     * form is chosen because it preserves the structure the source wrote -- one
     * symbol, one defining equation -- and because inlining a recursive
     * definition does not terminate, which Boogie permits and MiniZinc's
     * predicate inliner has to refuse (mzn_minimal.cpp, parsePredicateItem).
     */
    bool functionDecl(Uir::Diagnostics& d) {
        eat();                                    // 'function'
        BuiltinFunction builtin;
        if (!functionAttributes(builtin, d)) { return false; }
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE, "expected a function name", loc());
            return false;
        }
        const std::string name = tok_.text;
        const Uir::SourceLoc at = loc();
        eat();
        if (!expectP("(", d)) { return false; }

        std::vector<H::Sort>       params;
        std::vector<std::string>   param_names;    // empty string when unnamed
        while (!isP(")")) {
            if (!attributes(d)) { return false; }
            // Either `x: int` or a bare `int`. Boogie allows both, and only the
            // named form can appear in a body.
            // Either `x: int`, a group `x, y: int`, or a bare `int`. Only a
            // named parameter can appear in a body.
            std::vector<std::string> group;
            if (tok_.kind == Token::IDENT && lex_.namedGroupAhead()) {
                for (;;) {
                    if (tok_.kind != Token::IDENT) { break; }
                    group.push_back(tok_.text);
                    eat();
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (!expectP(":", d)) { return false; }
            }
            H::Sort ps;
            if (!type(ps, d)) { return false; }
            if (group.empty()) {
                params.push_back(ps);
                param_names.push_back("");
            } else {
                for (const std::string& n : group) {
                    params.push_back(ps);
                    param_names.push_back(n);
                }
            }
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(")", d)) { return false; }

        H::Sort result;
        if (is("returns")) {
            eat();
            if (!expectP("(", d)) { return false; }
            if (!type(result, d)) { return false; }
            if (!expectP(")", d)) { return false; }
        } else if (isP(":")) {
            eat();
            if (!type(result, d)) { return false; }
        } else {
            d.error(ErrorCode::E_PARSE,
                    "expected 'returns (T)' or ': T' after a function's parameters",
                    loc());
            return false;
        }

        if (sorts_.count(name) != 0 || funs_.count(name) != 0) {
            d.error(ErrorCode::E_TYPE, "'" + name + "' is already declared", at);
            return false;
        }
        if (!builtin.attribute.empty()) {
            if (!validateBuiltin(builtin, params, result, at, d)) { return false; }
            if (builtin.name == "MapImp") {
                if (chc_mode_) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "MapImp's quantified array definition is not a Horn clause; "
                            "the direct VC route carries it", at);
                    return false;
                }
                if (result.index->kind != H::SortKind::BOOL) {
                    builtin.pointwise_symbol = name;
                    declarePointwiseImplication(name, params, result, at);
                }
            }
            builtins_[name] = builtin;
        } else {
            H::FunDecl f;
            f.name = name;
            f.params = params;
            f.result = result;
            f.loc = at;
            model_->funs.push_back(f);
        }
        funs_[name] = params.size();
        funResult_[name] = result;
        funParams_[name] = params;

        if (!usesClause(d)) { return false; }
        if (had_uses_) { return true; }
        if (!isP("{")) { return expectP(";", d); }
        if (!builtin.attribute.empty()) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "an interpreted builtin function cannot also have a defining body", at);
            return false;
        }
        pending_functions_.push_back(FunctionBody{name, params, param_names, result, at, mark()});
        int depth = 0;
        do {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated function body", at);
                return false;
            }
            if (isP("{")) { ++depth; }
            else if (isP("}")) { --depth; }
            eat();
        } while (depth > 0);
        return true;
    }

    void declarePointwiseImplication(const std::string& name,
                                    const std::vector<H::Sort>& params,
                                    const H::Sort& result, const Uir::SourceLoc& at) {
        H::FunDecl function;
        function.name = name;
        function.params = params;
        function.result = result;
        function.loc = at;
        model_->funs.push_back(std::move(function));

        // HIR has no array-map/lambda node. Define the COMPLETE array, not
        // just the cells subsequently selected by this program. Array
        // extensionality makes this equation uniquely determine f(a,b).
        // Quantifying the operands also handles calls beneath source binders
        // without moving a bound argument into a global constraint.
        std::vector<H::Binder> binders;
        for (const H::Sort& sort : {result, result, *result.index}) {
            H::Binder binder;
            binder.name = "q!" + std::to_string(qv_++) + "!map";
            binder.sort = sort;
            binders.push_back(std::move(binder));
        }
        const auto left = H::mkBoundVar(binders[0].name, result, at);
        const auto right = H::mkBoundVar(binders[1].name, result, at);
        const auto index = H::mkBoundVar(binders[2].name, *result.index, at);
        const auto application = H::mkApply(name, result, {left, right}, at);
        const auto read = H::mkOp(H::Op::SELECT, {application, index}, at);
        const auto implication = H::mkOp(H::Op::IMPLIES,
            {H::mkOp(H::Op::SELECT, {left, index}, at),
             H::mkOp(H::Op::SELECT, {right, index}, at)}, at);
        H::Constraint definition;
        definition.loc = at;
        definition.formula = H::mkForall(std::move(binders),
            H::mkOp(H::Op::EQ, {read, implication}, at), at);
        model_->constraints.push_back(std::move(definition));
    }

    bool readFunctionBody(const FunctionBody& definition, Uir::Diagnostics& d) {
        const auto& name = definition.name;
        const auto& params = definition.params;
        const auto& param_names = definition.param_names;
        const auto& result = definition.result;
        const auto& at = definition.at;
        // ---- A definition: declaration plus `forall x. f(x) = body`. -------
        eat();                                    // '{'
        std::unordered_set<std::string> parameter_names;
        for (std::size_t i = 0; i < param_names.size(); ++i) {
            if (!parameter_names.insert(param_names[i]).second) {
                d.error(ErrorCode::E_TYPE, "duplicate function parameter '" + param_names[i] + "'", at);
                return false;
            }
            if (param_names[i].empty()) {
                d.error(ErrorCode::E_PARSE,
                        "function '" + name + "' has a body but its parameter "
                            + std::to_string(i + 1)
                            + " is unnamed, so the body cannot refer to it",
                        at);
                return false;
            }
        }
        // Alpha-renamed for the reason quantifier() renames: a definition's
        // parameter is a BOUND variable of the defining axiom, and `function
        // fact(n: int)` beside `procedure P(n: int)` is ordinary Boogie whose
        // scopes do not overlap. typeCheck refuses a binder that shadows a
        // declaration, and here too the collision may be with a procedure
        // parameter declared further down the file.
        std::vector<H::Binder> binders;
        binders.reserve(param_names.size());
        for (std::size_t i = 0; i < param_names.size(); ++i) {
            H::Binder b;
            b.name = "q!" + std::to_string(qv_++) + "!" + param_names[i];
            b.sort = params[i];
            binders.push_back(b);
            bound_[param_names[i]] = b.sort;
            renamed_binders_[param_names[i]] = b.name;
        }
        H::ExprPtr body = expr(d);
        for (const std::string& pn : param_names) {
            bound_.erase(pn);
            renamed_binders_.erase(pn);
        }
        if (!body) { return false; }
        if (!expectP("}", d)) { return false; }
        std::string mutable_global;
        if (firstMutableGlobal(body, mutable_global)) {
            d.error(ErrorCode::E_TYPE,
                    "function `" + name + "` refers to mutable global `"
                        + mutable_global
                        + "`; Boogie functions are stateless and cannot read mutable "
                          "program state",
                    at);
            return false;
        }

        std::vector<H::ExprPtr> args;
        args.reserve(binders.size());
        for (const H::Binder& b : binders) { args.push_back(H::mkBoundVar(b.name, b.sort, at)); }
        H::ExprPtr call = args.empty() ? H::mkApply(name, result, {}, at)
                                       : H::mkApply(name, result, args, at);
        H::ExprPtr eq = H::mkOp(H::Op::EQ, {call, body}, at);
        if (chc_mode_) {
            // A function definition is a quantified axiom over the constant
            // and function symbols -- not a Horn clause body. The direct VC
            // route (no `chc` option) carries it.
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "a function definition is not a Horn clause body; the direct "
                    "VC route carries it",
                    at);
            return false;
        }
        H::Constraint c;
        c.loc = at;
        c.formula = binders.empty() ? eq : H::mkForall(binders, eq, at);
        model_->constraints.push_back(c);
        return true;
    }

    /** An axiom is assumed globally (§4.4). Asserted positively, unlike the
     *  postcondition: it is a hypothesis about the world, not an obligation. */
    bool axiom(Uir::Diagnostics& d) {
        eat();                                    // 'axiom'
        if (!attributes(d)) { return false; }     // {:include_dep} and friends
        const Mark axiom_mark = mark();
        H::ExprPtr e = expr(d);
        if (!e) { return false; }
        if (!expectP(";", d)) { return false; }
        std::string mutable_global;
        if (firstMutableGlobal(e, mutable_global)) {
            d.error(ErrorCode::E_TYPE,
                    "axiom refers to mutable global `" + mutable_global
                        + "`; Boogie axioms are stateless and may refer only to "
                          "constants, functions, and bound variables",
                    loc());
            return false;
        }
        if (chc_mode_) {
            if (e->kind == H::ExprKind::FORALL || e->kind == H::ExprKind::EXISTS) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a quantified axiom is not a Horn clause body; the direct VC "
                        "route (no `chc` option) carries it",
                        loc());
                return false;
            }
            // The mark, not the formula: a constant is a tuple component in
            // this route, so the axiom is RE-READ inside each procedure's
            // entry clause, where the name resolves to the clause's binder.
            chc_axioms_.push_back(axiom_mark);
            return true;
        }
        H::Constraint c;
        c.loc = loc();
        c.formula = e;
        model_->constraints.push_back(c);
        // §4.4: an inconsistent axiom makes the whole verification vacuous, and
        // an inconsistency check is not optional. Recorded rather than run,
        // because running it means a second solver call this pipeline does not
        // make -- and a reader who is not told cannot know the risk was taken.
        if (!said_axiom_) {
            said_axiom_ = true;
            Uir::EncodingChoice ch;
            ch.site       = file_;
            ch.unified_op = "axiom";
            ch.strategy   = "assumed-globally-unchecked";
            ch.fidelity   = Uir::Fidelity::exact();
            ch.rationale =
                "axioms are assumed globally and NOT checked for consistency; an "
                "inconsistent axiom set makes every procedure verify vacuously, and "
                "detecting that needs a separate satisfiability check this pipeline "
                "does not make";
            report_->addChoice(std::move(ch));
        }
        return true;
    }

    /** Pass 1: a procedure's signature and contract, and nothing else.
     *
     *  A call is encoded against the callee's CONTRACT, so the contract must
     *  exist before any body is read -- and Boogie does not order
     *  declarations, so a call may sit above the callee it names. The clause
     *  EXPRESSIONS are not read here; each is recorded as a Mark and re-parsed
     *  where it is used, because an expression's meaning is its SSA resolution
     *  at the point of use: the body reads `requires` against its entry
     *  versions, a call site against the caller's current ones. */
    bool procedureSignature(Uir::Diagnostics& d) {
        eat();                                    // 'procedure'
        if (!attributes(d)) { return false; }
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE, "expected a procedure name", loc());
            return false;
        }
        const std::string name = tok_.text;
        eat();
        if (isP("<")) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "procedure type parameters are not implemented", loc());
            return false;
        }
        if (procs_.count(name) != 0) {
            d.error(ErrorCode::E_TYPE,
                    "procedure '" + name + "' is already declared", loc());
            return false;
        }
        ProcSig sig;
        if (!expectP("(", d)) { return false; }
        if (!signatureFormals(d, sig.in_names, sig.in_sorts)) { return false; }
        // ')'
        if (is("returns")) {
            eat();
            if (!expectP("(", d)) { return false; }
            if (!signatureFormals(d, sig.out_names, sig.out_sorts)) { return false; }
        }
        // The signature-terminating `;` comes BEFORE the contract clauses.
        sig.contract_start = mark();
        if (isP(";")) { eat(); }
        for (;;) {
            bool free_clause = false;
            if (is("free")) { free_clause = true; eat(); }
            if (is("requires") || is("ensures")) {
                const bool is_req = is("requires");
                eat();
                if (!attributes(d)) { return false; }
                const Mark m = mark();
                if (!skipExpression(d) || !expectP(";", d)) { return false; }
                (is_req ? sig.requires : sig.ensures).push_back({m, free_clause});
            } else if (is("modifies")) {
                eat();
                while (tok_.kind == Token::IDENT) {
                    // Not checked against the globals here: a modifies may name
                    // a global declared further down the file, and pass 2's
                    // re-read of the clause is where every declaration exists.
                    (free_clause ? sig.modifies_free : sig.modifies_checked)
                        .insert(tok_.text);
                    eat();
                    if (isP(",")) { eat(); }
                }
                if (!expectP(";", d)) { return false; }
            } else if (free_clause) {
                d.error(ErrorCode::E_PARSE,
                        "expected 'requires', 'ensures' or 'modifies' after 'free'",
                        loc());
                return false;
            } else {
                break;
            }
        }
        procs_[name] = std::move(sig);
        // A body, if one follows, is pass 2's business.
        if (isP(";")) { eat(); return true; }
        if (!isP("{")) { return true; }          // bodiless: next item follows
        if (infer_modifies_) { inference_bodies_.emplace_back(name, mark()); }
        int depth = 0;
        do {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated procedure body", loc());
                return false;
            }
            if (isP("{")) { ++depth; }
            else if (isP("}")) { --depth; }
            eat();
        } while (depth > 0);
        return true;
    }

    /** Syntactic may-write closure, as in Boogie's ModSetCollector. Retain
     *  declared frames (including bodiless procedures), collect global LHSs,
     *  havoc targets and call results, then propagate effects through calls.
     *  Multiple implementations contribute to the same procedure summary.
     *  This does not inline bodies, infer postconditions, or make calls async.
     *
     *  The existing free-modifies extension remains a separate permission
     *  channel. An observed actual write is checked, even if a free clause
     *  also mentions it; an unobserved free-only declaration stays free. */
    bool inferProcedureModifies(Uir::Diagnostics& d) {
        std::map<std::string, std::unordered_set<std::string>> declared_checked, declared_free;
        for (const auto& entry : procs_) {
            declared_checked[entry.first] = entry.second.modifies_checked;
            declared_free[entry.first] = entry.second.modifies_free;
            for (const auto* frame : {&entry.second.modifies_checked,
                                      &entry.second.modifies_free}) {
                for (const std::string& name : *frame) {
                    if (global_vars_.count(name) == 0) {
                        d.error(ErrorCode::E_TYPE, "modifies entry `" + name
                                    + "` is not a mutable global variable", loc());
                        return false;
                    }
                }
            }
        }
        for (const Mark& position : inference_implementations_) {
            reset(position);
            eat();                               // 'implementation'
            if (!attributes(d)) { return false; }
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected an implementation name", loc());
                return false;
            }
            const std::string name = tok_.text;
            eat();
            if (isP("<")) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "procedure type parameters are not implemented", loc());
                return false;
            }
            std::vector<std::string> inputs, outputs;
            std::vector<H::Sort> input_sorts, output_sorts;
            if (!expectP("(", d)
                || !signatureFormals(d, inputs, input_sorts)) { return false; }
            if (is("returns")) {
                eat();
                if (!expectP("(", d)
                    || !signatureFormals(d, outputs, output_sorts)) { return false; }
            }
            if (!matchImplementation(name, inputs, input_sorts,
                                     outputs, output_sorts, d)) { return false; }
            inference_bodies_.emplace_back(name, mark());
        }

        std::map<std::string, std::unordered_set<std::string>> calls, callers;
        std::map<std::string, std::unordered_set<std::string>> direct;
        for (const auto& body : inference_bodies_) {
            reset(body.second);
            body_scan_ = BodyScan();
            scan_builds_.clear();
            scan_gotos_.clear();
            list_while_.clear();
            scan_stack_.clear();
            std::vector<std::string> assigned;
            inference_calls_ = &calls[body.first];
            const bool ok = scanList(d, false, assigned);
            inference_calls_ = nullptr;
            if (!ok) { return false; }
            for (const std::string& name : assigned) {
                if (global_vars_.count(name) != 0) {
                    direct[body.first].insert(name);
                    procs_.at(body.first).modifies_checked.insert(name);
                }
            }
        }

        // The worklist operates on the call graph, not repeated source
        // parsing. Finite monotone sets give a least fixed point even for
        // mutually recursive procedures, independently of declaration order.
        for (const auto& entry : calls) {
            for (const std::string& callee : entry.second) {
                if (procs_.count(callee) == 0) {
                    d.error(ErrorCode::E_TYPE,
                            "call to undeclared procedure `" + callee + "`", loc());
                    return false;
                }
                callers[callee].insert(entry.first);
            }
        }
        std::vector<std::string> pending;
        std::unordered_set<std::string> queued;
        for (const auto& entry : procs_) {
            pending.push_back(entry.first);
            queued.insert(entry.first);
        }
        while (!pending.empty()) {
            const std::string callee = pending.back();
            pending.pop_back();
            queued.erase(callee);
            const ProcSig& effect = procs_.at(callee);
            for (const std::string& caller : callers[callee]) {
                if (caller == callee) { continue; }
                ProcSig& frame = procs_.at(caller);
                bool changed = false;
                for (const std::string& name : effect.modifies_checked) {
                    changed = frame.modifies_checked.insert(name).second || changed;
                }
                for (const std::string& name : effect.modifies_free) {
                    changed = frame.modifies_free.insert(name).second || changed;
                }
                if (changed && queued.insert(caller).second) { pending.push_back(caller); }
            }
        }

        auto names = [](const std::unordered_set<std::string>& values) {
            std::vector<std::string> sorted(values.begin(), values.end());
            std::sort(sorted.begin(), sorted.end());
            std::string text = "{";
            for (std::size_t i = 0; i < sorted.size(); ++i) {
                if (i != 0) { text += ", "; }
                text += sorted[i];
            }
            return text + "}";
        };
        std::vector<std::string> procedures;
        for (const auto& entry : procs_) { procedures.push_back(entry.first); }
        std::sort(procedures.begin(), procedures.end());
        for (const std::string& name : procedures) {
            const ProcSig& sig = procs_.at(name);
            Uir::EncodingChoice choice;
            choice.site = file_ + ":" + name;
            choice.unified_op = "modifies";
            choice.strategy = "call-graph-modifies-fixed-point";
            choice.fidelity = Uir::Fidelity::exact();
            choice.rationale = "explicit infer_modifies=1; procedure " + name
                + "; declared checked=" + names(declared_checked[name])
                + "; declared free=" + names(declared_free[name])
                + "; direct global writes=" + names(direct[name])
                + "; calls=" + names(calls[name])
                + "; checked frame=" + names(sig.modifies_checked)
                + "; free permissions=" + names(sig.modifies_free)
                + "; declared frames are retained; globals outside the checked "
                  "frame retain their call-entry values; no callee body inlining";
            report_->addChoice(std::move(choice));
        }
        return true;
    }

    /** The grouped formal list `(a, b: int, c: bool)` of a procedure
     *  signature, leaving tok_ past the closing `)`. */
    bool signatureFormals(Uir::Diagnostics& d, std::vector<std::string>& names,
                          std::vector<H::Sort>& sorts) {
        while (!isP(")")) {
            if (!attributes(d)) { return false; }
            std::vector<std::string> group;
            for (;;) {
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected a parameter name", loc());
                    return false;
                }
                group.push_back(tok_.text);
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(":", d)) { return false; }
            H::Sort s;
            if (!type(s, d)) { return false; }
            if (!whereClauseRefused(d)) { return false; }
            for (const std::string& n : group) {
                names.push_back(n);
                sorts.push_back(s);
            }
            if (isP(",")) { eat(); }
        }
        eat();                                    // ')'
        return true;
    }

    /** Implementations match their declaration by position and type, not by
     *  spelling. The declaration registry is complete before this is called,
     *  so an implementation may precede its declaration. */
    bool matchImplementation(const std::string& name,
                             const std::vector<std::string>& inputs,
                             const std::vector<H::Sort>& input_sorts,
                             const std::vector<std::string>& outputs,
                             const std::vector<H::Sort>& output_sorts,
                             Uir::Diagnostics& d) {
        const auto found = procs_.find(name);
        if (found == procs_.end()) {
            d.error(ErrorCode::E_TYPE,
                    "implementation `" + name + "` has no procedure declaration", loc());
            return false;
        }
        const ProcSig& sig = found->second;
        auto match = [&](const std::vector<H::Sort>& actual,
                         const std::vector<H::Sort>& declared,
                         const std::string& direction) {
            if (actual.size() != declared.size()) {
                d.error(ErrorCode::E_TYPE,
                        "implementation `" + name + "` has a mismatched number of "
                            + direction + "-parameters", loc());
                return false;
            }
            for (std::size_t i = 0; i < actual.size(); ++i) {
                if (!H::sameSort(actual[i], declared[i])) {
                    d.error(ErrorCode::E_TYPE,
                            "implementation `" + name + "` has a mismatched type for "
                                + direction + "-parameter " + std::to_string(i + 1), loc());
                    return false;
                }
            }
            return true;
        };
        if (!match(input_sorts, sig.in_sorts, "in")
            || !match(output_sorts, sig.out_sorts, "out")) { return false; }
        for (bool declaration : {false, true}) {
            std::unordered_set<std::string> seen;
            for (const auto* names : {declaration ? &sig.in_names : &inputs,
                                      declaration ? &sig.out_names : &outputs}) {
                for (const std::string& n : *names) {
                    if (!seen.insert(n).second) {
                        d.error(ErrorCode::E_TYPE,
                                "parameter `" + n + "` is declared more than once", loc());
                        return false;
                    }
                    if (global_vars_.count(n) != 0 || consts_.count(n) != 0) {
                        d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "a parameter shadowing the global `" + n
                                    + "` is not implemented: SSA versions are keyed by name", loc());
                        return false;
                    }
                }
            }
        }
        for (const auto* names : {&sig.modifies_checked, &sig.modifies_free}) {
            for (const std::string& n : *names) {
                if (global_vars_.count(n) == 0) {
                    d.error(ErrorCode::E_TYPE, "modifies entry `" + n
                                + "` is not a mutable global variable", loc());
                    return false;
                }
            }
        }
        if (!isP("{")) {
            d.error(ErrorCode::E_PARSE, "expected an implementation body", loc());
            return false;
        }
        return true;
    }

    /** Skip one expression, leaving tok_ at the terminating `;`. Pass 1
     *  records contract clauses as marks instead of reading them. */
    bool skipExpression(Uir::Diagnostics& d) {
        int depth = 0;
        for (;;) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated expression", loc());
                return false;
            }
            if (depth == 0 && isP(";")) { return true; }
            if (isP("(") || isP("[") || isP("{")) { ++depth; }
            else if (isP(")") || isP("]") || isP("}")) { --depth; }
            eat();
        }
    }

    bool procedure(Uir::Diagnostics& d) {
        const bool implementation = is("implementation");
        eat();                                    // 'procedure' or 'implementation'
        if (!attributes(d)) { return false; }
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE, "expected a procedure name", loc());
            return false;
        }
        const std::string procedure_name = tok_.text;
        eat();
        if (isP("<")) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "procedure type parameters are not implemented", loc());
            return false;
        }
        sorts_ = global_sorts_;
        old_aliases_.clear();
        bound_.clear();
        renamed_binders_.clear();
        input_formals_.clear();
        procedure_modifies_.clear();
        const std::size_t declaration_begin = model_->decls.size();
        if (procedure_count_++ != 0) {
            // Each procedure is verified from an independent entry state.
            // Fresh aliases prevent one procedure's final global version from
            // becoming the next procedure's initial value.
            for (const std::string& name : global_vars_) {
                declare(fresh(name), global_sorts_.at(name));
            }
        }
        // The entry version of every global, recorded NOW: the contracts are
        // parsed against these names, and old() ties to them. (The alias mint
        // above is what makes them fresh for a non-first procedure.)
        entry_versions_.clear();
        for (const std::string& name : global_vars_) {
            entry_versions_[name] = current(name);
        }
        const std::size_t branch_begin = model_->constraints.size();
        std::vector<std::string> in_names, out_names;
        std::vector<H::Sort> in_sorts, out_sorts;
        if (!expectP("(", d)) { return false; }
        while (!isP(")")) {
            if (!attributes(d)) { return false; }
            // `(a, b: int)` -- Boogie groups parameters that share a type, and
            // reading one name per type made `procedure T(a,b: int)` fail with
            // "expected ':', found ','" on a signature the language allows.
            std::vector<std::string> group;
            for (;;) {
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected a parameter name", loc());
                    return false;
                }
                group.push_back(tok_.text);
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(":", d)) { return false; }
            H::Sort s;
            if (!type(s, d)) { return false; }
            if (!whereClauseRefused(d)) { return false; }
            for (const std::string& n : group) {
                if (global_vars_.count(n) != 0 || consts_.count(n) != 0) {
                    // A formal shadowing a global would version the two
                    // together -- see the same refusal for locals.
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a parameter shadowing the global `" + n
                                + "` is not implemented: SSA versions are keyed by "
                                  "name",
                            loc());
                    return false;
                }
                if (input_formals_.count(n) != 0) {
                    d.error(ErrorCode::E_TYPE,
                            "parameter `" + n + "` is declared more than once", loc());
                    return false;
                }
                sorts_[n] = s;
                input_formals_.insert(n);
                declare(fresh(n), s);
                in_names.push_back(n);
                in_sorts.push_back(s);
            }
            if (isP(",")) { eat(); }
        }
        eat();                                    // ')'

        if (is("returns")) {
            eat();
            if (!expectP("(", d)) { return false; }
            while (!isP(")")) {
                if (!attributes(d)) { return false; }
                // Grouped exactly as the parameters are: `returns (q, r: int)`.
                std::vector<std::string> group;
                for (;;) {
                    if (tok_.kind != Token::IDENT) {
                        d.error(ErrorCode::E_PARSE, "expected a result name", loc());
                        return false;
                    }
                    group.push_back(tok_.text);
                    eat();
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (!expectP(":", d)) { return false; }
                H::Sort s;
                if (!type(s, d)) { return false; }
                if (!whereClauseRefused(d)) { return false; }
                for (const std::string& n : group) {
                    if (global_vars_.count(n) != 0 || consts_.count(n) != 0) {
                        d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "a parameter shadowing the global `" + n
                                    + "` is not implemented: SSA versions are keyed "
                                      "by name",
                                loc());
                        return false;
                    }
                    if (sorts_.count(n) != 0) {
                        // The in-parameters are in sorts_ by now, so this is a
                        // repeated parameter name, which the signature's
                        // distinctness rule makes source-illegal.
                        d.error(ErrorCode::E_TYPE,
                                "parameter `" + n + "` is declared more than once",
                                loc());
                        return false;
                    }
                    sorts_[n] = s;
                    declare(fresh(n), s);
                    out_names.push_back(n);
                    out_sorts.push_back(s);
                }
                if (isP(",")) { eat(); }
            }
            eat();
        }

        const Mark implementation_body = mark();
        if (implementation) {
            if (!matchImplementation(procedure_name, in_names, in_sorts,
                                     out_names, out_sorts, d)) { return false; }
            const ProcSig& sig = procs_.at(procedure_name);
            for (std::size_t i = 0; i < in_names.size(); ++i) {
                call_formals_[sig.in_names[i]] = H::mkIdent(current(in_names[i]), in_sorts[i]);
            }
            for (std::size_t i = 0; i < out_names.size(); ++i) {
                call_formals_[sig.out_names[i]] = H::mkIdent(current(out_names[i]), out_sorts[i]);
            }
            // Re-read only the declared contract, using implementation-state
            // formals. Quantifier binders still shadow these substitutions.
            contract_scope_ = true;
            reset(sig.contract_start);
        }

        // Boogie writes the signature-terminating `;` BEFORE the contract
        // clauses in a bodiless declaration: `procedure P(...) returns (...);
        // requires ...;`. Accepting it here rather than only after the clauses
        // is what lets such a declaration parse at all.
        if (isP(";")) { eat(); }

        // Per procedure: an obligation belongs to the contract it appears in.
        obligations_.clear();
        path_guard_ = nullptr;
        dead_ = false;
        body_ensures_.clear();
        frames_.clear();
        breakables_.clear();
        pending_labels_.clear();
        while_body_starts_.clear();
        while_body_contexts_.clear();
        for (;;) {
            bool free_clause = false;
            if (is("free")) { free_clause = true; eat(); }
            if (is("requires")) {
                eat();
                if (!attributes(d)) { return false; }
                if (implementation) {
                    for (const std::string& n : procs_.at(procedure_name).out_names) {
                        call_formals_.erase(n);
                        contract_forbidden_.insert(n);
                    }
                }
                // A precondition may not use old expressions (This is Boogie 2
                // §8) -- enforced by in_requires_ inside parseAtom.
                in_requires_ = true;
                H::ExprPtr e = expr(d);
                in_requires_ = false;
                if (implementation) {
                    const ProcSig& sig = procs_.at(procedure_name);
                    contract_forbidden_.clear();
                    for (std::size_t i = 0; i < out_names.size(); ++i) {
                        call_formals_[sig.out_names[i]] =
                            H::mkIdent(current(out_names[i]), out_sorts[i]);
                    }
                }
                if (!e || !expectP(";", d)) { return false; }
                // ASSUMED at the body, free or checked alike: the callee
                // traces keep every precondition; only the CALLER ignores the
                // free ones (This is Boogie 2 §8.2). The other side -- checked
                // ones asserted at each call site -- is callStatement.
                addAssume(e);
            } else if (is("ensures")) {
                eat();
                if (!attributes(d)) { return false; }
                H::ExprPtr e = expr(d);
                if (!e || !expectP(";", d)) { return false; }
                // ASSERTED at the body only when checked. A free ensures is
                // assumed at call sites but never an obligation here (§8.2).
                if (!free_clause) { body_ensures_.push_back(e); }
            } else if (is("modifies")) {
                eat();
                while (tok_.kind == Token::IDENT) {
                    const std::string name = tok_.text;
                    if (global_vars_.count(name) == 0) {
                        d.error(ErrorCode::E_TYPE,
                                "modifies entry `" + name
                                    + "` is not a mutable global variable", loc());
                        return false;
                    }
                    if (!procedure_modifies_.insert(name).second) {
                        d.error(ErrorCode::E_PARSE,
                                "modifies lists global `" + name + "` more than once",
                                loc());
                        return false;
                    }
                    // A free modifies permits the write in the body (the set
                    // above is both kinds); only the CALLER's frame ignores it.
                    eat();
                    if (isP(",")) { eat(); }
                }
                if (!expectP(";", d)) { return false; }
                if (!said_modifies_) {
                    said_modifies_ = true;
                    Uir::EncodingChoice ch;
                    ch.site       = file_;
                    ch.unified_op = "modifies";
                    ch.strategy   = "body-write-permission";
                    ch.fidelity   = Uir::Fidelity::exact();
                    ch.rationale =
                        "the clause is enforced as the exact permission set for mutable "
                        "global writes in the procedure body; the caller frame is "
                        "realised at call sites, which havoc exactly the callee's "
                        "checked modifies globals";
                    report_->addChoice(std::move(ch));
                }
            } else if (free_clause) {
                d.error(ErrorCode::E_PARSE,
                        "expected 'requires', 'ensures' or 'modifies' after 'free'",
                        loc());
                return false;
            } else {
                break;
            }
        }

        if (infer_modifies_) {
            const ProcSig& sig = procs_.at(procedure_name);
            procedure_modifies_.insert(sig.modifies_checked.begin(), sig.modifies_checked.end());
            procedure_modifies_.insert(sig.modifies_free.begin(), sig.modifies_free.end());
        }

        if (implementation) {
            call_formals_.clear();
            contract_scope_ = false;
            reset(implementation_body);
        }

        // A body is OPTIONAL: `procedure P(...) returns (...); requires ...;`
        // with no `{` is a declaration, whose contract is only usable by a
        // caller. Its terminating `;` comes before the contract clauses, so by
        // here there is nothing left to consume -- the next token starts the
        // next declaration.
        //
        // Recognised by what follows rather than by accepting anything that is
        // not `{`: a typo inside a body must still be a parse error naming the
        // token, not a procedure silently read as bodiless.
        if (isP(";")) {
            eat();
            model_->constraints.resize(branch_begin);
            model_->decls.resize(declaration_begin);
            return true;
        }
        if (!isP("{")) {
            if (tok_.kind == Token::END || is("procedure") || is("implementation")
                || is("var") || is("axiom") || is("const") || is("function")
                || is("type")) {
                model_->constraints.resize(branch_begin);
                model_->decls.resize(declaration_begin);
                return true;
            }
            d.error(ErrorCode::E_PARSE,
                    "expected a procedure body or the next declaration, found '"
                        + tok_.text + "'", loc());
            return false;
        }
        // The pre-scan runs before any statement is processed: which labels
        // are loop headers (backward-goto targets) and what each cycle
        // assigns must be known when the header is reached, which is BEFORE
        // its back edge is seen. The scan is syntactic and refusals are
        // named there.
        const Mark body_mark = mark();           // tok_ is '{'
        if (!scanBody(d)) { return false; }
        reset(body_mark);
        if (!statementList(d, false)) { return false; }
        saw_procedure_ = true;

        // The query is a refutation: each obligation contributes a separate
        // counterexample branch consisting of the assumptions and SSA
        // equalities that precede THAT obligation, followed by its negation.
        // A single negation around all obligations loses these program points:
        // an `assume false` after an earlier failing assert would then make the
        // whole procedure branch inconsistent and falsely "verify" it.
        //
        // The final fall-through is one exit point; every `return` in the
        // body was another, and emitted its own.
        if (!dead_) { emitEnsures(); }
        dead_ = false;
        H::ExprPtr branch = H::mkBool(false, loc());
        for (const ObligationPoint& obligation : obligations_) {
            H::ExprPtr counterexample =
                H::mkOp(H::Op::NOT, {obligation.formula});
            for (std::size_t i = branch_begin; i < obligation.prefix_end; ++i) {
                counterexample = H::mkOp(
                    H::Op::AND, {model_->constraints[i].formula, counterexample});
            }
            branch = H::mkOp(H::Op::OR, {branch, counterexample});
        }

        // A file asks whether EVERY procedure verifies. Its refutation is the
        // disjunction of per-procedure counterexample branches. Keeping each
        // procedure's paths separate prevents a later assumption, or an
        // infeasible independent procedure, from suppressing an earlier bug.
        model_->constraints.resize(branch_begin);
        procedure_refutations_.push_back(std::move(branch));
        (void)procedure_name;
        return true;
    }

    /** Rewrite every program variable in @p e to its FINAL version.
     *
     *  `ensures` clauses are parsed before the body runs, so every identifier
     *  in them resolves to version 1 -- and `y := x + 1` then leaves the
     *  postcondition talking about the *entry* `y` rather than the one the body
     *  assigned. The script is still well-formed and still gets a verdict: the
     *  negated postcondition constrains a variable nothing else mentions, so it
     *  is trivially satisfiable and the procedure reports "not verified" while
     *  being correct. Nothing about the output looks wrong.
     *
     *  So the clause is parsed early, for its scope, and resolved late, for its
     *  meaning. */
    H::ExprPtr finalise(const H::ExprPtr& e) {
        // Every EXISTING version name maps to the final one, not only the base
        // name: a contract is parsed before the body runs, and in a non-first
        // procedure the entry alias (g@2, say) is what gets baked into the
        // clause -- mapping only the base name would leave the clause talking
        // about the entry state, which for a global the body changed is the
        // wrong state. (Found by loop_call_modifies in the verdict corpus.)
        std::unordered_map<std::string, std::string> to_current;
        for (const auto& kv : sorts_) {
            const std::string& base = kv.first;
            const unsigned hi = mint_.count(base) != 0 ? mint_.at(base) : 0;
            for (unsigned v = 1; v <= hi; ++v) {
                to_current[versionName(base, v)] = current(base);
            }
            to_current[base] = current(base);
        }
        return H::substituteIdents(e, to_current, sorts_);
    }

    /** The checked postconditions as obligations at ONE exit point -- the
     *  final fall-through or a `return` -- resolved against the versions in
     *  force there. */
    void emitEnsures() {
        for (const H::ExprPtr& e : body_ensures_) {
            addObligation(finalise(e));
        }
    }

    /** Record a proof obligation, under the path condition it sits on.
     *
     *  Straight-line code has one path, so `path_guard_` is null and an
     *  obligation is recorded as written. A loop or a branch introduces
     *  another path, and from that point the continuation is only reachable
     *  in the state the construct exited in -- so everything after it is an
     *  obligation about that state and not about every state. See
     *  whileStatement for what goes wrong without this: the exit assumptions
     *  land in the same conjunction as the preservation check, and if they
     *  are contradictory the whole script is unsatisfiable, which this
     *  encoding reads as "verified". */
    void addObligation(const H::ExprPtr& e) {
        // An assertion in dead code is not checked: the reference prunes
        // unreachable blocks before VC generation, so their obligations do
        // not exist.
        if (dead_) { return; }
        obligations_.push_back(
            ObligationPoint{path_guard_ ? H::mkOp(H::Op::IMPLIES, {path_guard_, e})
                                        : e,
                            model_->constraints.size()});
    }

    void addAssume(const H::ExprPtr& e) {
        if (dead_) { return; }                 // unreachable, as above
        // Guarded by the path condition in force, ALWAYS. A raw constraint
        // over a shared (pre-split) version would constrain paths that never
        // executed the assume -- with a join in the program that is the
        // classic unsoundness of a flat encoding, and it shows up as a
        // counterexample wrongly excluded.
        H::Constraint c;
        c.loc = loc();
        c.formula = path_guard_ ? H::mkOp(H::Op::IMPLIES, {path_guard_, e}) : e;
        model_->constraints.push_back(c);
    }

    /** A `where` on a parameter or variable group is a free pre/postcondition
     *  on the variable (This is Boogie 2's A/B/C rules); dropping it admits
     *  states the source excludes, so it is refused by name. */
    bool whereClauseRefused(Uir::Diagnostics& d) {
        if (!is("where")) { return true; }
        d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "a 'where' clause is not implemented: it is a free pre/postcondition "
                "on the variable, and dropping it would admit states the source "
                "excludes",
                loc());
        return false;
    }

    /** Bind a callee's formals to their caller-side meaning: in-formals to the
     *  actual expressions (read against the pre-call versions), out-formals to
     *  the fresh versions minted for the call's targets. parseAtom consults
     *  the map before its own scope. */
    void bindCallFormals(const ProcSig& sig, const std::vector<H::ExprPtr>& args,
                         const std::vector<std::string>& out_versions) {
        for (std::size_t i = 0; i < args.size(); ++i) {
            call_formals_[sig.in_names[i]] = args[i];
        }
        for (std::size_t i = 0; i < out_versions.size(); ++i) {
            call_formals_[sig.out_names[i]] =
                H::mkIdent(out_versions[i], sig.out_sorts[i]);
        }
    }

    /** Re-read one contract clause of @p sig in the caller's context.
     *
     *  The clause's text was recorded as a Mark in pass 1 because its meaning
     *  is its SSA resolution at the point of USE: an identifier resolves to
     *  the caller's current version, a formal to the expression bound by
     *  bindCallFormals, and -- for an ensures clause -- `old(g)` to g's
     *  version at call entry (old_overrides_). A requires clause may not use
     *  `old` (This is Boogie 2 §8), which in_requires_ makes a type error. */
    H::ExprPtr readContractClause(const ProcContract& c, bool is_ensures,
                                  Uir::Diagnostics& d) {
        const bool saved_req   = in_requires_;
        const bool saved_scope = contract_scope_;
        in_requires_    = !is_ensures;
        contract_scope_ = true;
        const Mark here = mark();
        reset(c.mark);
        H::ExprPtr out;
        if (attributes(d)) { out = expr(d); }
        reset(here);
        in_requires_    = saved_req;
        contract_scope_ = saved_scope;
        return out;
    }

    /** `call x, y := P(e1, e2);` -- the two-sided contract at the call site,
     *  and no inlining.
     *
     *  Per This is Boogie 2 §8.2/§9.9 (docs/languages/boogie.md §2.3's table):
     *
     *    1. ASSERT every checked `requires` with actuals substituted for the
     *       in-formals -- each its own refutation branch, so a violated
     *       precondition reports sat (§2.5 alpha). A free requires is IGNORED
     *       by the caller, and a `free call` skips the step.
     *    2. Havoc the callee's CHECKED modifies globals and mint fresh
     *       versions for the out-parameter targets; a global the clause does
     *       not list keeps its version, which is the frame. Free modifies are
     *       invisible to the caller.
     *    3. ASSUME every `ensures` (checked and free) with out-formals bound
     *       to the fresh targets and `old()` resolved to the call-entry
     *       state.
     *
     *  The call is legal only if the callee's whole modifies set (checked and
     *  free) lies inside the caller's: the reference implementation's
     *  CheckAssignments makes the same check over GetAssignedVariables, which
     *  for a call includes the callee's modifies (AbsyCmd.cs). Without it the
     *  caller's own frame would be a lie. */
    bool callStatement(Uir::Diagnostics& d) {
        if (is("async")) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "'async call' is not implemented: an asynchronous call does not "
                    "give the caller the callee's postcondition, so it is not a "
                    "contract instantiation",
                    loc());
            return false;
        }
        bool free_call = false;
        if (is("free")) { free_call = true; eat(); }
        if (!is("call")) {
            d.error(ErrorCode::E_PARSE, "expected 'call' after 'free'", loc());
            return false;
        }
        eat();                                    // 'call'
        if (!attributes(d)) { return false; }
        if (is("forall")) { return callForallStatement(d); }
        // `call P(e);` against `call x, y := P(e);`: the first identifier is
        // the callee exactly when `(` follows it.
        std::vector<std::string> lhs;
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE,
                    "expected a procedure name or an out-parameter target after 'call'",
                    loc());
            return false;
        }
        std::string callee = tok_.text;
        eat();
        if (!isP("(")) {
            lhs.push_back(callee);
            while (isP(",")) {
                eat();
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected an out-parameter target",
                            loc());
                    return false;
                }
                lhs.push_back(tok_.text);
                eat();
            }
            if (!expectP(":=", d)) { return false; }
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected a procedure name after ':='",
                        loc());
                return false;
            }
            callee = tok_.text;
            eat();
        }
        if (!expectP("(", d)) { return false; }
        std::vector<H::ExprPtr> args;
        while (!isP(")")) {
            H::ExprPtr a = expr(d);
            if (!a) { return false; }
            args.push_back(a);
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(")", d) || !expectP(";", d)) { return false; }

        if (funs_.count(callee) != 0) {
            d.error(ErrorCode::E_TYPE,
                    "call target `" + callee + "` is a function, not a procedure",
                    loc());
            return false;
        }
        const auto pit = procs_.find(callee);
        if (pit == procs_.end()) {
            d.error(ErrorCode::E_TYPE,
                    "call target `" + callee + "` is not a declared procedure", loc());
            return false;
        }
        const ProcSig& sig = pit->second;
        if (args.size() != sig.in_names.size()) {
            d.error(ErrorCode::E_TYPE,
                    "'" + callee + "' takes " + std::to_string(sig.in_names.size())
                        + " in-parameter(s), not " + std::to_string(args.size()),
                    loc());
            return false;
        }
        if (lhs.size() != sig.out_names.size()) {
            d.error(ErrorCode::E_TYPE,
                    "'" + callee + "' returns " + std::to_string(sig.out_names.size())
                        + " out-parameter(s), not " + std::to_string(lhs.size()),
                    loc());
            return false;
        }
        for (std::size_t i = 0; i < args.size(); ++i) {
            if (!H::sameSort(args[i]->sort, sig.in_sorts[i])) {
                d.error(ErrorCode::E_TYPE,
                        "argument " + std::to_string(i + 1) + " of '" + callee
                            + "' is " + H::toString(args[i]->sort) + ", not "
                            + H::toString(sig.in_sorts[i]),
                        loc());
                return false;
            }
        }
        std::unordered_set<std::string> seen_lhs;
        for (const std::string& l : lhs) {
            if (sorts_.find(l) == sorts_.end()) {
                d.error(ErrorCode::E_TYPE, "'" + l + "' is not declared", loc());
                return false;
            }
            if (!seen_lhs.insert(l).second) {
                d.error(ErrorCode::E_TYPE,
                        "out-parameter target `" + l + "` appears twice in one call",
                        loc());
                return false;
            }
            if (!checkWritable(l, d)) { return false; }
        }
        // The callee's whole modifies set (checked and free) must lie inside
        // the caller's, or the caller's own frame is a lie.
        for (const std::string& g : sig.modifies_checked) {
            if (procedure_modifies_.count(g) == 0) {
                d.error(ErrorCode::E_TYPE,
                        "call to `" + callee + "` may modify global `" + g
                            + "`, which the enclosing procedure's modifies clause "
                              "does not permit",
                        loc());
                return false;
            }
        }
        for (const std::string& g : sig.modifies_free) {
            if (procedure_modifies_.count(g) == 0) {
                d.error(ErrorCode::E_TYPE,
                        "call to `" + callee + "` may modify global `" + g
                            + "`, which the enclosing procedure's modifies clause "
                              "does not permit",
                        loc());
                return false;
            }
        }

        // 1. Assert the checked preconditions, each its own refutation branch.
        if (!free_call) {
            bindCallFormals(sig, args, {});
            for (const std::string& n : sig.out_names) {
                contract_forbidden_.insert(n);
            }
            for (const ProcContract& c : sig.requires) {
                if (c.free_clause) { continue; }
                H::ExprPtr e = readContractClause(c, false, d);
                if (!e) { return false; }
                addObligation(e);
            }
            contract_forbidden_.clear();
            call_formals_.clear();
        }

        // 2. old(g) at this call site is g's pre-call version, for every
        //    global; computed before the havoc so the post-call clause can
        //    still name the entry state.
        for (const std::string& g : global_vars_) {
            old_overrides_[g] = H::mkIdent(current(g), global_sorts_.at(g));
        }
        // 3. Havoc the checked modifies; mint the out-targets' fresh versions.
        for (const std::string& g : sig.modifies_checked) {
            declare(fresh(g), global_sorts_.at(g));
        }
        std::vector<std::string> out_versions;
        for (const std::string& l : lhs) {
            out_versions.push_back(fresh(l));
            declare(out_versions.back(), sorts_.at(l));
        }
        // 4. Assume every postcondition (checked and free).
        bindCallFormals(sig, args, out_versions);
        for (const ProcContract& c : sig.ensures) {
            H::ExprPtr e = readContractClause(c, true, d);
            if (!e) { return false; }
            addAssume(e);
        }
        call_formals_.clear();
        old_overrides_.clear();

        if (!said_call_) {
            said_call_ = true;
            Uir::EncodingChoice ch;
            ch.site       = file_;
            ch.unified_op = "call";
            ch.strategy   = "contract-two-sided-no-inlining";
            ch.fidelity   = Uir::Fidelity::exact();
            ch.rationale =
                "a call asserts the callee's checked requires (each its own "
                "refutation branch), havocs its checked modifies globals and the "
                "out-parameter targets, and assumes every ensures with actuals "
                "substituted and old() resolved to the call-entry state; free "
                "requires are ignored by the caller and a free call skips the "
                "assertion (This is Boogie 2 §8.2/§9.9); the body is verified "
                "separately against the same contract";
            report_->addChoice(std::move(ch));
        }
        return true;
    }

    /** `call forall P(we, ...);` -- This is Boogie 2 §9.10. P must be a LEMMA
     *  procedure: no out-parameters and no checked modifies clause. The
     *  statement is exactly
     *
     *      assume (forall <wildcard formals> :: Pre ==> Post)
     *
     *  with Pre the conjunction of P's checked preconditions and Post the
     *  conjunction of all its postconditions (checked and free), the formals
     *  supplied at the call site substituted. A lemma modifies nothing, so
     *  `old(g)` in Post is g as the caller sees it -- the identity override. */
    bool callForallStatement(Uir::Diagnostics& d) {
        eat();                                    // 'forall'
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE,
                    "expected a procedure name after 'call forall'", loc());
            return false;
        }
        const std::string callee = tok_.text;
        eat();
        const auto pit = procs_.find(callee);
        if (pit == procs_.end()) {
            d.error(ErrorCode::E_TYPE,
                    "call target `" + callee + "` is not a declared procedure", loc());
            return false;
        }
        const ProcSig& sig = pit->second;
        if (!sig.out_names.empty() || !sig.modifies_checked.empty()) {
            d.error(ErrorCode::E_TYPE,
                    "call forall target `" + callee
                        + "` is not a lemma procedure: it has out-parameters or a "
                          "checked modifies clause (This is Boogie 2 §9.10)",
                    loc());
            return false;
        }
        if (!expectP("(", d)) { return false; }
        const std::size_t n = sig.in_names.size();
        std::vector<H::ExprPtr> args(n);
        std::vector<bool>        wild(n, false);
        std::size_t idx = 0;
        while (!isP(")")) {
            if (idx >= n) {
                d.error(ErrorCode::E_TYPE,
                        "'" + callee + "' takes " + std::to_string(n)
                            + " in-parameter(s), not more",
                        loc());
                return false;
            }
            if (isP("*")) {
                eat();
                wild[idx] = true;
            } else {
                args[idx] = expr(d);
                if (!args[idx]) { return false; }
                if (!H::sameSort(args[idx]->sort, sig.in_sorts[idx])) {
                    d.error(ErrorCode::E_TYPE,
                            "argument " + std::to_string(idx + 1) + " of '" + callee
                                + "' is " + H::toString(args[idx]->sort) + ", not "
                                + H::toString(sig.in_sorts[idx]),
                            loc());
                    return false;
                }
            }
            ++idx;
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(")", d) || !expectP(";", d)) { return false; }
        if (idx != n) {
            d.error(ErrorCode::E_TYPE,
                    "'" + callee + "' takes " + std::to_string(n)
                        + " in-parameter(s), not " + std::to_string(idx),
                    loc());
            return false;
        }
        // Wildcard formals become the bound variables of the assumed
        // quantification, alpha-renamed as quantifier() renames.
        std::vector<H::Binder> binders;
        std::vector<std::pair<std::string, bool>> shadowed;
        std::vector<H::Sort> previous;
        std::vector<std::string> previous_renamed;
        for (std::size_t i = 0; i < n; ++i) {
            if (!wild[i]) { call_formals_[sig.in_names[i]] = args[i]; continue; }
            const std::string& fn = sig.in_names[i];
            const auto old_it = bound_.find(fn);
            shadowed.emplace_back(fn, old_it != bound_.end());
            previous.push_back(old_it != bound_.end() ? old_it->second : H::Sort{});
            previous_renamed.push_back(old_it != bound_.end()
                                           ? renamed_binders_[fn]
                                           : std::string());
            H::Binder b;
            b.name = "q!" + std::to_string(qv_++) + "!" + fn;
            b.sort = sig.in_sorts[i];
            binders.push_back(b);
            bound_[fn] = b.sort;
            renamed_binders_[fn] = b.name;
        }
        for (const std::string& g : global_vars_) {
            old_overrides_[g] = H::mkIdent(current(g), global_sorts_.at(g));
        }
        H::ExprPtr pre;
        for (const ProcContract& c : sig.requires) {
            if (c.free_clause) { continue; }
            H::ExprPtr e = readContractClause(c, false, d);
            if (!e) { return false; }
            pre = conjoin(pre, e);
        }
        H::ExprPtr post;
        for (const ProcContract& c : sig.ensures) {
            H::ExprPtr e = readContractClause(c, true, d);
            if (!e) { return false; }
            post = conjoin(post, e);
        }
        call_formals_.clear();
        old_overrides_.clear();
        for (std::size_t i = shadowed.size(); i > 0; --i) {
            const auto& sh = shadowed[i - 1];
            if (sh.second) {
                bound_[sh.first] = previous[i - 1];
                renamed_binders_[sh.first] = previous_renamed[i - 1];
            } else {
                bound_.erase(sh.first);
                renamed_binders_.erase(sh.first);
            }
        }
        if (!post) { return true; }              // a lemma that says nothing
        H::ExprPtr clause = pre ? H::mkOp(H::Op::IMPLIES, {pre, post}) : post;
        if (!binders.empty()) { clause = H::mkForall(binders, clause); }
        addAssume(clause);
        return true;
    }

    /** Collect the names a block assigns, and leave the lexer past it.
     *
     *  Scanned lexically rather than declared, because Boogie infers a loop's
     *  targets and a source file never writes them down. `x := e` and
     *  `x[i] := e` both assign x -- a map write is a write to the map -- and
     *  `havoc x` is one too. A parallel assignment `x, y := e, f` assigns
     *  BOTH: a target is an identifier followed by `:=` OR by `,`, and the
     *  first form alone used to be collected, so a loop whose body swapped two
     *  variables in parallel kept the first one's value across iterations --
     *  the unsoundness §4.3's havoc exists to prevent. A `call` assigns its
     *  out-targets and, through the callee's contract, the callee's checked
     *  modifies globals -- exactly the set the call itself havoc's. */
    void scanTargetsAndSkipBlock(std::vector<std::string>& targets) {
        int depth = 0;
        for (;;) {
            if (tok_.kind == Token::END) { return; }
            if (isP("{")) { ++depth; eat(); continue; }
            if (isP("}")) {
                eat();
                if (--depth == 0) { return; }
                continue;
            }
            if (is("havoc")) {
                eat();
                while (tok_.kind == Token::IDENT) {
                    targets.push_back(tok_.text);
                    eat();
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                continue;
            }
            if (is("call")) {
                eat();
                // A call may carry attributes; skip them token-wise.
                while (isP("{")) {
                    int bd = 0;
                    do {
                        if (tok_.kind == Token::END) { return; }
                        if (isP("{")) { ++bd; }
                        else if (isP("}")) { --bd; }
                        eat();
                    } while (bd > 0);
                }
                if (is("forall")) { eat(); }
                if (tok_.kind == Token::IDENT) {
                    const std::string first = tok_.text;
                    eat();
                    std::string callee = first;
                    if (!isP("(")) {
                        // `call x, y := P(...)`: out-targets, then the callee.
                        targets.push_back(first);
                        while (isP(",")) {
                            eat();
                            if (tok_.kind == Token::IDENT) {
                                targets.push_back(tok_.text);
                                eat();
                            }
                        }
                        if (isP(":=")) { eat(); }
                        if (tok_.kind == Token::IDENT) {
                            callee = tok_.text;
                            eat();
                        }
                    }
                    const auto it = procs_.find(callee);
                    if (it != procs_.end()) {
                        for (const std::string& g : it->second.modifies_checked) {
                            targets.push_back(g);
                        }
                    }
                }
                // The rest of the statement is argument expressions.
                int pd = 0;
                while (tok_.kind != Token::END) {
                    if (pd == 0 && isP(";")) { eat(); break; }
                    if (isP("(") || isP("[") || isP("{")) { ++pd; }
                    else if (isP(")") || isP("]") || isP("}")) { --pd; }
                    eat();
                }
                continue;
            }
            if (is("assume") || is("assert") || is("return") || is("goto")
                || is("break")) {
                // No assignment targets; the expression or label list may hold
                // commas (a quantifier's binders, a goto's targets), so skip
                // the whole statement rather than misread one as a target.
                int pd = 0;
                while (tok_.kind != Token::END) {
                    if (pd == 0 && isP(";")) { eat(); break; }
                    if (isP("(") || isP("[") || isP("{")) { ++pd; }
                    else if (isP(")") || isP("]") || isP("}")) { --pd; }
                    eat();
                }
                continue;
            }
            if (tok_.kind == Token::IDENT) {
                const std::string n = tok_.text;
                eat();
                int br = 0;
                while (isP("[")) {                 // `a[i]`, `a[i][j]`
                    ++br;
                    eat();
                    while (br > 0 && tok_.kind != Token::END) {
                        if (isP("[")) { ++br; }
                        else if (isP("]")) { --br; }
                        eat();
                    }
                }
                if (isP(":=") || isP(",")) { targets.push_back(n); }
                continue;
            }
            eat();
        }
    }

    /**
     * `while (c) invariant I; { body }` -- the INVARIANT strategy of
     * `boogie.md` §4.3, which is Boogie's own and the one the corpus is
     * annotated for.
     *
     * The question the output then answers is "is the program correct GIVEN
     * that the invariant holds", and the invariant is VERIFIED as part of it
     * rather than assumed for free. Three parts, in the order a reader of the
     * source would check them:
     *
     *   1. ENTRY -- I holds when the loop is first reached.
     *   2. PRESERVATION -- if I holds and the guard is true, I holds again
     *      after one pass of the body.
     *   3. everything after the loop is verified from an ARBITRARY exited
     *      iteration, not from the entry state.
     *
     * (3) is what the havoc is for. Every variable the body assigns takes a
     * fresh SSA version before the loop is reasoned about, so nothing after
     * the loop may rely on a value the entry state happened to have. Omitting
     * it is the classic unsound loop encoding: the code after the loop would
     * be verified against the state before it ran.
     *
     * **The guard and the invariants are RE-PARSED at each point they are
     * needed.** `expr()` resolves an identifier to its current SSA version at
     * parse time, so a formula parsed once is a statement about one state; the
     * invariant has to be a statement about three. This is the same re-parse
     * the lexer's Mark exists for elsewhere in this file.
     *
     * The body's effects do not flow past the loop: it is generated to
     * discharge (2), and the version map is then restored so the continuation
     * reads the havoc'd versions. The body's fresh names stay declared and
     * their defining assumes stay, guarded by the loop condition, which is
     * harmless because nothing after the loop refers to them.
     *
     * A `break` (plain, or naming this loop) is one more edge into the
     * continuation: it leaves from the body's PRESERVATION state, so the
     * continuation joins exit-edge and break edges with gate booleans, the
     * same discipline a label with several incoming edges uses. A path that
     * breaks owes no invariant preservation: it never reaches the back edge,
     * exactly as This is Boogie 2 §9.5's desugaring (`break` is a goto to the
     * loop's Done) makes it.
     *
     * `exact()`, and no bound. The invariant is checked rather than trusted, so
     * this is not an approximation. What the result is relative to is the
     * ANNOTATION -- a weak invariant proves a weak property -- and that is a
     * property of the input, not of the encoding.
     */
    bool whileStatement(Uir::Diagnostics& d) {
        eat();                                    // 'while'
        // `L: while ...` makes L a `break L` target; the plain `break` entry
        // (empty label) is the innermost-while rule of This is Boogie 2 §9.5.
        std::vector<PendingEdge> break_edges;
        std::size_t breakables_added = 0;
        for (const std::string& l : pending_labels_) {
            breakables_.push_back(Breakable{l, true, &break_edges});
            ++breakables_added;
        }
        breakables_.push_back(Breakable{"", true, &break_edges});
        ++breakables_added;
        pending_labels_.clear();
        const H::ExprPtr guard_before_body = path_guard_;
        if (!expectP("(", d)) { return false; }
        // `while (*)` is Boogie's nondeterministic guard: the loop may exit at
        // any iteration, so there is no condition to assume in either
        // direction and the body is generated unguarded.
        bool star = false;
        Mark guard_mark = mark();
        if (isP("*")) {
            eat();
            star = true;
        } else {
            guard_mark = mark();
            H::ExprPtr probe = expr(d);           // parsed once to get past it
            if (!probe) { return false; }
        }
        if (!expectP(")", d)) { return false; }

        std::vector<Mark> invariants;             // checked
        std::vector<Mark> free_invariants;        // assumed, never checked
        while (is("invariant") || is("free")) {
            const bool is_free = is("free");
            eat();
            if (is_free) {
                if (!is("invariant")) {
                    d.error(ErrorCode::E_PARSE, "expected 'invariant' after 'free'",
                            loc());
                    return false;
                }
                eat();
            }
            if (!attributes(d)) { return false; }
            const Mark m = mark();
            H::ExprPtr probe = expr(d);
            if (!probe || !expectP(";", d)) { return false; }
            // A `free invariant` is a hypothesis, not an obligation: Boogie
            // assumes it and does not check it. Assuming one that does not hold
            // is how a loop encoding goes quietly wrong, so the two lists stay
            // apart rather than being merged with a flag.
            (is_free ? free_invariants : invariants).push_back(m);
        }
        if (!isP("{")) {
            d.error(ErrorCode::E_PARSE, "expected a loop body", loc());
            return false;
        }

        // Re-reads a marked formula against the CURRENT version map.
        const auto readAt = [&](const Mark& m, H::ExprPtr& out) -> bool {
            const Mark here = mark();
            reset(m);
            out = expr(d);
            reset(here);
            return out != nullptr;
        };

        // 1. ENTRY: an obligation in the state before the loop.
        for (const Mark& m : invariants) {
            H::ExprPtr inv;
            if (!readAt(m, inv)) { return false; }
            addObligation(inv);
        }

        // 2. The loop is reasoned about in TWO havoc'd states, and neither
        //    state's assumptions may become global constraints.
        //
        //    Preservation is checked where the guard is TRUE, the continuation
        //    reasoned about where it is FALSE. Those are different paths, and a
        //    conjunction cannot hold two paths: assume both and the script is
        //    unsatisfiable, which this encoding reads as "verified". A loop with
        //    a plainly broken invariant then verifies --
        //
        //        i := 0; while (i < 10) invariant i <= 5; { i := i + 1; }
        //
        //    -- because `i <= 5` and `i >= 10` cannot both hold, so the whole
        //    query is UNSAT and the preservation failure never surfaces.
        //
        //    So preservation becomes ONE self-contained implication, with its
        //    own assumptions as the antecedent, and the exit state's
        //    assumptions become a path guard on everything after the loop
        //    rather than a constraint on everything at all.
        const Mark body_start = mark();
        std::vector<std::string> targets;
        scanTargetsAndSkipBlock(targets);
        const Mark after_body = mark();

        const auto havoc = [&]() {
            for (const std::string& n : targets) {
                const auto it = sorts_.find(n);
                if (it == sorts_.end()) { continue; }   // a local of an inner scope
                declare(fresh(n), it->second);
            }
        };
        // The invariants and the free invariants, read against the current
        // version map. Free ones are assumed and never checked, which is the
        // whole of what `free` means.
        const auto readAllInvariants = [&](H::ExprPtr& out) -> bool {
            for (const Mark& m : invariants) {
                H::ExprPtr inv;
                if (!readAt(m, inv)) { return false; }
                out = conjoin(out, inv);
            }
            for (const Mark& m : free_invariants) {
                H::ExprPtr inv;
                if (!readAt(m, inv)) { return false; }
                out = conjoin(out, inv);
            }
            return true;
        };

        // 3. PRESERVATION, entirely inside one implication.
        havoc();
        H::ExprPtr pres_ante;
        if (!readAllInvariants(pres_ante)) { return false; }
        if (!star) {
            H::ExprPtr cond;
            if (!readAt(guard_mark, cond)) { return false; }
            pres_ante = conjoin(pres_ante, cond);
        }
        // The head context -- invariants and guard -- is what holds where the
        // body runs; an edge escaping the body (a `break`, a `goto` out of
        // the loop) must carry it, or the escape's state is unconstrained
        // havoc and the continuation would see states the loop excludes.
        while_body_contexts_.push_back(pres_ante);
        {
            // The body's own assumes belong to this path too, so they are
            // spliced out of the model and folded into the antecedent. Left
            // global they would constrain the continuation with a state it
            // never reaches.
            const std::size_t first = model_->constraints.size();
            const std::size_t first_obl = obligations_.size();
            reset(body_start);
            if (!statementList(d, true)) { return false; }
            while_body_contexts_.pop_back();
            for (std::size_t i = breakables_added; i > 0; --i) {
                breakables_.pop_back();
            }
            for (std::size_t i = first; i < model_->constraints.size(); ++i) {
                pres_ante = conjoin(pres_ante, model_->constraints[i].formula);
            }
            model_->constraints.resize(first);
            // An `assert` inside the body is an obligation on this path.
            for (std::size_t i = first_obl; i < obligations_.size(); ++i) {
                obligations_[i].formula = pres_ante
                    ? H::mkOp(H::Op::IMPLIES,
                              {pres_ante, obligations_[i].formula})
                    : obligations_[i].formula;
                // The body's assumptions now live inside pres_ante and were
                // removed from the model, so this obligation's external
                // prefix ends where the loop body started.
                obligations_[i].prefix_end = first;
            }
            H::ExprPtr pres_post;
            for (const Mark& m : invariants) {
                H::ExprPtr inv;
                if (!readAt(m, inv)) { return false; }
                pres_post = conjoin(pres_post, inv);
            }
            if (pres_post) {
                // Only a path that COMPLETES the body owes the invariant: one
                // that left via `return` or `break` is not an iteration. That
                // is already the encoding's own discipline -- the body-end
                // path guard is the completion condition and addObligation
                // wraps the obligation in it.
                addObligation(pres_ante
                                  ? H::mkOp(H::Op::IMPLIES, {pres_ante, pres_post})
                                  : pres_post);
            }
            path_guard_ = guard_before_body;
        }

        // 4. THE CONTINUATION: the invariant holds, the guard does not, and
        //    both guard what follows instead of constraining what precedes.
        //    `while (*)` exits nondeterministically and assumes no guard.
        havoc();
        H::ExprPtr exit_ante;
        if (!readAllInvariants(exit_ante)) { return false; }
        if (!star) {
            H::ExprPtr cond;
            if (!readAt(guard_mark, cond)) { return false; }
            exit_ante = conjoin(exit_ante, H::mkOp(H::Op::NOT, {cond}));
        }
        if (break_edges.empty()) {
            if (exit_ante) { path_guard_ = conjoin(path_guard_, exit_ante); }
        } else {
            // `break` exits are edges into the continuation too: they come
            // from the body's PRESERVATION state, so their guards are not
            // exclusive with the exit edge's -- a gated join (as at a label).
            std::vector<PendingEdge> edges;
            edges.push_back(PendingEdge{exit_ante, version_});
            for (PendingEdge& e : break_edges) { edges.push_back(std::move(e)); }
            joinEdges(edges, /*gated=*/true);
            path_guard_ = conjoin(guard_before_body, path_guard_);
        }
        reset(after_body);
        return true;
    }

    // ---- The body pre-scan ---------------------------------------------------

    /** A segment of a statement list for the pre-scan: a maximal run between
     *  labels and transfer commands. A `while` or `if` folds into the segment
     *  as one node; its assigned variables count as the segment's. */
    struct ScanSeg {
        std::string label;                          // "" if unlabeled
        std::size_t first_pos = 0;
        std::vector<std::string> assigned;          // incl. nested constructs'
        std::vector<std::pair<std::size_t, std::string>> edges;  // (goto pos, target)
        bool ends_transfer = false;                 // goto/return/break at the end
        bool dead = false;                          // unreachable by fall-through
    };
    struct GotoRecord {
        std::vector<std::size_t> chain;             // enclosing list ids, outer first
        std::size_t pos = 0;                        // the goto token's position
        int line = 0;                               // its line, for diagnostics
        std::vector<std::string> targets;
    };
    struct ScanListBuild {
        LabelScan scan;
        std::vector<ScanSeg> segs;
    };

    /** One simple statement's assigned targets, consumed through its `;`.
     *  The same lexical rules as scanTargetsAndSkipBlock: `:=` or `,` after an
     *  identifier means an assignment target, and a call adds its out-targets
     *  and the callee's checked modifies. */
    bool scanSimpleStatement(Uir::Diagnostics& d,
                             std::vector<std::string>& targets) {
        if (is("assume") || is("assert") || is("return")) {
            eat();
            return skipExpression(d) && expectP(";", d);
        }
        if (is("var")) {
            eat();
            return skipExpression(d) && expectP(";", d);
        }
        if (is("havoc")) {
            eat();
            while (tok_.kind == Token::IDENT) {
                targets.push_back(tok_.text);
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            return expectP(";", d);
        }
        if (is("async")) {
            if (inference_calls_ != nullptr) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'async call' requires concurrent semantics; infer_modifies "
                        "does not turn it into a synchronous call", loc());
                return false;
            }
            eat();
        }
        if (is("free")) { eat(); }
        if (is("call")) {
            eat();
            while (isP("{")) {                    // attributes, token-wise
                int bd = 0;
                do {
                    if (tok_.kind == Token::END) { return true; }
                    if (isP("{")) { ++bd; }
                    else if (isP("}")) { --bd; }
                    eat();
                } while (bd > 0);
            }
            if (is("forall")) { eat(); }
            if (tok_.kind == Token::IDENT) {
                const std::string first_name = tok_.text;
                eat();
                std::string callee = first_name;
                if (!isP("(")) {
                    targets.push_back(first_name);
                    while (isP(",")) {
                        eat();
                        if (tok_.kind == Token::IDENT) {
                            targets.push_back(tok_.text);
                            eat();
                        }
                    }
                    if (isP(":=")) { eat(); }
                    if (tok_.kind == Token::IDENT) {
                        callee = tok_.text;
                        eat();
                    }
                }
                const auto it = procs_.find(callee);
                if (inference_calls_ != nullptr) {
                    inference_calls_->insert(callee);
                } else if (it != procs_.end()) {
                    for (const std::string& g : it->second.modifies_checked) {
                        targets.push_back(g);
                    }
                }
            }
            // the arguments
            int pd = 0;
            while (tok_.kind != Token::END) {
                if (pd == 0 && isP(";")) { break; }
                if (isP("(") || isP("[") || isP("{")) { ++pd; }
                else if (isP(")") || isP("]") || isP("}")) { --pd; }
                eat();
            }
            return expectP(";", d);
        }
        // An assignment: IDENT [brackets] (`,` ...)* `:=` exprs `;`.
        for (;;) {
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected an assignment target", loc());
                return false;
            }
            targets.push_back(tok_.text);
            eat();
            int br = 0;
            while (isP("[")) {                 // `a[i]`, `a[i][j]`
                ++br;
                eat();
                while (br > 0 && tok_.kind != Token::END) {
                    if (isP("[")) { ++br; }
                    else if (isP("]")) { --br; }
                    eat();
                }
            }
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(":=", d)) { return false; }
        // The right-hand sides: a comma-separated expression list.
        int pd = 0;
        while (tok_.kind != Token::END) {
            if (pd == 0 && isP(";")) { break; }
            if (isP("(") || isP("[") || isP("{")) { ++pd; }
            else if (isP(")") || isP("]") || isP("}")) { --pd; }
            eat();
        }
        return expectP(";", d);
    }

    /** The guard `( c )` or `( * )` of an if/while, consumed. */
    bool scanGuard(Uir::Diagnostics& d) {
        if (!expectP("(", d)) { return false; }
        int depth = 1;
        while (depth > 0) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated guard", loc());
                return false;
            }
            if (isP("(")) { ++depth; }
            else if (isP(")")) { --depth; }
            eat();
        }
        return true;
    }

    /** The `{`-list walk of the pre-scan. tok_ is at `{`; the call consumes
     *  through the matching `}`. */
    bool scanList(Uir::Diagnostics& d, bool in_while_body,
                  std::vector<std::string>& assigned_out) {
        const std::size_t list_id = tok_.pos;
        list_while_[list_id] = in_while_body;
        scan_stack_.push_back(list_id);
        ScanListBuild& build = scan_builds_[list_id];
        eat();                                       // '{'
        ScanSeg cur;
        cur.first_pos = tok_.pos;
        auto closeSeg = [&]() {
            build.segs.push_back(cur);
            cur = ScanSeg();
            cur.first_pos = tok_.pos;
            cur.dead = true;    // a segment is born dead until a label names it
        };
        while (!isP("}")) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated block", loc());
                return false;
            }
            if (is("if")) {
                if (!scanIf(d, cur.assigned)) { return false; }
                continue;
            }
            if (is("while")) {
                if (!scanWhile(d, cur.assigned)) { return false; }
                continue;
            }
            if (is("goto")) {
                GotoRecord rec;
                rec.chain = scan_stack_;
                rec.pos = tok_.pos;
                rec.line = tok_.line;
                eat();
                while (tok_.kind == Token::IDENT) {
                    rec.targets.push_back(tok_.text);
                    eat();
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (rec.targets.empty()) {
                    d.error(ErrorCode::E_PARSE, "goto requires at least one label",
                            loc());
                    return false;
                }
                if (!expectP(";", d)) { return false; }
                for (const std::string& t : rec.targets) {
                    cur.edges.emplace_back(rec.pos, t);
                }
                scan_gotos_.push_back(std::move(rec));
                closeSeg();
                continue;
            }
            if (is("break")) {
                eat();
                bool saw_label = false;
                if (tok_.kind == Token::IDENT) { saw_label = true; eat(); }
                if (!expectP(";", d)) { return false; }
                // A plain break needs an enclosing while body (This is Boogie
                // 2 §9.5); the labeled form's target is resolved at
                // processing time, where the breakables stack knows kinds.
                bool in_loop = false;
                for (std::size_t l : scan_stack_) {
                    if (list_while_[l]) { in_loop = true; break; }
                }
                if (!in_loop && !saw_label) {
                    d.error(ErrorCode::E_TYPE, "`break` outside a loop", loc());
                    return false;
                }
                closeSeg();
                continue;
            }
            // A label: `L:` -- a new segment starts here, live.
            if (tok_.kind == Token::IDENT && lex_.peekIsColon()
                && !lex_.peekIsAssign()) {
                const std::string name = tok_.text;
                const std::size_t pos = tok_.pos;
                eat();
                eat();                               // ':'
                if (!body_scan_.label_list.emplace(name, list_id).second) {
                    d.error(ErrorCode::E_TYPE,
                            "label `" + name
                                + "` is declared more than once in this procedure body",
                            loc());
                    return false;
                }
                build.scan.label_pos[name] = pos;
                // The leading run of asserts after the label: at a loop
                // header these are the invariants (the reference turns the
                // header's assert prefix into the invariant set,
                // RemoveBackEdges.cs). Collected for every label; used only
                // for backward-goto targets.
                std::vector<Mark> asserts;
                while (is("assert")) {
                    eat();
                    if (!attributes(d)) { return false; }
                    asserts.push_back(mark());
                    if (!skipExpression(d) || !expectP(";", d)) { return false; }
                }
                if (!asserts.empty()) {
                    build.scan.label_asserts[name] = std::move(asserts);
                }
                closeSeg();
                cur.label = name;
                cur.first_pos = pos;
                cur.dead = false;
                continue;
            }
            if (!scanSimpleStatement(d, cur.assigned)) { return false; }
        }
        eat();                                       // '}'
        // The last segment falls out of the list (no successor here). Every
        // segment's assigned set propagates to the parent: a nested statement
        // is one node in it.
        build.segs.push_back(cur);
        for (const ScanSeg& sg : build.segs) {
            assigned_out.insert(assigned_out.end(), sg.assigned.begin(),
                                sg.assigned.end());
        }
        scan_stack_.pop_back();
        return true;
    }

    bool scanIf(Uir::Diagnostics& d, std::vector<std::string>& assigned_out) {
        eat();                                       // 'if'
        if (!scanGuard(d)) { return false; }
        if (!scanList(d, false, assigned_out)) { return false; }
        if (is("else")) {
            eat();
            if (is("if")) { return scanIf(d, assigned_out); }
            if (!scanList(d, false, assigned_out)) { return false; }
        }
        return true;
    }

    bool scanWhile(Uir::Diagnostics& d, std::vector<std::string>& assigned_out) {
        eat();                                       // 'while'
        if (!scanGuard(d)) { return false; }
        while (is("invariant") || is("free")) {
            const bool is_free = is("free");
            eat();
            if (is_free) {
                if (!is("invariant")) {
                    d.error(ErrorCode::E_PARSE, "expected 'invariant' after 'free'",
                            loc());
                    return false;
                }
                eat();
            }
            if (!skipExpression(d) || !expectP(";", d)) { return false; }
        }
        return scanList(d, true, assigned_out);
    }

    /** The whole pre-scan: walk the body, classify every goto, compute the
     *  cycle havoc sets. Purely syntactic; runs before any statement is
     *  processed, and refuses what the encoding does not support BY NAME. */
    bool scanBody(Uir::Diagnostics& d) {
        body_scan_ = BodyScan();
        scan_builds_.clear();
        scan_gotos_.clear();
        list_while_.clear();
        scan_stack_.clear();
        std::vector<std::string> sink;
        if (!scanList(d, false, sink)) { return false; }
        return classifyGotos(d);
    }

    bool classifyGotos(Uir::Diagnostics& d) {
        Uir::SourceLoc at;
        for (const GotoRecord& rec : scan_gotos_) {
            at.file = file_;
            at.line = rec.line;
            for (const std::string& t : rec.targets) {
                const auto lit = body_scan_.label_list.find(t);
                if (lit == body_scan_.label_list.end()) {
                    // This is Boogie 2 §9.5: the labels listed in a goto must
                    // all be defined in the same implementation body.
                    d.error(ErrorCode::E_TYPE,
                            "goto target `" + t
                                + "` is not a label in this procedure body",
                            at);
                    return false;
                }
                const std::size_t owner = lit->second;
                int up = -1;
                for (int i = static_cast<int>(rec.chain.size()) - 1; i >= 0; --i) {
                    if (rec.chain[i] == owner) { up = i; break; }
                }
                if (up < 0) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a `goto` into a structured statement's body is not "
                            "implemented: control flow is joined at construct "
                            "boundaries",
                            at);
                    return false;
                }
                const bool backward =
                    scan_builds_[owner].scan.label_pos[t] <= rec.pos;
                if (backward) {
                    for (std::size_t i = up + 1; i < rec.chain.size(); ++i) {
                        if (list_while_[rec.chain[i]]) {
                            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                    "a `goto` that loops back across a `while` "
                                    "boundary is not implemented: the `while`'s "
                                    "checked-invariant encoding and a goto loop's "
                                    "implicit-true-invariant cut do not compose; "
                                    "write the loop as one construct",
                                    at);
                            return false;
                        }
                    }
                }
                if (up != static_cast<int>(rec.chain.size()) - 1) {
                    // An escape edge re-homes into the ancestor list's graph,
                    // at the segment containing the child construct.
                    const std::size_t child = rec.chain[up + 1];
                    ScanListBuild& b = scan_builds_[owner];
                    std::size_t seg = 0;
                    for (std::size_t i = 0; i < b.segs.size(); ++i) {
                        if (b.segs[i].first_pos <= child) { seg = i; }
                    }
                    b.segs[seg].edges.emplace_back(rec.pos, t);
                }
            }
        }
        // Cycles per list: every lexical-back edge's target is a header, and
        // the havoc set is what the cycle's segments assign.
        for (auto& kv : scan_builds_) {
            computeLoops(kv.second);
        }
        // Keep only what the processing reads.
        for (auto& kv : scan_builds_) { body_scan_.lists[kv.first] = kv.second.scan; }
        return true;
    }

    void computeLoops(ScanListBuild& b) {
        const std::size_t n = b.segs.size();
        if (n == 0) { return; }
        // label -> segment index
        std::unordered_map<std::string, std::size_t> seg_of;
        for (std::size_t i = 0; i < n; ++i) {
            if (!b.segs[i].label.empty()) { seg_of[b.segs[i].label] = i; }
        }
        // adjacency: fall-through and goto edges (local targets only)
        std::vector<std::vector<std::size_t>> succ(n);
        for (std::size_t i = 0; i < n; ++i) {
            if (!b.segs[i].dead && !b.segs[i].ends_transfer && i + 1 < n) {
                succ[i].push_back(i + 1);
            }
            for (const auto& e : b.segs[i].edges) {
                const auto it = seg_of.find(e.second);
                if (it != seg_of.end()) { succ[i].push_back(it->second); }
            }
        }
        const auto reaches = [&](std::size_t from) {
            std::vector<bool> r(n, false);
            std::vector<std::size_t> wl{from};
            r[from] = true;
            while (!wl.empty()) {
                const std::size_t x = wl.back();
                wl.pop_back();
                for (const std::size_t s : succ[x]) {
                    if (!r[s]) { r[s] = true; wl.push_back(s); }
                }
            }
            return r;
        };
        for (std::size_t i = 0; i < n; ++i) {
            for (const auto& e : b.segs[i].edges) {
                const auto it = seg_of.find(e.second);
                if (it == seg_of.end()) { continue; }
                const std::size_t h = it->second;
                if (b.scan.label_pos[e.second] > e.first) { continue; }  // forward
                // The natural loop of the back edge i -> h: the segments on
                // some path h ~> i.
                const std::vector<bool> from_h = reaches(h);
                std::vector<bool> to_i(n, false);
                {
                    std::vector<std::size_t> wl{i};
                    to_i[i] = true;
                    while (!wl.empty()) {
                        const std::size_t x = wl.back();
                        wl.pop_back();
                        for (std::size_t p = 0; p < n; ++p) {
                            if (!to_i[p]
                                && std::find(succ[p].begin(), succ[p].end(), x)
                                       != succ[p].end()) {
                                to_i[p] = true;
                                wl.push_back(p);
                            }
                        }
                    }
                }
                std::vector<std::string>& havoc = b.scan.header_havoc[e.second];
                for (std::size_t j = 0; j < n; ++j) {
                    if (from_h[j] && to_i[j]) {
                        havoc.insert(havoc.end(), b.segs[j].assigned.begin(),
                                     b.segs[j].assigned.end());
                    }
                }
            }
        }
    }

    // ---- Control flow: lists, labels, joins, gotos, breaks -------------------

    /** The guard an edge carries: the path condition in force, PLUS -- when
     *  inside a `while` body -- the body's constraints so far, as an
     *  expression. The body's constraints leave the model at the body's end
     *  (they fold into the preservation antecedent), so an edge that outlives
     *  the body must be self-contained. */
    H::ExprPtr edgeGuard() {
        H::ExprPtr g = path_guard_;
        // The head context of every enclosing loop -- the invariants and the
        // guard, which is what holds where the body runs. Without it an
        // escaping edge's state would be unconstrained havoc.
        for (const H::ExprPtr& ctx : while_body_contexts_) {
            g = conjoin(g, ctx);
        }
        if (!while_body_starts_.empty()) {
            // ...and the body's own constraints so far, which leave the model
            // at the body's end (folded into the preservation antecedent).
            for (std::size_t i = while_body_starts_.front();
                 i < model_->constraints.size(); ++i) {
                g = conjoin(g, model_->constraints[i].formula);
            }
        }
        return g;
    }

    /** The join of N edges at one point.
     *
     *  With EXCLUSIVE edge guards (an if's two branch guards, or break edges
     *  built from branch conditions) the ite keys are the guards themselves.
     *  Arbitrary goto edges are NOT exclusive -- two guards can hold in one
     *  model and the ite would pick the wrong path's value -- so each edge
     *  gets a fresh GATE boolean: the gate implies its source guard (an edge
     *  cannot be claimed infeasible), and the model is always free to set
     *  exactly the taken one. */
    void joinEdges(const std::vector<PendingEdge>& edges, bool gated) {
        // The join's constraints are DEFINITIONAL -- they hold in every state,
        // not only on the path that happens to be in force when the join is
        // emitted (which is the LAST incoming edge's guard). Emitting them
        // under that guard would make the joined version free on every other
        // path, so they are emitted raw.
        const H::ExprPtr saved_guard = path_guard_;
        path_guard_ = nullptr;
        std::vector<H::ExprPtr> keys;
        for (const PendingEdge& e : edges) {
            H::ExprPtr key = e.guard;
            if (gated) {
                const std::string g = "edge!" + std::to_string(edge_++);
                declare(g, H::Sort::boolean());
                key = H::mkIdent(g, H::Sort::boolean(), loc());
                if (e.guard) { addAssume(H::mkOp(H::Op::IMPLIES, {key, e.guard})); }
            }
            keys.push_back(key ? key : H::mkBool(true, loc()));
        }
        std::unordered_map<std::string, unsigned> joined;
        std::unordered_set<std::string> names;
        for (const PendingEdge& e : edges) {
            for (const auto& kv : e.versions) { names.insert(kv.first); }
        }
        for (const std::string& n : names) {
            std::vector<unsigned> vs;
            vs.reserve(edges.size());
            bool same = true;
            for (const PendingEdge& e : edges) {
                const auto vit = e.versions.find(n);
                vs.push_back(vit == e.versions.end() ? 0 : vit->second);
                if (vs.back() != vs.front()) { same = false; }
            }
            if (same) {
                if (vs.front() > 1) { joined[n] = vs.front(); }
                continue;
            }
            const auto sit = sorts_.find(n);
            if (sit == sorts_.end()) { continue; }   // declared only in dead code
            const H::Sort s = sit->second;
            const unsigned nv = ++mint_[n];
            const std::string jn = versionName(n, nv);
            joined[n] = nv;
            declare(jn, s);
            H::ExprPtr chain = H::mkIdent(versionName(n, vs.back()), s);
            for (std::size_t i = edges.size() - 1; i-- > 0;) {
                chain = H::mkOp(H::Op::ITE,
                                {keys[i], H::mkIdent(versionName(n, vs[i]), s), chain});
            }
            addAssume(H::mkOp(H::Op::EQ, {H::mkIdent(jn, s), chain}));
        }
        version_ = std::move(joined);
        H::ExprPtr g = keys.front();
        for (std::size_t i = 1; i < keys.size(); ++i) {
            g = H::mkOp(H::Op::OR, {g, keys[i]});
        }
        (void)saved_guard;
        path_guard_ = g;
    }

    /** A brace-delimited statement list: the unit on which labels (and thus
     *  joins and gotos) live. */
    bool statementList(Uir::Diagnostics& d, bool in_while_body) {
        const std::size_t list_id = tok_.pos;      // the '{'
        const LabelScan* scan = nullptr;
        const auto sit = body_scan_.lists.find(list_id);
        if (sit != body_scan_.lists.end()) { scan = &sit->second; }
        frames_.push_back(ListFrame{list_id, scan, {}, in_while_body});
        if (in_while_body) {
            while_body_starts_.push_back(model_->constraints.size());
        }
        bool ok = true;
        if (!expectP("{", d)) { ok = false; }
        while (ok && !isP("}")) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated block", loc());
                ok = false;
                break;
            }
            // A label: `L:` -- a join point, maybe a loop header.
            if (tok_.kind == Token::IDENT && lex_.peekIsColon()
                && !lex_.peekIsAssign()) {
                if (!labelStatement(d)) { ok = false; }
                continue;
            }
            if (!statement(d)) { ok = false; }
        }
        if (ok) { eat(); }                         // '}'
        if (in_while_body) { while_body_starts_.pop_back(); }
        frames_.pop_back();
        return ok;
    }

    /** `L:` -- the fall-through edge joins the recorded goto edges.
     *
     *  A backward goto's target is a LOOP HEADER: the reference cuts back
     *  edges, havoc's what the cycle assigns, and treats a missing invariant
     *  as `true` (RemoveBackEdges.cs), which is also exactly what a
     *  no-invariant `while` degrades to here. The havoc set comes from the
     *  pre-scan, because at the header no back edge has been seen yet. */
    bool labelStatement(Uir::Diagnostics& d) {
        const std::string name = tok_.text;
        eat();                                       // the identifier
        if (!expectP(":", d)) { return false; }
        ListFrame& frame = frames_.back();
        if (!dead_) {
            frame.edges[name].push_back(PendingEdge{path_guard_, version_});
        }
        std::vector<PendingEdge> edges;
        const auto eit = frame.edges.find(name);
        if (eit != frame.edges.end()) {
            edges = std::move(eit->second);
            frame.edges.erase(eit);
        }
        if (edges.empty()) {
            // Nothing jumps here and the fall-through is dead: unreachable,
            // until another label is reached.
            dead_ = true;
            path_guard_ = nullptr;
        } else if (edges.size() == 1) {
            dead_ = false;
            version_ = edges.front().versions;
            path_guard_ = edges.front().guard;
        } else {
            dead_ = false;
            joinEdges(edges, /*gated=*/true);
        }
        if (!dead_ && frame.scan != nullptr) {
            const auto hit = frame.scan->header_havoc.find(name);
            if (hit != frame.scan->header_havoc.end()) {
                // A backward goto's target is a LOOP HEADER. The reference
                // (RemoveBackEdges.cs) turns the header block's leading run
                // of `assert`s into the loop's invariants: asserted on entry
                // and at each back edge, assumed at the head. No asserts, no
                // invariants -- the implicit `true` of the plain cut.
                const std::vector<Mark>* invs = nullptr;
                const auto ait = frame.scan->label_asserts.find(name);
                if (ait != frame.scan->label_asserts.end()) { invs = &ait->second; }
                // 1. ENTRY: the invariants are obligations of the joined
                //    pre-havoc state (every non-back edge into the header).
                if (invs != nullptr) {
                    for (const Mark& m : *invs) {
                        H::ExprPtr inv = readMarkedExpr(m, d);
                        if (!inv) { return false; }
                        addObligation(inv);
                    }
                }
                // 2. The havoc: the cycle's assignments are arbitrary from
                //    here (the cut).
                for (const std::string& n : hit->second) {
                    const auto sit = sorts_.find(n);
                    if (sit == sorts_.end()) { continue; }
                    declare(fresh(n), sit->second);
                }
                // 3. ASSUME the invariants over the havoc'd state, and consume
                //    the assert statements from the stream -- they are the
                //    invariants now, not per-pass obligations.
                if (invs != nullptr) {
                    for (std::size_t i = 0; i < invs->size(); ++i) {
                        if (!is("assert")) {
                            d.error(ErrorCode::E_PARSE,
                                    "the pre-scanned invariant run and the body "
                                    "disagree at label `" + name + "`",
                                    loc());
                            return false;
                        }
                        eat();
                        if (!attributes(d)) { return false; }
                        H::ExprPtr inv = expr(d);
                        if (!inv || !expectP(";", d)) { return false; }
                        addAssume(inv);
                    }
                }
            }
        }
        pending_labels_.push_back(name);
        return true;
    }

    bool gotoStatement(Uir::Diagnostics& d) {
        const std::size_t goto_pos = tok_.pos;
        eat();                                       // 'goto'
        std::vector<std::string> targets;
        while (tok_.kind == Token::IDENT) {
            targets.push_back(tok_.text);
            eat();
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (targets.empty()) {
            d.error(ErrorCode::E_PARSE, "goto requires at least one label", loc());
            return false;
        }
        if (!expectP(";", d)) { return false; }
        if (!dead_) {
            for (const std::string& t : targets) {
                if (!routeGoto(t, goto_pos, d)) { return false; }
            }
        }
        dead_ = true;
        return true;
    }

    /** Route one goto target: forward edges are recorded in the target's
     *  frame; a backward edge is CUT -- the implicit invariant is `true`, and
     *  the header havoc'd the cycle's assignments when it was processed
     *  (RemoveBackEdges.cs's treatment of a header with no assert prefix). */
    bool routeGoto(const std::string& name, std::size_t goto_pos,
                   Uir::Diagnostics& d) {
        const auto lit = body_scan_.label_list.find(name);
        if (lit == body_scan_.label_list.end()) {
            // Unreachable after the pre-scan, which refuses this; kept as the
            // defensive type error it is (This is Boogie 2 §9.5).
            d.error(ErrorCode::E_TYPE,
                    "goto target `" + name + "` is not a label in this procedure body",
                    loc());
            return false;
        }
        const std::size_t owner = lit->second;
        int up = -1;
        for (int i = static_cast<int>(frames_.size()) - 1; i >= 0; --i) {
            if (frames_[i].list_id == owner) { up = i; break; }
        }
        if (up < 0) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "a `goto` into a structured statement's body is not "
                    "implemented: control flow is joined at construct boundaries",
                    loc());
            return false;
        }
        const LabelScan& scan = body_scan_.lists.at(owner);
        const bool backward = scan.label_pos.at(name) <= goto_pos;
        if (backward) {
            for (int i = up + 1; i < static_cast<int>(frames_.size()); ++i) {
                if (frames_[i].in_while_body) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a `goto` that loops back across a `while` boundary is "
                            "not implemented: the `while`'s checked-invariant "
                            "encoding and a goto loop's implicit-true-invariant "
                            "cut do not compose; write the loop as one construct",
                            loc());
                    return false;
                }
            }
            // The cut -- and the header's invariants, if the pre-scan saw an
            // assert prefix there, are obligations HERE: the back edge is
            // where preservation is checked (RemoveBackEdges.cs turns the
            // header's assert prefix into the invariant set).
            const auto ait = scan.label_asserts.find(name);
            if (ait != scan.label_asserts.end()) {
                for (const Mark& m : ait->second) {
                    H::ExprPtr inv = readMarkedExpr(m, d);
                    if (!inv) { return false; }
                    addObligation(inv);
                }
            }
            return true;                               // the cut
        }
        frames_[up].edges[name].push_back(PendingEdge{edgeGuard(), version_});
        return true;
    }

    bool breakStatement(Uir::Diagnostics& d) {
        eat();                                       // 'break'
        std::string label;
        if (tok_.kind == Token::IDENT) { label = tok_.text; eat(); }
        if (!expectP(";", d)) { return false; }
        // Plain `break` is the innermost enclosing WHILE (if entries are
        // skipped); `break L` names an enclosing labeled while or if (This is
        // Boogie 2 §9.5).
        int target = -1;
        for (int i = static_cast<int>(breakables_.size()) - 1; i >= 0; --i) {
            if (label.empty() && breakables_[i].is_while) { target = i; break; }
            if (!label.empty() && breakables_[i].label == label) {
                target = i;
                break;
            }
        }
        if (target < 0) {
            d.error(ErrorCode::E_TYPE,
                    label.empty()
                        ? "`break` outside a loop"
                        : "`break` target `" + label
                              + "` is not an enclosing labeled `while` or `if`",
                    loc());
            return false;
        }
        if (!dead_) {
            breakables_[target].collector->push_back(
                PendingEdge{edgeGuard(), version_});
        }
        dead_ = true;
        return true;
    }

    bool statement(Uir::Diagnostics& d) {
        if (!is("while") && !is("if")) { pending_labels_.clear(); }
        if (is("while")) { return whileStatement(d); }
        if (is("goto")) { return gotoStatement(d); }
        if (is("break")) { return breakStatement(d); }
        if (is("call") || is("free") || is("async")) { return callStatement(d); }
        if (is("if")) { return ifStatement(d); }
        if (is("assume") || is("assert")) {
            const bool is_assert = is("assert");
            // `assume {:captureState "..."} true;` -- a statement carries
            // attributes too, and they are verifier directives like the ones on
            // a declaration.
            eat();
            if (!attributes(d)) { return false; }
            H::ExprPtr e = expr(d);
            if (!e || !expectP(";", d)) { return false; }
            // An `assert` inside a body is an obligation like the postcondition,
            // so it is negated too -- but only one obligation can be refuted at
            // a time, so it joins the postcondition's disjunction of negations.
            //
            // It used to push its own `NOT(e)` constraint, and the model's
            // constraints are a CONJUNCTION, so two obligations became
            // `¬a1 ∧ ¬a2`: every obligation had to fail on ONE execution for
            // the query to be satisfiable. A procedure violating exactly one
            // assert therefore produced an unsatisfiable script, which this
            // encoding reads as "meets its contract".
            //
            //     procedure P(x: int) { assert x == x; assert false; }
            //
            // emitted `(assert (distinct x x)) (assert true)` -- UNSAT, and
            // reported as verified. **That is unsound in the direction that
            // matters**: it claims a proof that does not exist.
            //
            // Each obligation is timestamped with the prefix at this source
            // point. Its branch is `prefix_i ∧ ¬a_i`, and all such branches are
            // disjoined at procedure end. The assertion is then assumed for
            // later statements, exactly as Boogie's assert-then-assume rule
            // requires; that later assumption cannot flow backward across the
            // stored prefix boundary.
            if (is_assert) {
                addObligation(e);
                addAssume(e);
            } else {
                addAssume(e);
            }
            return true;
        }
        if (is("havoc")) {
            eat();
            bool saw_target = false;
            while (tok_.kind == Token::IDENT) {
                const std::string name = tok_.text;
                const auto it = sorts_.find(name);
                if (it == sorts_.end()) {
                    d.error(ErrorCode::E_TYPE, "'" + name + "' is not declared", loc());
                    return false;
                }
                if (!checkWritable(name, d)) { return false; }
                // A FRESH variable, which is the whole content of havoc. As a
                // no-op the old value persists and the VC proves a property of a
                // program that cannot happen.
                declare(fresh(name), it->second);
                saw_target = true;
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!saw_target) {
                d.error(ErrorCode::E_PARSE, "havoc requires at least one variable", loc());
                return false;
            }
            return expectP(";", d);
        }
        if (is("return")) {
            eat();
            if (!expectP(";", d)) { return false; }
            // The procedure's checked postconditions are obligations at EVERY
            // exit point, under the path that reaches it (§2.3); the body's
            // final fall-through is another one, handled at the end of
            // procedure().
            emitEnsures();
            dead_ = true;
            return true;
        }
        if (is("var")) {
            // A local has the same declaration syntax but not global
            // ownership. Registering it in global_vars_ makes the next
            // procedure try to recreate it from global_sorts_, where it
            // correctly does not exist.
            return globalDecl(d, false);
        }
        // An assignment: `x := e;` or the PARALLEL form `x, y := e, f;`.
        // (A label is a statement-list matter and is intercepted by
        // statementList before statement() is ever called on one.)
        if (tok_.kind == Token::IDENT) {
            std::vector<std::string> targets;
            std::vector<std::vector<H::ExprPtr>> target_indices;
            std::unordered_set<std::string> assigned;
            for (;;) {
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected an assignment target", loc());
                    return false;
                }
                const std::string name = tok_.text;
                if (sorts_.find(name) == sorts_.end()) {
                    d.error(ErrorCode::E_TYPE, "'" + name + "' is not declared", loc());
                    return false;
                }
                if (!checkWritable(name, d)) { return false; }
                if (!assigned.insert(name).second) {
                    d.error(ErrorCode::E_PARSE,
                            "variable `" + name
                                + "` is assigned more than once in parallel assignment",
                            loc());
                    return false;
                }
                targets.push_back(name);
                eat();
                // `m[i] := v` assigns the MAP, not a cell: the new map is
                // `store(m, i, v)`. Recording it as an index list here rather
                // than rewriting later is what keeps the parallel form honest
                // -- every index is an expression, and it must be read against
                // the versions in force BEFORE any target is updated, exactly
                // as the right-hand sides are.
                std::vector<H::ExprPtr> idx;
                while (isP("[")) {
                    const Uir::SourceLoc at = loc();
                    eat();
                    H::ExprPtr i = expr(d);
                    if (!i) { return false; }
                    if (isP(",")) {
                        d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "a multi-index map assignment is not implemented, for "
                                "the reason the multi-index map TYPE is not", at);
                        return false;
                    }
                    if (!expectP("]", d)) { return false; }
                    idx.push_back(std::move(i));
                }
                target_indices.push_back(std::move(idx));
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(":=", d)) { return false; }
            std::vector<H::ExprPtr> rhs;
            for (;;) {
                H::ExprPtr e = expr(d);
                if (!e) { return false; }
                rhs.push_back(e);
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(";", d)) { return false; }
            if (rhs.size() != targets.size()) {
                d.error(ErrorCode::E_TYPE,
                        "this assignment has " + std::to_string(targets.size())
                            + " target(s) and " + std::to_string(rhs.size())
                            + " value(s)",
                        loc());
                return false;
            }
            for (std::size_t i = 0; i < targets.size(); ++i) {
                if (!checkAssignment(sorts_.at(targets[i]), target_indices[i], rhs[i], d)) {
                    return false;
                }
            }
            // **Every right-hand side is read before ANY target is updated.**
            // That is what makes it parallel: `r, u := u, r` swaps, and
            // versioning the targets one at a time as they are assigned would
            // make the second read the value the first had just written. The
            // expressions above were all built against the current versions, so
            // the only thing that has to wait is fresh().
            for (std::size_t i = 0; i < targets.size(); ++i) {
                const H::Sort ts = sorts_.at(targets[i]);
                // The OLD map, read before any target is versioned -- so
                // `a[i], a[j] := a[j], a[i]` reads one map and writes another,
                // which is what makes the parallel form a swap here too.
                H::ExprPtr value = rhs[i];
                if (!target_indices[i].empty()) {
                    H::ExprPtr old = H::mkIdent(
                        consts_.count(targets[i]) != 0 ? targets[i]
                                                       : current(targets[i]), ts);
                    value = storeAt(old, target_indices[i], 0, rhs[i], targets[i], d);
                    if (!value) { return false; }
                }
                const std::string next = fresh(targets[i]);
                declare(next, ts);
                addAssume(H::mkOp(H::Op::EQ, {H::mkIdent(next, ts), value}));
            }
            return true;
        }
        d.error(ErrorCode::E_PARSE, "unexpected '" + tok_.text + "' in a statement", loc());
        return false;
    }


    // ---- D7: the Horn-clause route -------------------------------------------
    //
    // boogie.md §4.6's two-hop route. From the SAME parse -- same
    // declarations, same contracts re-read from the same marks, same body
    // text -- emit constrained Horn clauses whose solution is the program's
    // inductive invariants:
    //
    //   * per procedure P, a summary relation `P!sum(in, g_entry, g_exit,
    //     out)`: its clauses are the body's exit edges CONJOINED with the
    //     ensures, so the caller's assumption of the postcondition is the
    //     relation's definition, and the caller's check of the precondition
    //     is an error clause;
    //   * per while loop a head relation, so the loop's invariant is INFERRED
    //     by the Horn solver (the source's checked invariants become error
    //     clauses, never assumptions; free ones are assumed, as the direct
    //     route assumes them);
    //   * per program point a relation over the state tuple (in-formals,
    //     mutable globals now, the same globals at body entry for old(),
    //     out-formals, locals). A label's relation is defined by one clause
    //     per incoming edge -- the join needs no gates here.
    //
    // `error!` is the one nullary relation; SAT means a counterexample
    // exists, the direct route's polarity exactly (§2.4). The agreement
    // harness is test/python/test_boogie_chc_crosscheck.py.
    //
    // What this route cannot express: `call forall` with a wildcard -- the
    // quantified lemma assumption it denotes is not a Horn clause. Refused by
    // name in this mode only. A quantified axiom or function body is refused
    // here for the same reason.

    /** Declare a Horn relation (a Bool-returning function). */
    void chcRel(const std::string& name, const std::vector<H::Sort>& params) {
        if (!chc_rels_.insert(name).second) { return; }
        H::FunDecl f;
        f.name = name;
        f.params = params;
        f.result = H::Sort::boolean();
        f.loc = loc();
        model_->funs.push_back(f);
    }

    /** A fresh program-point relation over the current procedure's tuple. */
    std::string chcFreshRel(const std::string& tag) {
        const std::string name =
            chc_body_ + "!" + tag + "!" + std::to_string(chc_point_++);
        chcRel(name, chc_sorts_);
        return name;
    }

    /** Begin one clause: every tuple component becomes a fresh bound
     *  variable, resolved by the expression parser through bound_ -- the same
     *  discipline quantifier() uses. */
    void chcBeginClause() {
        chc_binders_.clear();
        chc_tuple_binders_.clear();
        for (std::size_t i = 0; i < chc_names_.size(); ++i) {
            H::Binder b;
            b.name = "q!" + std::to_string(qv_++) + "!" + chc_names_[i];
            b.sort = chc_sorts_[i];
            chc_binders_.push_back(b);
            bound_[chc_names_[i]] = b.sort;
            renamed_binders_[chc_names_[i]] = b.name;
            chc_tuple_binders_.insert(b.name);
        }
    }
    void chcEndClause() {
        for (std::size_t i = 0; i < chc_names_.size(); ++i) {
            bound_.erase(chc_names_[i]);
            renamed_binders_.erase(chc_names_[i]);
        }
    }

    /** The binder for one tuple component (e.g. `g`, or `g!entry`). */
    H::ExprPtr chcVar(const std::string& component) {
        return H::mkBoundVar(renamed_binders_.at(component),
                             chc_sort_of_.at(component));
    }

    /** The state tuple as head arguments: the component's binder, or the
     *  override term where the statement changed it. */
    std::vector<H::ExprPtr>
    chcState(const std::unordered_map<std::string, H::ExprPtr>& overridden) {
        std::vector<H::ExprPtr> args;
        args.reserve(chc_names_.size());
        for (std::size_t i = 0; i < chc_names_.size(); ++i) {
            const auto it = overridden.find(chc_names_[i]);
            args.push_back(it != overridden.end()
                               ? it->second
                               : H::mkBoundVar(renamed_binders_.at(chc_names_[i]),
                                               chc_sorts_[i]));
        }
        return args;
    }

    /** Whether the antecedent is visibly false: a literal, a conjunction with
     *  a false conjunct, or a negation of `true` -- the factory fold runs at
     *  lowering time, not here, so look through the surface. */
    static bool chcVacuous(const H::ExprPtr& e) {
        if (e->kind == H::ExprKind::LIT_BOOL) { return !e->bool_value; }
        if (e->kind == H::ExprKind::OP && e->op == H::Op::AND) {
            for (const H::ExprPtr& a : e->args) {
                if (chcVacuous(a)) { return true; }
            }
        }
        if (e->kind == H::ExprKind::OP && e->op == H::Op::NOT
            && !e->args.empty()
            && e->args[0]->kind == H::ExprKind::LIT_BOOL) {
            return e->args[0]->bool_value;
        }
        return false;
    }

    /** chcState with DISTINCT head arguments: every overridden component gets
     *  a fresh binder in the head and its equation moves into @p eqs, because
     *  CHC-COMP heads apply a predicate to distinct variables (reusing one
     *  binder at two positions is not accepted by the format check). */
    std::vector<H::ExprPtr>
    chcStateDistinct(const std::unordered_map<std::string, H::ExprPtr>& overridden,
                     H::ExprPtr& eqs) {
        std::vector<H::ExprPtr> args;
        args.reserve(chc_names_.size());
        for (std::size_t i = 0; i < chc_names_.size(); ++i) {
            const std::string& n = chc_names_[i];
            const auto it = overridden.find(n);
            if (it == overridden.end()) {
                args.push_back(H::mkBoundVar(renamed_binders_.at(n), chc_sorts_[i]));
                continue;
            }
            if (it->second->kind == H::ExprKind::BOUND_VAR
                && chc_tuple_binders_.count(it->second->name) == 0) {
                // already a fresh binder (havoc, call): use it directly. A
                // TUPLE binder (an assignment's `r := x` reads x's binder)
                // would collide at the other position, so it takes the
                // equation form below.
                args.push_back(it->second);
                continue;
            }
            H::Binder b;
            b.name = "q!" + std::to_string(qv_++) + "!" + n;
            b.sort = chc_sorts_[i];
            chc_binders_.push_back(b);
            args.push_back(H::mkBoundVar(b.name, b.sort));
            eqs = conjoin(eqs, H::mkOp(H::Op::EQ, {H::mkBoundVar(b.name, b.sort),
                                                   it->second}));
        }
        return args;
    }

    /** One clause: `forall binders. body ==> head`. A clause that folds to
     *  `true` is vacuous and skipped; every emitted clause is quantified,
     *  with a dummy binder when the tuple is empty (CHC-COMP wants
     *  implications universally quantified). Axioms are NOT folded here: they
     *  constrain the tuple's constant components at the entry clause, and the
     *  components' pass-through carries them to every reachable state -- the
     *  exact reading, since Spacer rejects free constants in rule bodies. */
    void chcClause(const H::ExprPtr& body, const H::ExprPtr& head) {
        H::ExprPtr ante = body;
        // A false antecedent makes the clause vacuous (an unreachable
        // continuation); whether the fold happens at mkOp or later, do not
        // emit it. The AND case arises because the factory fold runs at
        // lowering time, not here.
        if (ante && chcVacuous(ante)) { return; }
        H::ExprPtr f = ante ? H::mkOp(H::Op::IMPLIES, {ante, head}) : head;
        if (f->kind == H::ExprKind::LIT_BOOL) { return; }   // vacuous
        if (chc_binders_.empty()) {
            H::Binder q;
            q.name = "q!empty!" + std::to_string(qv_++);
            q.sort = H::Sort::boolean();
            chc_binders_.push_back(q);
        }
        f = H::mkForall(chc_binders_, f, loc());
        H::Constraint c;
        c.loc = loc();
        c.formula = f;
        model_->constraints.push_back(c);
    }

    H::ExprPtr chcApp(const std::string& rel,
                      const std::vector<H::ExprPtr>& args) {
        return H::mkApply(rel, H::Sort::boolean(), args, loc());
    }

    H::ExprPtr chcError() {
        chcRel("error!", {});
        return H::mkApply("error!", H::Sort::boolean(), {}, loc());
    }

    /** Re-read one of the current procedure's own contract clauses with the
     *  current clause's bindings live. */
    H::ExprPtr chcReadOwnContract(const ProcContract& c, Uir::Diagnostics& d,
                                  bool requires = false) {
        const auto saved_bound = bound_;
        const auto saved_renamed = renamed_binders_;
        const auto saved_formals = call_formals_;
        const auto saved_forbidden = contract_forbidden_;
        const ProcSig& sig = procs_.at(chc_proc_);
        call_formals_.clear();
        contract_forbidden_.clear();
        // Body locals and implementation parameter spellings are not in the
        // declaration's contract scope. Keep globals (including old-state
        // aliases) and constants; install positional formal substitutions.
        for (const std::string& n : chc_names_) {
            if (global_vars_.count(n) == 0 && consts_.count(n) == 0
                && n.find("!entry") == std::string::npos) { bound_.erase(n); }
        }
        for (const std::string& n : sig.in_names) {
            call_formals_[n] = chcVar(chc_contract_names_.at(n));
        }
        for (const std::string& n : sig.out_names) {
            if (requires) { contract_forbidden_.insert(n); }
            else { call_formals_[n] = chcVar(chc_contract_names_.at(n)); }
        }
        H::ExprPtr out = readContractClause(c, !requires, d);
        bound_ = saved_bound;
        renamed_binders_ = saved_renamed;
        call_formals_ = saved_formals;
        contract_forbidden_ = saved_forbidden;
        return out;
    }

    /** Re-read a marked expression against the CURRENT version map (or the
     *  current clause's bindings in the Horn route). The re-parse idiom: an
     *  expression's meaning is its SSA resolution at the point of use. */
    H::ExprPtr readMarkedExpr(const Mark& m, Uir::Diagnostics& d) {
        const Mark here = mark();
        reset(m);
        H::ExprPtr out = expr(d);
        reset(here);
        return out;
    }

    /** Collect the body's locals (with their types) before any clause exists:
     *  the state tuple is fixed per procedure. */
    bool chcCollectLocals(Uir::Diagnostics& d) {
        // tok_ is at the list's `{`; consumes through `}`.
        eat();                                       // '{'
        while (!isP("}")) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated block", loc());
                return false;
            }
            if (is("var")) {
                eat();
                if (!attributes(d)) { return false; }
                for (;;) {
                    std::vector<std::string> group;
                    for (;;) {
                        if (tok_.kind != Token::IDENT) {
                            d.error(ErrorCode::E_PARSE, "expected a variable name",
                                    loc());
                            return false;
                        }
                        group.push_back(tok_.text);
                        eat();
                        if (isP(",")) { eat(); continue; }
                        break;
                    }
                    if (!expectP(":", d)) { return false; }
                    H::Sort s;
                    if (!type(s, d)) { return false; }
                    if (!whereClauseRefused(d)) { return false; }
                    for (const std::string& n : group) {
                        chc_names_.push_back(n);
                        chc_sorts_.push_back(s);
                        chc_sort_of_[n] = s;
                        sorts_[n] = s;               // for probe-parses
                    }
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (!expectP(";", d)) { return false; }
                continue;
            }
            if (is("if")) {
                eat();
                if (!scanGuard(d)) { return false; }
                if (!chcCollectLocals(d)) { return false; }
                while (is("else")) {
                    eat();
                    if (is("if")) { break; }          // else-if: re-loop below
                    if (!chcCollectLocals(d)) { return false; }
                }
                if (is("if")) {
                    // the else-if chain's `if` was left current by the break
                    continue;
                }
                continue;
            }
            if (is("while")) {
                eat();
                if (!scanGuard(d)) { return false; }
                while (is("invariant") || is("free")) {
                    const bool is_free = is("free");
                    eat();
                    if (is_free) {
                        if (!is("invariant")) {
                            d.error(ErrorCode::E_PARSE,
                                    "expected 'invariant' after 'free'", loc());
                            return false;
                        }
                        eat();
                    }
                    if (!skipExpression(d) || !expectP(";", d)) { return false; }
                }
                if (!chcCollectLocals(d)) { return false; }
                continue;
            }
            // A label, or any simple statement: through its `;`.
            if (tok_.kind == Token::IDENT && lex_.peekIsColon()
                && !lex_.peekIsAssign()) {
                eat();
                eat();                               // ':'
                continue;
            }
            int pd = 0;
            while (tok_.kind != Token::END) {
                if (pd == 0 && isP(";")) { break; }
                if (isP("(") || isP("[") || isP("{")) { ++pd; }
                else if (isP(")") || isP("]") || isP("}")) { --pd; }
                eat();
            }
            if (!expectP(";", d)) { return false; }
        }
        eat();                                       // '}'
        return true;
    }

    /** The exit edges of the current procedure from relation @p rel: an error
     *  clause per checked ensures, and the summary clause conjoining every
     *  ensures (checked or free -- the caller assumes all of them). */
    bool chcExit(Uir::Diagnostics& d, const std::string& rel) {
        const ProcSig& sig = procs_.at(chc_proc_);
        chcBeginClause();
        H::ExprPtr all;
        std::vector<H::ExprPtr> checked;
        for (const ProcContract& c : sig.ensures) {
            H::ExprPtr e = chcReadOwnContract(c, d);
            if (!e) { chcEndClause(); return false; }
            all = conjoin(all, e);
            if (!c.free_clause) { checked.push_back(e); }
        }
        const std::vector<H::ExprPtr> state = chcState({});
        for (const H::ExprPtr& e : checked) {
            chcClause(conjoin(chcApp(rel, state), H::mkOp(H::Op::NOT, {e})),
                      chcError());
        }
        // The summary tuple: (in, g_entry, g_exit, out).
        std::vector<H::ExprPtr> sargs;
        for (std::size_t i = 0; i < chc_sum_in_; ++i) {
            sargs.push_back(chcVar(chc_names_[i]));
        }
        for (const std::string& g : chc_globals_) {
            sargs.push_back(chcVar(g + "!entry"));
        }
        for (const std::string& g : chc_globals_) { sargs.push_back(chcVar(g)); }
        for (const std::string& o : chc_outs_) { sargs.push_back(chcVar(o)); }
        H::ExprPtr body = chcApp(rel, state);
        if (all) { body = conjoin(body, all); }
        chcClause(body, chcApp(chc_proc_ + "!sum", sargs));
        chcEndClause();
        return true;
    }

    /** A statement list in the Horn route: a label is a relation (the join is
     *  one clause per incoming edge); `cur` is the current point's relation,
     *  empty for dead code -- an empty relation is never derived, which is
     *  exactly the direct route's dead-code pruning. */
    bool chcList(Uir::Diagnostics& d, std::string& cur) {
        if (!expectP("{", d)) { return false; }
        while (!isP("}")) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated block", loc());
                return false;
            }
            if (tok_.kind == Token::IDENT && lex_.peekIsColon()
                && !lex_.peekIsAssign()) {
                const std::string lrel = chc_body_ + "!L!" + tok_.text;
                chcRel(lrel, chc_sorts_);
                eat();
                eat();                               // ':'
                if (!cur.empty()) {
                    chcBeginClause();
                    chcClause(chcApp(cur, chcState({})), chcApp(lrel, chcState({})));
                    chcEndClause();
                }
                cur = lrel;
                continue;
            }
            if (!chcStatement(d, cur)) { return false; }
        }
        eat();                                       // '}'
        return true;
    }

    /** `if (c) T else E` / `if (*)`: one entry clause per branch, one
     *  fall-through clause per live branch end into the shared join relation.
     *  `L: if ...` makes L a `break L` target, as in the direct route. */
    bool chcIf(Uir::Diagnostics& d, std::string& cur) {
        eat();                                       // 'if'
        const std::vector<std::string> pending = pending_labels_;
        pending_labels_.clear();
        if (!expectP("(", d)) { return false; }
        const Mark guard_mark = mark();
        bool star = false;
        if (isP("*")) {
            eat();
            star = true;
        } else {
            H::ExprPtr probe = expr(d);
            if (!probe) { return false; }
        }
        if (!expectP(")", d)) { return false; }

        const std::string join_rel = chcFreshRel("j");
        std::size_t breakables_added = 0;
        for (const std::string& l : pending) {
            chc_breakables_.push_back(ChcBreakable{l, false, join_rel, {}});
            ++breakables_added;
        }
        const auto readGuard = [&](H::ExprPtr& out) -> bool {
            out = readMarkedExpr(guard_mark, d);
            return out != nullptr;
        };

        const std::string then_in = chcFreshRel("t");
        if (!cur.empty()) {
            chcBeginClause();
            H::ExprPtr ante = chcApp(cur, chcState({}));
            if (!star) {
                H::ExprPtr c;
                if (!readGuard(c)) { return false; }
                ante = conjoin(ante, c);
            }
            chcClause(ante, chcApp(then_in, chcState({})));
            chcEndClause();
        }
        std::string tcur = then_in;
        if (!chcList(d, tcur)) { return false; }
        if (!tcur.empty()) {
            chcBeginClause();
            chcClause(chcApp(tcur, chcState({})), chcApp(join_rel, chcState({})));
            chcEndClause();
        }

        const std::string else_in = chcFreshRel("e");
        if (!cur.empty()) {
            chcBeginClause();
            H::ExprPtr ante = chcApp(cur, chcState({}));
            if (!star) {
                H::ExprPtr c;
                if (!readGuard(c)) { return false; }
                ante = conjoin(ante, H::mkOp(H::Op::NOT, {c}));
            }
            chcClause(ante, chcApp(else_in, chcState({})));
            chcEndClause();
        }
        std::string ecur = else_in;
        if (is("else")) {
            eat();
            if (is("if")) {
                if (!chcIf(d, ecur)) { return false; }
            } else if (!chcList(d, ecur)) {
                return false;
            }
        }
        // With or without an `else`, the else path flows into the join.
        if (!ecur.empty()) {
            chcBeginClause();
            chcClause(chcApp(ecur, chcState({})), chcApp(join_rel, chcState({})));
            chcEndClause();
        }
        // Breaks into the join are clauses too.
        for (std::size_t i = chc_breakables_.size() - breakables_added;
             i < chc_breakables_.size(); ++i) {
            for (const std::string& src : chc_breakables_[i].pending) {
                chcBeginClause();
                chcClause(chcApp(src, chcState({})), chcApp(join_rel, chcState({})));
                chcEndClause();
            }
        }
        for (std::size_t i = breakables_added; i > 0; --i) {
            chc_breakables_.pop_back();
        }
        cur = join_rel;
        return true;
    }

    /** `while (c) invariant I; B`: the head relation H is the invariant the
     *  Horn solver must find. The source's checked invariants are ERROR
     *  clauses (entry and preservation), never assumptions; free invariants
     *  are conjoined into the body-entry and exit clauses, which is exactly
     *  the direct route's assumption of them. */
    bool chcWhile(Uir::Diagnostics& d, std::string& cur) {
        eat();                                       // 'while'
        const std::vector<std::string> pending = pending_labels_;
        pending_labels_.clear();
        if (!expectP("(", d)) { return false; }
        const Mark guard_mark = mark();
        bool star = false;
        if (isP("*")) {
            eat();
            star = true;
        } else {
            H::ExprPtr probe = expr(d);
            if (!probe) { return false; }
        }
        if (!expectP(")", d)) { return false; }
        std::vector<Mark> invariants;
        std::vector<Mark> free_invariants;
        while (is("invariant") || is("free")) {
            const bool is_free = is("free");
            eat();
            if (is_free) {
                if (!is("invariant")) {
                    d.error(ErrorCode::E_PARSE, "expected 'invariant' after 'free'",
                            loc());
                    return false;
                }
                eat();
            }
            if (!attributes(d)) { return false; }
            const Mark m = mark();
            H::ExprPtr probe = expr(d);
            if (!probe || !expectP(";", d)) { return false; }
            (is_free ? free_invariants : invariants).push_back(m);
        }
        if (!isP("{")) {
            d.error(ErrorCode::E_PARSE, "expected a loop body", loc());
            return false;
        }

        const std::string head = chcFreshRel("h");
        const std::string exit_rel = chcFreshRel("x");
        for (const std::string& l : pending) {
            chc_breakables_.push_back(ChcBreakable{l, true, exit_rel, {}});
        }
        chc_breakables_.push_back(ChcBreakable{"", true, exit_rel, {}});

        // Entry: the head holds on the incoming state; checked invariants are
        // obligations there.
        if (!cur.empty()) {
            chcBeginClause();
            const H::ExprPtr ante = chcApp(cur, chcState({}));
            chcClause(ante, chcApp(head, chcState({})));
            for (const Mark& m : invariants) {
                H::ExprPtr inv = readMarkedExpr(m, d);
                if (!inv) { return false; }
                chcClause(conjoin(ante, H::mkOp(H::Op::NOT, {inv})), chcError());
            }
            chcEndClause();
        }
        // The body runs where the head holds and the guard is true (free
        // invariants assumed).
        const std::string body_in = chcFreshRel("b");
        {
            chcBeginClause();
            H::ExprPtr ante = chcApp(head, chcState({}));
            if (!star) {
                H::ExprPtr c = readMarkedExpr(guard_mark, d);
                if (!c) { return false; }
                ante = conjoin(ante, c);
            }
            for (const Mark& m : free_invariants) {
                H::ExprPtr inv = readMarkedExpr(m, d);
                if (!inv) { return false; }
                ante = conjoin(ante, inv);
            }
            chcClause(ante, chcApp(body_in, chcState({})));
            chcEndClause();
        }
        std::string bcur = body_in;
        if (!chcList(d, bcur)) { return false; }
        if (!bcur.empty()) {
            // The back edge, and preservation as an error clause per checked
            // invariant: from the body-end state the invariant must hold.
            chcBeginClause();
            const H::ExprPtr ante = chcApp(bcur, chcState({}));
            chcClause(ante, chcApp(head, chcState({})));
            for (const Mark& m : invariants) {
                H::ExprPtr inv = readMarkedExpr(m, d);
                if (!inv) { return false; }
                chcClause(conjoin(ante, H::mkOp(H::Op::NOT, {inv})), chcError());
            }
            chcEndClause();
        }
        // Break edges are exits too.
        std::vector<std::string> pending_sources;
        for (std::size_t i = chc_breakables_.size() - (pending.size() + 1);
             i < chc_breakables_.size(); ++i) {
            for (const std::string& src : chc_breakables_[i].pending) {
                pending_sources.push_back(src);
            }
        }
        for (std::size_t i = pending.size() + 1; i > 0; --i) {
            chc_breakables_.pop_back();
        }
        for (const std::string& src : pending_sources) {
            chcBeginClause();
            chcClause(chcApp(src, chcState({})), chcApp(exit_rel, chcState({})));
            chcEndClause();
        }
        // The exit: the head holds and the guard does not.
        {
            chcBeginClause();
            H::ExprPtr ante = chcApp(head, chcState({}));
            if (!star) {
                H::ExprPtr c = readMarkedExpr(guard_mark, d);
                if (!c) { return false; }
                ante = conjoin(ante, H::mkOp(H::Op::NOT, {c}));
            }
            for (const Mark& m : free_invariants) {
                H::ExprPtr inv = readMarkedExpr(m, d);
                if (!inv) { return false; }
                ante = conjoin(ante, inv);
            }
            chcClause(ante, chcApp(exit_rel, chcState({})));
            chcEndClause();
        }
        cur = exit_rel;
        return true;
    }

    /** `call x, y := P(e)`, `free call`, `call forall` (ground) -- the same
     *  contract as the direct route, as clauses: a checked requires is an
     *  error clause per clause; the continuation applies the callee's
     *  summary relation, whose definition conjoins the callee's ensures. */
    bool chcCall(Uir::Diagnostics& d, std::string& cur) {
        if (is("async")) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "'async call' is not implemented: an asynchronous call does not "
                    "give the caller the callee's postcondition, so it is not a "
                    "contract instantiation",
                    loc());
            return false;
        }
        bool free_call = false;
        if (is("free")) { free_call = true; eat(); }
        if (!is("call")) {
            d.error(ErrorCode::E_PARSE, "expected 'call' after 'free'", loc());
            return false;
        }
        eat();                                       // 'call'
        if (!attributes(d)) { return false; }
        if (is("forall")) {
            eat();
            // Only the ground form is a Horn clause; a wildcard's quantified
            // lemma assumption is not one.
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE,
                        "expected a procedure name after 'call forall'", loc());
                return false;
            }
            const std::string callee = tok_.text;
            eat();
            const auto pit = procs_.find(callee);
            if (pit == procs_.end()) {
                d.error(ErrorCode::E_TYPE,
                        "call target `" + callee + "` is not a declared procedure",
                        loc());
                return false;
            }
            const ProcSig& sig = pit->second;
            if (!sig.out_names.empty() || !sig.modifies_checked.empty()) {
                d.error(ErrorCode::E_TYPE,
                        "call forall target `" + callee
                            + "` is not a lemma procedure: it has out-parameters or "
                              "a checked modifies clause (This is Boogie 2 §9.10)",
                        loc());
                return false;
            }
            if (!expectP("(", d)) { return false; }
            chcBeginClause();
            const std::size_t n = sig.in_names.size();
            std::vector<H::ExprPtr> args(n);
            bool any_wild = false;
            std::size_t idx = 0;
            while (!isP(")")) {
                if (idx >= n) {
                    d.error(ErrorCode::E_TYPE,
                            "'" + callee + "' takes " + std::to_string(n)
                                + " in-parameter(s), not more",
                            loc());
                    return false;
                }
                if (isP("*")) {
                    eat();
                    any_wild = true;
                } else {
                    args[idx] = expr(d);
                    if (!args[idx]) { return false; }
                }
                ++idx;
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(")", d) || !expectP(";", d)) { return false; }
            if (any_wild) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a `call forall` with a wildcard is not a Horn clause: the "
                        "quantified lemma assumption it denotes (This is Boogie 2 "
                        "§9.10) has no clause form; the direct VC route handles it",
                        loc());
                return false;
            }
            if (!cur.empty()) {
                for (std::size_t i = 0; i < n; ++i) {
                    call_formals_[sig.in_names[i]] = args[i];
                }
                H::ExprPtr pre;
                for (const ProcContract& c : sig.requires) {
                    if (c.free_clause) { continue; }
                    H::ExprPtr e = readContractClause(c, false, d);
                    if (!e) { return false; }
                    pre = conjoin(pre, e);
                }
                H::ExprPtr post;
                for (const ProcContract& c : sig.ensures) {
                    H::ExprPtr e = readContractClause(c, true, d);
                    if (!e) { return false; }
                    post = conjoin(post, e);
                }
                call_formals_.clear();
                H::ExprPtr lemma =
                    pre ? H::mkOp(H::Op::IMPLIES, {pre, post}) : post;
                if (lemma) {
                    const std::string next = chcFreshRel("p");
                    chcClause(conjoin(chcApp(cur, chcState({})), lemma),
                              chcApp(next, chcState({})));
                    cur = next;
                }
            } else {
                call_formals_.clear();
            }
            chcEndClause();
            return true;
        }
        // A plain call.
        std::vector<std::string> lhs;
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE,
                    "expected a procedure name or an out-parameter target after 'call'",
                    loc());
            return false;
        }
        std::string callee = tok_.text;
        eat();
        if (!isP("(")) {
            lhs.push_back(callee);
            while (isP(",")) {
                eat();
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected an out-parameter target",
                            loc());
                    return false;
                }
                lhs.push_back(tok_.text);
                eat();
            }
            if (!expectP(":=", d)) { return false; }
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected a procedure name after ':='",
                        loc());
                return false;
            }
            callee = tok_.text;
            eat();
        }
        if (!expectP("(", d)) { return false; }
        chcBeginClause();
        std::vector<H::ExprPtr> args;
        while (!isP(")")) {
            H::ExprPtr a = expr(d);
            if (!a) { return false; }
            args.push_back(a);
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(")", d) || !expectP(";", d)) { return false; }

        if (funs_.count(callee) != 0) {
            d.error(ErrorCode::E_TYPE,
                    "call target `" + callee + "` is a function, not a procedure",
                    loc());
            return false;
        }
        const auto pit = procs_.find(callee);
        if (pit == procs_.end()) {
            d.error(ErrorCode::E_TYPE,
                    "call target `" + callee + "` is not a declared procedure",
                    loc());
            return false;
        }
        const ProcSig& sig = pit->second;
        if (args.size() != sig.in_names.size()) {
            d.error(ErrorCode::E_TYPE,
                    "'" + callee + "' takes " + std::to_string(sig.in_names.size())
                        + " in-parameter(s), not " + std::to_string(args.size()),
                    loc());
            return false;
        }
        if (lhs.size() != sig.out_names.size()) {
            d.error(ErrorCode::E_TYPE,
                    "'" + callee + "' returns " + std::to_string(sig.out_names.size())
                        + " out-parameter(s), not " + std::to_string(lhs.size()),
                    loc());
            return false;
        }
        for (std::size_t i = 0; i < args.size(); ++i) {
            if (!H::sameSort(args[i]->sort, sig.in_sorts[i])) {
                d.error(ErrorCode::E_TYPE,
                        "argument " + std::to_string(i + 1) + " of '" + callee
                            + "' is " + H::toString(args[i]->sort) + ", not "
                            + H::toString(sig.in_sorts[i]),
                        loc());
                return false;
            }
        }
        std::unordered_set<std::string> seen_lhs;
        for (const std::string& l : lhs) {
            if (chc_sort_of_.find(l) == chc_sort_of_.end()) {
                d.error(ErrorCode::E_TYPE, "'" + l + "' is not declared", loc());
                return false;
            }
            if (!seen_lhs.insert(l).second) {
                d.error(ErrorCode::E_TYPE,
                        "out-parameter target `" + l + "` appears twice in one call",
                        loc());
                return false;
            }
            if (!checkWritable(l, d)) { return false; }
        }
        for (const std::string& g : sig.modifies_checked) {
            if (procedure_modifies_.count(g) == 0) {
                d.error(ErrorCode::E_TYPE,
                        "call to `" + callee + "` may modify global `" + g
                            + "`, which the enclosing procedure's modifies clause "
                              "does not permit",
                        loc());
                return false;
            }
        }
        for (const std::string& g : sig.modifies_free) {
            if (procedure_modifies_.count(g) == 0) {
                d.error(ErrorCode::E_TYPE,
                        "call to `" + callee + "` may modify global `" + g
                            + "`, which the enclosing procedure's modifies clause "
                              "does not permit",
                        loc());
                return false;
            }
        }

        if (!cur.empty()) {
            // The checked preconditions, each its own error clause.
            if (!free_call) {
                for (std::size_t i = 0; i < args.size(); ++i) {
                    call_formals_[sig.in_names[i]] = args[i];
                }
                for (const std::string& n : sig.out_names) {
                    contract_forbidden_.insert(n);
                }
                for (const ProcContract& c : sig.requires) {
                    if (c.free_clause) { continue; }
                    H::ExprPtr e = readContractClause(c, false, d);
                    if (!e) { return false; }
                    chcClause(conjoin(chcApp(cur, chcState({})),
                                      H::mkOp(H::Op::NOT, {e})),
                              chcError());
                }
                contract_forbidden_.clear();
                call_formals_.clear();
            }
            // The continuation: apply the summary. Modified globals and the
            // out-targets get fresh binders from the sum's out positions;
            // unmodified globals pass their current binder through -- the
            // frame.
            std::unordered_map<std::string, H::ExprPtr> upd;
            std::vector<H::ExprPtr> sargs;
            for (std::size_t i = 0; i < args.size(); ++i) { sargs.push_back(args[i]); }
            for (const std::string& g : chc_globals_) {
                // The callee's entry state is the caller's CURRENT one.
                sargs.push_back(H::mkBoundVar(renamed_binders_.at(g),
                                              chc_sort_of_.at(g)));
            }
            std::vector<H::ExprPtr> gnext;
            for (const std::string& g : chc_globals_) {
                H::ExprPtr v;
                if (sig.modifies_checked.count(g) != 0) {
                    H::Binder b;
                    b.name = "q!" + std::to_string(qv_++) + "!" + g;
                    b.sort = chc_sort_of_.at(g);
                    chc_binders_.push_back(b);
                    v = H::mkBoundVar(b.name, b.sort);
                    upd[g] = v;
                } else {
                    v = H::mkBoundVar(renamed_binders_.at(g), chc_sort_of_.at(g));
                }
                gnext.push_back(v);
            }
            sargs.insert(sargs.end(), gnext.begin(), gnext.end());
            for (std::size_t i = 0; i < lhs.size(); ++i) {
                H::Binder b;
                b.name = "q!" + std::to_string(qv_++) + "!" + lhs[i];
                b.sort = chc_sort_of_.at(lhs[i]);
                chc_binders_.push_back(b);
                H::ExprPtr v = H::mkBoundVar(b.name, b.sort);
                sargs.push_back(v);
                upd[lhs[i]] = v;
            }
            const std::string next = chcFreshRel("p");
            chcClause(conjoin(chcApp(cur, chcState({})),
                              chcApp(callee + "!sum", sargs)),
                      chcApp(next, chcState(upd)));
            cur = next;
        }
        chcEndClause();
        return true;
    }

    bool chcStatement(Uir::Diagnostics& d, std::string& cur) {
        if (is("assume") || is("assert")) {
            const bool is_assert = is("assert");
            eat();
            if (!attributes(d)) { return false; }
            chcBeginClause();
            H::ExprPtr e = expr(d);
            if (!e) { return false; }
            if (!expectP(";", d)) { return false; }
            if (!cur.empty()) {
                const std::string next = chcFreshRel("p");
                const H::ExprPtr ante = chcApp(cur, chcState({}));
                if (is_assert) {
                    chcClause(conjoin(ante, H::mkOp(H::Op::NOT, {e})), chcError());
                }
                // assert-then-assume, the same rule as the direct route.
                chcClause(conjoin(ante, e), chcApp(next, chcState({})));
                cur = next;
            }
            chcEndClause();
            return true;
        }
        if (is("havoc")) {
            eat();
            chcBeginClause();
            std::unordered_map<std::string, H::ExprPtr> upd;
            bool saw_target = false;
            while (tok_.kind == Token::IDENT) {
                const std::string name = tok_.text;
                const auto it = chc_sort_of_.find(name);
                if (it == chc_sort_of_.end()) {
                    d.error(ErrorCode::E_TYPE, "'" + name + "' is not declared", loc());
                    return false;
                }
                if (!checkWritable(name, d)) { return false; }
                // A fresh bound variable at the head, unconstrained: arbitrary.
                H::Binder b;
                b.name = "q!" + std::to_string(qv_++) + "!" + name;
                b.sort = it->second;
                chc_binders_.push_back(b);
                upd[name] = H::mkBoundVar(b.name, b.sort);
                saw_target = true;
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!saw_target) {
                d.error(ErrorCode::E_PARSE, "havoc requires at least one variable",
                        loc());
                return false;
            }
            if (!expectP(";", d)) { return false; }
            if (!cur.empty()) {
                const std::string next = chcFreshRel("p");
                chcClause(chcApp(cur, chcState({})), chcApp(next, chcState(upd)));
                cur = next;
            }
            chcEndClause();
            return true;
        }
        if (is("var")) {
            // Collected into the tuple already; the declaration is consumed.
            eat();
            if (!attributes(d)) { return false; }
            for (;;) {
                while (tok_.kind == Token::IDENT) {
                    eat();
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (!expectP(":", d)) { return false; }
                H::Sort s;
                if (!type(s, d)) { return false; }
                if (!whereClauseRefused(d)) { return false; }
                if (isP(",")) { eat(); continue; }
                break;
            }
            return expectP(";", d);
        }
        if (is("return")) {
            eat();
            if (!expectP(";", d)) { return false; }
            if (!cur.empty() && !chcExit(d, cur)) { return false; }
            cur.clear();
            return true;
        }
        if (is("goto")) {
            eat();
            std::vector<std::string> targets;
            while (tok_.kind == Token::IDENT) {
                targets.push_back(tok_.text);
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (targets.empty()) {
                d.error(ErrorCode::E_PARSE, "goto requires at least one label", loc());
                return false;
            }
            if (!expectP(";", d)) { return false; }
            if (!cur.empty()) {
                for (const std::string& t : targets) {
                    const std::string lrel = chc_body_ + "!L!" + t;
                    chcRel(lrel, chc_sorts_);
                    chcBeginClause();
                    chcClause(chcApp(cur, chcState({})), chcApp(lrel, chcState({})));
                    chcEndClause();
                }
            }
            cur.clear();
            return true;
        }
        if (is("break")) {
            eat();
            std::string label;
            if (tok_.kind == Token::IDENT) { label = tok_.text; eat(); }
            if (!expectP(";", d)) { return false; }
            int target = -1;
            for (int i = static_cast<int>(chc_breakables_.size()) - 1; i >= 0; --i) {
                if (label.empty() && chc_breakables_[i].is_while) { target = i; break; }
                if (!label.empty() && chc_breakables_[i].label == label) {
                    target = i;
                    break;
                }
            }
            if (target < 0) {
                d.error(ErrorCode::E_TYPE,
                        label.empty()
                            ? "`break` outside a loop"
                            : "`break` target `" + label
                                  + "` is not an enclosing labeled `while` or `if`",
                        loc());
                return false;
            }
            if (!cur.empty()) { chc_breakables_[target].pending.push_back(cur); }
            cur.clear();
            return true;
        }
        if (is("if")) { return chcIf(d, cur); }
        if (is("while")) { return chcWhile(d, cur); }
        if (is("call") || is("free") || is("async")) { return chcCall(d, cur); }
        if (tok_.kind == Token::IDENT) {
            // An assignment: `x := e;` or the parallel form; the head carries
            // the update terms directly over the source state's binders.
            chcBeginClause();
            std::vector<std::string> targets;
            std::vector<std::vector<H::ExprPtr>> target_indices;
            std::unordered_set<std::string> assigned;
            for (;;) {
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected an assignment target", loc());
                    return false;
                }
                const std::string name = tok_.text;
                if (chc_sort_of_.find(name) == chc_sort_of_.end()) {
                    d.error(ErrorCode::E_TYPE, "'" + name + "' is not declared", loc());
                    return false;
                }
                if (!checkWritable(name, d)) { return false; }
                if (!assigned.insert(name).second) {
                    d.error(ErrorCode::E_PARSE,
                            "variable `" + name
                                + "` is assigned more than once in parallel assignment",
                            loc());
                    return false;
                }
                targets.push_back(name);
                eat();
                std::vector<H::ExprPtr> idx;
                while (isP("[")) {
                    const Uir::SourceLoc at = loc();
                    eat();
                    H::ExprPtr i = expr(d);
                    if (!i) { return false; }
                    if (isP(",")) {
                        d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "a multi-index map assignment is not implemented, for "
                                "the reason the multi-index map TYPE is not", at);
                        return false;
                    }
                    if (!expectP("]", d)) { return false; }
                    idx.push_back(std::move(i));
                }
                target_indices.push_back(std::move(idx));
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(":=", d)) { return false; }
            std::vector<H::ExprPtr> rhs;
            for (;;) {
                H::ExprPtr e = expr(d);
                if (!e) { return false; }
                rhs.push_back(e);
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(";", d)) { return false; }
            if (rhs.size() != targets.size()) {
                d.error(ErrorCode::E_TYPE,
                        "this assignment has " + std::to_string(targets.size())
                            + " target(s) and " + std::to_string(rhs.size())
                            + " value(s)",
                        loc());
                return false;
            }
            for (std::size_t i = 0; i < targets.size(); ++i) {
                if (!checkAssignment(chc_sort_of_.at(targets[i]), target_indices[i], rhs[i], d)) {
                    return false;
                }
            }
            if (!cur.empty()) {
                // CHC-COMP heads apply relations to VARIABLES only: the
                // next-state binder is fresh per target and the update
                // equation moves into the body. (z3 accepts terms in heads,
                // but the format -- and the format check -- does not.)
                std::unordered_map<std::string, H::ExprPtr> upd;
                for (std::size_t i = 0; i < targets.size(); ++i) {
                    H::ExprPtr value = rhs[i];
                    if (!target_indices[i].empty()) {
                        H::ExprPtr old = chcVar(targets[i]);
                        value = storeAt(old, target_indices[i], 0, rhs[i], targets[i],
                                        d);
                        if (!value) { return false; }
                    }
                    upd[targets[i]] = value;
                }
                H::ExprPtr eqs;
                const std::vector<H::ExprPtr> head_args = chcStateDistinct(upd, eqs);
                const std::string next = chcFreshRel("p");
                chcClause(conjoin(chcApp(cur, chcState({})), eqs),
                          chcApp(next, head_args));
                cur = next;
            }
            chcEndClause();
            return true;
        }
        d.error(ErrorCode::E_PARSE, "unexpected '" + tok_.text + "' in a statement",
                loc());
        return false;
    }

    /** One procedure in the Horn route: the contract from the pass-1 registry,
     *  the body as clauses, the summary relation as the contract's definition. */
    bool chcProcedure(Uir::Diagnostics& d) {
        const bool implementation = is("implementation");
        const std::size_t declaration_pos = tok_.pos;
        eat();                                       // 'procedure' or 'implementation'
        if (!attributes(d)) { return false; }
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE, "expected a procedure name", loc());
            return false;
        }
        const std::string name = tok_.text;
        eat();
        if (isP("<")) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "procedure type parameters are not implemented", loc());
            return false;
        }
        if (procs_.count(name) == 0) {
            d.error(ErrorCode::E_TYPE,
                    "implementation `" + name + "` has no procedure declaration", loc());
            return false;
        }
        ProcSig sig = procs_.at(name);
        std::vector<std::string> in_names, out_names;
        std::vector<H::Sort> in_sorts, out_sorts;
        // Consume the signature text; the registry already has its content.
        {
            if (!expectP("(", d)) { return false; }
            if (!signatureFormals(d, in_names, in_sorts)) { return false; }
            if (is("returns")) {
                eat();
                if (!expectP("(", d)) { return false; }
                if (!signatureFormals(d, out_names, out_sorts)) { return false; }
            }
            if (implementation && !matchImplementation(name, in_names, in_sorts,
                                                        out_names, out_sorts, d)) {
                return false;
            }
            if (isP(";")) { eat(); }
        }
        chc_contract_names_.clear();
        for (std::size_t i = 0; i < in_names.size(); ++i) {
            chc_contract_names_[sig.in_names[i]] = in_names[i];
        }
        for (std::size_t i = 0; i < out_names.size(); ++i) {
            chc_contract_names_[sig.out_names[i]] = out_names[i];
        }
        sig.in_names = in_names;
        sig.out_names = out_names;
        for (;;) {
            if (is("free")) { eat(); }
            if (is("requires") || is("ensures")) {
                eat();
                if (!attributes(d)) { return false; }
                if (!skipExpression(d) || !expectP(";", d)) { return false; }
            } else if (is("modifies")) {
                eat();
                while (tok_.kind == Token::IDENT) {
                    eat();
                    if (isP(",")) { eat(); }
                }
                if (!expectP(";", d)) { return false; }
            } else {
                break;
            }
        }

        // The state tuple: in-formals, mutable globals now, the same globals
        // at body entry, out-formals, then locals (collected from the body).
        chc_proc_ = name;
        // Every implementation has its own program-point relations, even
        // when several bodies implement the same procedure contract.
        chc_body_ = implementation ? name + "!implementation!" + std::to_string(declaration_pos)
                                   : name;
        chc_point_ = 0;
        chc_names_.clear();
        chc_sorts_.clear();
        chc_sort_of_.clear();
        chc_globals_.clear();
        chc_outs_.clear();
        input_formals_.clear();
        procedure_modifies_.clear();
        for (std::size_t i = 0; i < sig.in_names.size(); ++i) {
            chc_names_.push_back(sig.in_names[i]);
            chc_sorts_.push_back(sig.in_sorts[i]);
            chc_sort_of_[sig.in_names[i]] = sig.in_sorts[i];
            input_formals_.insert(sig.in_names[i]);
        }
        chc_sum_in_ = sig.in_names.size();
        // Deterministic global order: sorted names.
        std::vector<std::string> globals(global_vars_.begin(), global_vars_.end());
        std::sort(globals.begin(), globals.end());
        for (const std::string& g : globals) {
            chc_globals_.push_back(g);
            chc_names_.push_back(g);
            chc_sorts_.push_back(global_sorts_.at(g));
            chc_sort_of_[g] = global_sorts_.at(g);
        }
        for (const std::string& g : chc_globals_) {
            chc_names_.push_back(g + "!entry");
            chc_sorts_.push_back(global_sorts_.at(g));
            chc_sort_of_[g + "!entry"] = global_sorts_.at(g);
        }
        for (std::size_t i = 0; i < sig.out_names.size(); ++i) {
            chc_names_.push_back(sig.out_names[i]);
            chc_sorts_.push_back(sig.out_sorts[i]);
            chc_sort_of_[sig.out_names[i]] = sig.out_sorts[i];
            chc_outs_.push_back(sig.out_names[i]);
        }
        // Constants join the tuple as components nothing ever overrides: the
        // same binder flows through every clause, so a value pinned by an
        // axiom at the entry clause holds at every reachable state.
        std::vector<std::string> cst(consts_.begin(), consts_.end());
        std::sort(cst.begin(), cst.end());
        for (const std::string& c : cst) {
            chc_names_.push_back(c);
            chc_sorts_.push_back(global_sorts_.at(c));
            chc_sort_of_[c] = global_sorts_.at(c);
        }
        for (const std::string& g : sig.modifies_checked) {
            procedure_modifies_.insert(g);
        }
        for (const std::string& g : sig.modifies_free) {
            procedure_modifies_.insert(g);
        }
        // Probe-parses (a guard read once to get past it) resolve names
        // through sorts_; the tuple covers the same names for the clauses.
        sorts_ = global_sorts_;
        for (std::size_t i = 0; i < sig.in_names.size(); ++i) {
            sorts_[sig.in_names[i]] = sig.in_sorts[i];
        }
        for (std::size_t i = 0; i < sig.out_names.size(); ++i) {
            sorts_[sig.out_names[i]] = sig.out_sorts[i];
        }
        // The summary relation: (in, g_entry, g_exit, out).
        {
            std::vector<H::Sort> ssorts;
            ssorts.insert(ssorts.end(), sig.in_sorts.begin(), sig.in_sorts.end());
            for (const std::string& g : chc_globals_) {
                ssorts.push_back(global_sorts_.at(g));
            }
            for (const std::string& g : chc_globals_) {
                ssorts.push_back(global_sorts_.at(g));
            }
            ssorts.insert(ssorts.end(), sig.out_sorts.begin(), sig.out_sorts.end());
            chcRel(name + "!sum", ssorts);
        }

        const bool has_body = isP("{");
        if (!has_body) {
            if (!isP(";") && tok_.kind != Token::END && !is("procedure")
                && !is("implementation") && !is("var") && !is("axiom")
                && !is("const") && !is("function") && !is("type")) {
                d.error(ErrorCode::E_PARSE,
                        "expected a procedure body or the next declaration, found '"
                            + tok_.text + "'",
                        loc());
                return false;
            }
            // A bodiless procedure: the contract alone defines the summary.
            // The ensures are read against the POST state: a modified
            // global's post-state is a fresh binder (the exit position); an
            // unmodified one's exit is tied to the entry -- the frame. Reading
            // the current component instead would tie a modified global to its
            // entry value, which the contract does not say.
            chcBeginClause();
            std::unordered_map<std::string, std::string> exit_of;
            for (const std::string& g : chc_globals_) {
                H::Binder b;
                b.name = "q!" + std::to_string(qv_++) + "!" + g;
                b.sort = chc_sort_of_.at(g);
                chc_binders_.push_back(b);
                exit_of[g] = b.name;
                if (sig.modifies_checked.count(g) != 0) {
                    renamed_binders_[g] = b.name;    // the post-state binder
                }
            }
            H::ExprPtr all;
            for (const ProcContract& c : sig.ensures) {
                H::ExprPtr e = chcReadOwnContract(c, d);
                if (!e) { chcEndClause(); return false; }
                all = conjoin(all, e);
            }
            for (const std::string& g : chc_globals_) {
                if (sig.modifies_checked.count(g) == 0) {
                    all = conjoin(all,
                                  H::mkOp(H::Op::EQ,
                                          {H::mkBoundVar(exit_of[g],
                                                         chc_sort_of_.at(g)),
                                           chcVar(g + "!entry")}));
                }
            }
            std::vector<H::ExprPtr> sargs;
            for (std::size_t i = 0; i < chc_sum_in_; ++i) {
                sargs.push_back(chcVar(sig.in_names[i]));
            }
            for (const std::string& g : chc_globals_) {
                sargs.push_back(chcVar(g + "!entry"));   // g_entry position
            }
            for (const std::string& g : chc_globals_) {
                sargs.push_back(H::mkBoundVar(exit_of[g], chc_sort_of_.at(g)));
            }
            for (const std::string& o : chc_outs_) { sargs.push_back(chcVar(o)); }
            chcClause(all, chcApp(name + "!sum", sargs));
            chcEndClause();
            return true;
        }

        const Mark body_mark = mark();               // tok_ is '{'
        if (!chcCollectLocals(d)) { return false; }
        reset(body_mark);
        saw_procedure_ = true;

        // The entry point: requires (all of them) assumed.
        const std::string entry = chcFreshRel("in");
        {
            chcBeginClause();
            H::ExprPtr ante;
            for (const ProcContract& c : sig.requires) {
                H::ExprPtr e = chcReadOwnContract(c, d, true);
                if (!e) { chcEndClause(); return false; }
                ante = conjoin(ante, e);
            }
            for (const Mark& a : chc_axioms_) {
                H::ExprPtr e = readMarkedExpr(a, d);
                if (!e) { chcEndClause(); return false; }
                ante = conjoin(ante, e);
            }
            // Constants are tuple components in the Horn route, never free
            // declarations. Carry `unique` as an entry assumption over those
            // bound components, just like the source axioms above.
            for (const auto& group : unique_constants_) {
                if (group.second.size() < 2) { continue; }
                std::vector<H::ExprPtr> values;
                for (const std::string& constant : group.second) {
                    values.push_back(chcVar(constant));
                }
                ante = conjoin(ante, H::mkOp(H::Op::DISTINCT, std::move(values), loc()));
            }
            // At entry the entry-globals ARE the current ones -- tied in the
            // body, since the head's arguments are distinct variables.
            std::unordered_map<std::string, H::ExprPtr> id;
            H::ExprPtr eqs;
            for (const std::string& g : chc_globals_) {
                id[g + "!entry"] = chcVar(g);
            }
            const std::vector<H::ExprPtr> head_args = chcStateDistinct(id, eqs);
            chcClause(conjoin(ante, eqs), chcApp(entry, head_args));
            chcEndClause();
        }
        std::string cur = entry;
        if (!chcList(d, cur)) { return false; }
        if (!cur.empty()) { return chcExit(d, cur); }
        return true;
    }

    // ---- Expressions -------------------------------------------------------

    H::ExprPtr expr(Uir::Diagnostics& d) { return parseImplies(d); }

    bool firstMutableGlobal(const H::ExprPtr& e, std::string& out) const {
        if (!e) { return false; }
        if (e->kind == H::ExprKind::IDENT) {
            for (const std::string& global : global_vars_) {
                if (e->name == global
                    || (e->name.size() > global.size() + 1
                        && e->name.compare(0, global.size(), global) == 0
                        && e->name[global.size()] == '@')) {
                    out = global;
                    return true;
                }
            }
        }
        for (const H::ExprPtr& arg : e->args) {
            if (firstMutableGlobal(arg, out)) { return true; }
        }
        return false;
    }

    bool checkAssignment(const H::Sort& target, const std::vector<H::ExprPtr>& indices,
                         const H::ExprPtr& value, Uir::Diagnostics& d) const {
        const H::Sort* expected = &target;
        for (const auto& index : indices) {
            if (expected->kind != H::SortKind::ARRAY || !expected->index || !expected->elem
                || !H::sameSort(*expected->index, index->sort)) {
                d.error(ErrorCode::E_TYPE, "assignment map index has an incompatible type", index->loc);
                return false;
            }
            expected = expected->elem.get();
        }
        // Check before VC pruning: an empty-obligation or unreachable body
        // can discard its assignment equations before the HIR type checker.
        if (!H::sameSort(*expected, value->sort)) {
            d.error(ErrorCode::E_TYPE,
                    "assignment value has type " + H::toString(value->sort)
                        + ", expected " + H::toString(*expected), value->loc);
            return false;
        }
        return true;
    }

    bool checkWritable(const std::string& name, Uir::Diagnostics& d) const {
        if (consts_.count(name) != 0 || input_formals_.count(name) != 0) {
            d.error(ErrorCode::E_TYPE,
                    "assignment target `" + name
                        + "` is immutable (a const or input formal)", loc());
            return false;
        }
        if (global_vars_.count(name) != 0
            && procedure_modifies_.count(name) == 0) {
            d.error(ErrorCode::E_TYPE,
                    "assignment to global `" + name
                        + "` is not permitted by the enclosing procedure's modifies clause",
                    loc());
            return false;
        }
        return true;
    }

    H::ExprPtr parseImplies(Uir::Diagnostics& d) {
        H::ExprPtr l = parseOr(d);
        if (!l) { return nullptr; }
        if (isP("==>")) {
            eat();
            H::ExprPtr r = parseImplies(d);        // right-associative
            if (!r) { return nullptr; }
            return H::mkOp(H::Op::IMPLIES, {l, r});
        }
        return l;
    }
    H::ExprPtr parseOr(Uir::Diagnostics& d) {
        H::ExprPtr l = parseAnd(d);
        if (!l) { return nullptr; }
        while (isP("||")) {
            eat();
            H::ExprPtr r = parseAnd(d);
            if (!r) { return nullptr; }
            l = H::mkOp(H::Op::OR, {l, r});
        }
        return l;
    }
    H::ExprPtr parseAnd(Uir::Diagnostics& d) {
        H::ExprPtr l = parseCmp(d);
        if (!l) { return nullptr; }
        while (isP("&&")) {
            eat();
            H::ExprPtr r = parseCmp(d);
            if (!r) { return nullptr; }
            l = H::mkOp(H::Op::AND, {l, r});
        }
        return l;
    }
    H::ExprPtr parseCmp(Uir::Diagnostics& d) {
        H::ExprPtr l = parseConcat(d);
        if (!l) { return nullptr; }
        static const std::unordered_map<std::string, H::Op> kCmp = {
            {"==", H::Op::EQ}, {"<", H::Op::LT}, {">", H::Op::GT},
            {"<=", H::Op::LE}, {">=", H::Op::GE},
        };
        if (tok_.kind == Token::PUNCT) {
            if (tok_.text == "!=") {
                eat();
                H::ExprPtr r = parseConcat(d);
                if (!r) { return nullptr; }
                return H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {l, r})});
            }
            const auto it = kCmp.find(tok_.text);
            if (it != kCmp.end()) {
                const H::Op op = it->second;
                eat();
                H::ExprPtr r = parseConcat(d);
                if (!r) { return nullptr; }
                return H::mkOp(op, {l, r});
            }
        }
        return l;
    }
    H::ExprPtr parseConcat(Uir::Diagnostics& d) {
        H::ExprPtr left = parseAdd(d);
        if (!left) { return nullptr; }
        while (isP("++")) {
            const auto at = loc();
            eat();
            H::ExprPtr right = parseAdd(d);
            if (!right) { return nullptr; }
            if (left->sort.kind != H::SortKind::BITVEC || right->sort.kind != H::SortKind::BITVEC
                || left->sort.width > std::numeric_limits<unsigned>::max() - right->sort.width) {
                d.error(ErrorCode::E_TYPE, "bit-vector concatenation needs two valid bit-vector widths", at);
                return nullptr;
            }
            left = H::mkOp(H::Op::BV_CONCAT, {left, right}, at);
        }
        return left;
    }
    H::ExprPtr parseAdd(Uir::Diagnostics& d) {
        H::ExprPtr l = parseMul(d);
        if (!l) { return nullptr; }
        while (isP("+") || isP("-")) {
            const bool plus = isP("+");
            eat();
            H::ExprPtr r = parseMul(d);
            if (!r) { return nullptr; }
            l = H::mkOp(plus ? H::Op::ADD : H::Op::SUB, {l, r});
        }
        return l;
    }
    H::ExprPtr parseMul(Uir::Diagnostics& d) {
        H::ExprPtr l = parseAtom(d);
        if (!l) { return nullptr; }
        for (;;) {
            if (isP("*")) {
                eat();
                H::ExprPtr r = parseAtom(d);
                if (!r) { return nullptr; }
                l = H::mkOp(H::Op::MUL, {l, r});
            } else if (is("div") || is("mod")) {
                // §4.5, the fifth language to hit this. Boogie's `div` and `mod`
                // are SMT-LIB's -- the language is defined by translation to
                // SMT-LIB -- so this is the one frontend in the batch that
                // names EUCLID rather than TRUNC, and naming it is the whole
                // difference on a negative dividend.
                const bool is_div = is("div");
                eat();
                H::ExprPtr r = parseAtom(d);
                if (!r) { return nullptr; }
                l = H::mkOp(is_div ? H::Op::DIV_EUCLID : H::Op::MOD_EUCLID, {l, r});
            } else {
                break;
            }
        }
        return l;
    }

    /** Skip to the start of the next top-level item.
     *
     *  Boogie items end in a `;` or in a `{ ... }` body, and a procedure has
     *  both -- `requires a <= b;` sits at brace depth 0 -- so "skip to the next
     *  semicolon" would stop in the middle of one. Stopping at the next
     *  item KEYWORD at depth 0 is what actually delimits them: a local `var` is
     *  inside a body and therefore at depth 1 or more. */
    void skipItem() {
        int depth = 0;
        eat();                                    // the keyword that starts this item
        while (tok_.kind != Token::END) {
            if (isP("{")) { ++depth; }
            else if (isP("}")) { if (depth > 0) { --depth; } }
            else if (depth == 0 && tok_.kind == Token::IDENT
                     && (is("var") || is("const") || is("function") || is("type")
                         || is("axiom") || is("procedure") || is("implementation"))) {
                return;
            }
            eat();
        }
    }

    /** `uses { axiom P; axiom Q; }` on a const or function.
     *
     *  Boogie includes these axioms only when the symbol is used, which is a
     *  performance device: including them unconditionally cannot change the
     *  answer, because an axiom about a symbol nothing references constrains
     *  nothing. Dropping them WOULD change it, so they are parsed rather than
     *  skipped. */
    bool usesClause(Uir::Diagnostics& d) {
        had_uses_ = false;
        if (!is("uses")) { return true; }
        had_uses_ = true;
        eat();
        if (!isP("{")) {
            d.error(ErrorCode::E_PARSE, "expected '{' after 'uses'", loc());
            return false;
        }
        // In the DECLARATION pass the block is recorded and skipped, not read:
        // its axioms may name a function declared further down the file --
        // TuringFactorial.bpl's `Factorial` uses `Factorial_Aux`, declared five
        // lines later -- and Boogie does not order declarations. Parsed after
        // pass 1, when every symbol exists.
        // Recorded and skipped here, read by readUsesBody once every
        // declaration exists. The mark points at the `{`, which is why the
        // deferred reader takes the body and not the `uses` keyword.
        pending_uses_.push_back(mark());
        int depth = 0;
        do {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated 'uses' block", loc());
                return false;
            }
            if (isP("{")) { ++depth; }
            else if (isP("}")) { --depth; }
            eat();
        } while (depth > 0);
        return true;
    }

    /** The `{ axiom ...; }` body of a `uses` clause, read after pass 1.
     *
     *  Split from usesClause because the recorded mark points at the `{`: a
     *  deferred call that went back through usesClause would look for `uses`,
     *  not find it, and return success having read NOTHING -- dropping the
     *  axioms silently, which is the failure this project exists to refuse.
     *  Its own test caught exactly that. */
    bool readUsesBody(Uir::Diagnostics& d) {
        if (!expectP("{", d)) { return false; }
        while (!isP("}")) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE, "unterminated 'uses' block", loc());
                return false;
            }
            if (!is("axiom")) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "only 'axiom' is read inside a 'uses' block, found '"
                            + tok_.text + "'",
                        loc());
                return false;
            }
            if (!axiom(d)) { return false; }
        }
        return expectP("}", d);
    }

    /** `f(a, b)` -- an application of a declared function. */
    H::ExprPtr application(const std::string& name, std::size_t arity,
                           const Uir::SourceLoc& at, Uir::Diagnostics& d) {
        if (!expectP("(", d)) { return nullptr; }
        std::vector<H::ExprPtr> args;
        while (!isP(")")) {
            H::ExprPtr a = expr(d);
            if (!a) { return nullptr; }
            args.push_back(a);
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(")", d)) { return nullptr; }
        if (args.size() != arity) {
            d.error(ErrorCode::E_TYPE,
                    "'" + name + "' takes " + std::to_string(arity)
                        + " argument(s), not " + std::to_string(args.size()),
                    at);
            return nullptr;
        }
        const auto& params = funParams_.at(name);
        for (std::size_t i = 0; i < args.size(); ++i) {
            if (!H::sameSort(args[i]->sort, params[i])) {
                d.error(ErrorCode::E_TYPE,
                        "argument " + std::to_string(i + 1) + " of '" + name
                            + "' has type " + H::toString(args[i]->sort)
                            + ", expected " + H::toString(params[i]), at);
                return nullptr;
            }
        }
        const auto builtin = builtins_.find(name);
        if (builtin != builtins_.end()) { return applyBuiltin(builtin->second, args, at); }
        return H::mkApply(name, funResult_.at(name), args, at);
    }

    /**
     * `(forall j: int :: P(j))`, `(exists k: int, m: int :: Q(k, m))`.
     *
     * Bound variables go in `bound_` and NOT in `sorts_`: a bound variable is
     * not a free variable of the model, and one that reached `decls` would be
     * reported by features() and become eligible for the bound-ints pass.
     * Shadowing is saved and restored, so `forall x :: ... forall x :: ...` --
     * legal, and what a generated verification condition looks like -- binds
     * the inner one.
     *
     * A trigger (`{ f(j) }`) is skipped: it is a solver hint that constrains
     * nothing, in the same class as a MiniZinc search annotation.
     */
    H::ExprPtr quantifier(Uir::Diagnostics& d) {
        const bool is_forall = is("forall");
        const Uir::SourceLoc at = loc();
        eat();
        std::vector<H::Binder> binders;
        std::vector<std::pair<std::string, bool>> shadowed;   // name, had_previous
        std::vector<H::Sort> previous;
        std::vector<std::string> previous_renamed;
        for (;;) {
            std::vector<std::string> group;
            for (;;) {
                if (tok_.kind != Token::IDENT) {
                    d.error(ErrorCode::E_PARSE, "expected a bound variable name", loc());
                    return nullptr;
                }
                group.push_back(tok_.text);
                eat();
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (!expectP(":", d)) { return nullptr; }
            H::Sort s;
            if (!type(s, d)) { return nullptr; }
            if (!whereClauseRefused(d)) { return nullptr; }
            for (const std::string& n : group) {
                const auto old_it = bound_.find(n);
                shadowed.emplace_back(n, old_it != bound_.end());
                previous.push_back(old_it != bound_.end() ? old_it->second : H::Sort{});
                previous_renamed.push_back(old_it != bound_.end()
                                               ? renamed_binders_[n]
                                               : std::string());
                H::Binder b;
                // Alpha-renamed ALWAYS, not only on a visible collision.
                //
                // Boogie scopes an axiom's binders separately from a
                // procedure's parameters, so `axiom (forall a,b: int :: ...)`
                // beside `procedure T(a,b: int)` is ordinary Boogie -- and the
                // HIR type check refuses a binder that shadows a declaration,
                // because downstream a shadowed binder cannot be told from the
                // free variable.
                //
                // Renaming only on collision does not work, and DivMod.bpl is
                // why: its axioms come BEFORE the procedure that declares `a`
                // and `b`, so at the moment the binder is created there is
                // nothing to collide with, and the clash appears only when
                // typeCheck sees the finished model. The decision would have to
                // depend on declarations not yet read.
                //
                // So every binder gets a name nothing else can have. The source
                // name is kept as a suffix so the emitted script still reads
                // like the input.
                b.name = "q!" + std::to_string(qv_++) + "!" + n;
                b.sort = s;
                binders.push_back(b);
                bound_[n] = s;
                renamed_binders_[n] = b.name;
            }
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(":", d) || !expectP(":", d)) { return nullptr; }
        // A TRIGGER is `{ f(n) }` -- braces with no colon -- and an attribute is
        // `{: name ... }`. Both may appear here and neither constrains the
        // model: a trigger tells the solver when to instantiate, which changes
        // how long the proof takes and not which models exist. `attributes`
        // alone left the trigger's `{` to the expression parser, which reported
        // "unexpected '{' in an expression" about a construct the author wrote
        // correctly.
        while (isP("{")) {
            int depth = 0;
            do {
                if (tok_.kind == Token::END) {
                    d.error(ErrorCode::E_PARSE,
                            "unterminated trigger or attribute in a quantifier", loc());
                    return nullptr;
                }
                if (isP("{")) { ++depth; }
                else if (isP("}")) { --depth; }
                eat();
            } while (depth > 0);
        }
        H::ExprPtr body = expr(d);
        for (std::size_t i = shadowed.size(); i > 0; --i) {
            const auto& sh = shadowed[i - 1];
            if (sh.second) {
                bound_[sh.first] = previous[i - 1];
                renamed_binders_[sh.first] = previous_renamed[i - 1];
            } else {
                bound_.erase(sh.first);
                renamed_binders_.erase(sh.first);
            }
        }
        if (!body) { return nullptr; }
        return is_forall ? H::mkForall(binders, body, at)
                         : H::mkExists(binders, body, at);
    }

    /** Skip ordinary verifier/source annotations. Semantic function attributes
     *  are handled by functionAttributes, and semantic type attributes by the
     *  type collector; interpreting those as hints would erase their meaning. */
    bool attributes(Uir::Diagnostics& d) {
        while (isP("{")) {
            if (!lex_.peekIsColonAfterBrace()) { return true; }   // a body, not an attribute
            eat();                                // '{'
            if (!expectP(":", d)) { return false; }
            int depth = 1;
            while (depth > 0) {
                if (tok_.kind == Token::END) {
                    d.error(ErrorCode::E_PARSE, "unterminated attribute", loc());
                    return false;
                }
                if (isP("{")) { ++depth; }
                else if (isP("}")) { --depth; }
                eat();
            }
        }
        return true;
    }

    /** The current procedure's entry alias, declared and tied on first use.
     *  Entry SSA versions are unique across procedures. Include that version
     *  in the alias too: resetting old_aliases_ cannot reuse one global x@old
     *  declaration for several independent procedure-entry states. The @old
     *  suffix is outside source identifiers and ordinary numeric SSA names,
     *  and keeps finalise() from rewriting an old value to the current one. */
    std::string oldAlias(const std::string& name, const H::Sort& s) {
        const auto it = old_aliases_.find(name);
        if (it != old_aliases_.end()) { return it->second; }
        const std::string alias = entry_versions_.at(name) + "@old";
        // Dead code discards the expression anyway; recording the alias would
        // leave a name a later live old() reuses but nothing declares.
        if (dead_) { return alias; }
        old_aliases_[name] = alias;
        declare(alias, s);
        // The tie is to the RECORDED entry version: not current(name), which
        // drifts with the body, and not the base name, which for a non-first
        // procedure is ANOTHER procedure's entry value. And deliberately not
        // the guarded addAssume: the tie holds in EVERY state, including paths
        // where the alias's first mention sits under a branch guard.
        H::Constraint c;
        c.loc = loc();
        c.formula = H::mkOp(H::Op::EQ,
                            {H::mkIdent(alias, s),
                             H::mkIdent(entry_versions_.at(name), s)});
        model_->constraints.push_back(c);
        return alias;
    }

    /** `store` @p value into @p base at @p idx[from...], nesting for a map of
     *  maps: `m[i][j] := v` rebuilds the inner map and then stores THAT back
     *  into the outer one, because assigning a cell of a nested map is an
     *  assignment to the outer map. */
    H::ExprPtr storeAt(const H::ExprPtr& base, const std::vector<H::ExprPtr>& idx,
                       std::size_t from, const H::ExprPtr& value,
                       const std::string& name, Uir::Diagnostics& d) {
        if (base->sort.kind != H::SortKind::ARRAY) {
            d.error(ErrorCode::E_TYPE,
                    "'" + name + "' is " + H::toString(base->sort)
                        + ", which is not a map, so it cannot be indexed",
                    base->loc);
            return nullptr;
        }
        if (from + 1 == idx.size()) {
            return H::mkOp(H::Op::STORE, {base, idx[from], value});
        }
        H::ExprPtr inner = H::mkOp(H::Op::SELECT, {base, idx[from]});
        H::ExprPtr updated = storeAt(inner, idx, from + 1, value, name, d);
        if (!updated) { return nullptr; }
        return H::mkOp(H::Op::STORE, {base, idx[from], updated});
    }

    /** Postfix map reads, functional map updates and bit-vector extractions.
     *
     *  Chained because a map may hold maps: `m[i][j]` reads the inner map out
     *  of the outer one and then indexes it, which is two selects and not a
     *  two-index read. `[i, j]` is the two-index form and is refused by
     *  type() -- accepting it here would let a multi-index map in through the
     *  expression grammar after the type grammar had declined it. */
    H::ExprPtr mapReads(H::ExprPtr base, const std::string& name,
                        Uir::Diagnostics& d) {
        while (isP("[")) {
            const Uir::SourceLoc at = loc();
            if (base->sort.kind == H::SortKind::BITVEC) {
                // Boogie's [end:start] excludes end; SMT extract includes its
                // high index. The upstream BvExtractExpr result has end-start bits.
                eat();
                unsigned end = 0, start = 0;
                if (tok_.kind != Token::INT || !unsignedDecimal(tok_.text, end)) {
                    d.error(ErrorCode::E_TYPE, "bit-vector extraction needs literal end:start bounds", at);
                    return nullptr;
                }
                eat();
                if (!expectP(":", d)) { return nullptr; }
                if (tok_.kind != Token::INT || !unsignedDecimal(tok_.text, start)) {
                    d.error(ErrorCode::E_TYPE, "bit-vector extraction needs literal end:start bounds", at);
                    return nullptr;
                }
                eat();
                if (!expectP("]", d)) { return nullptr; }
                if (start >= end || end > base->sort.width) {
                    d.error(ErrorCode::E_TYPE,
                            "bit-vector extraction requires 0 <= start < end <= width; zero-width values are not supported", at);
                    return nullptr;
                }
                base = H::mkBvExtract(base, end - 1, start, at);
                continue;
            }
            if (base->sort.kind != H::SortKind::ARRAY) {
                d.error(ErrorCode::E_TYPE,
                        "'" + name + "' is " + H::toString(base->sort)
                            + ", which is not a map, so it cannot be indexed",
                        at);
                return nullptr;
            }
            eat();                                  // '['
            H::ExprPtr idx = expr(d);
            if (!idx) { return nullptr; }
            if (isP(",")) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a multi-index map read is not implemented, for the reason the "
                        "multi-index map TYPE is not", at);
                return nullptr;
            }
            if (isP(":=")) {
                eat();
                H::ExprPtr value = expr(d);
                if (!value || !expectP("]", d)) { return nullptr; }
                base = H::mkOp(H::Op::STORE, {base, idx, value}, at);
            } else {
                if (!expectP("]", d)) { return nullptr; }
                base = H::mkOp(H::Op::SELECT, {base, idx}, at);
            }
        }
        return base;
    }

    H::ExprPtr parseAtom(Uir::Diagnostics& d) {
        if (isP("(")) {
            eat();
            H::ExprPtr e = expr(d);
            if (!e || !expectP(")", d)) { return nullptr; }
            return mapReads(e, "(...)", d);
        }
        if (isP("!")) {
            eat();
            H::ExprPtr e = parseAtom(d);
            if (!e) { return nullptr; }
            return H::mkOp(H::Op::NOT, {e});
        }
        if (isP("-")) {
            eat();
            H::ExprPtr e = parseAtom(d);
            if (!e) { return nullptr; }
            return H::mkOp(H::Op::NEG, {e});
        }
        if (tok_.kind == Token::INT) {
            const std::string v = tok_.text;
            const auto at = loc();
            eat();
            if (tok_.kind == Token::IDENT && tok_.text.size() > 2
                && tok_.text.compare(0, 2, "bv") == 0
                && std::isdigit(static_cast<unsigned char>(tok_.text[2]))) {
                unsigned width = 0;
                if (!unsignedDecimal(tok_.text.substr(2), width) || width == 0
                    || !fitsBitVector(v, width)) {
                    d.error(ErrorCode::E_TYPE,
                            "bit-vector literal '" + v + tok_.text
                                + "' has invalid width or an out-of-range value", at);
                    return nullptr;
                }
                eat();
                return mapReads(H::mkBitVec(v, width, at), "bit-vector literal", d);
            }
            return H::mkInt(v, at);
        }
        if (is("true") || is("false")) {
            const bool v = is("true");
            eat();
            return H::mkBool(v);
        }
        if (is("forall") || is("exists")) {
            return quantifier(d);
        }
        if (is("if")) {
            // `if c then a else b` -- an expression, not a statement. Boogie
            // spells the conditional term this way and DivMod.bpl's `abs` is
            // nothing else.
            const Uir::SourceLoc at = loc();
            eat();
            H::ExprPtr c = expr(d);
            if (!c) { return nullptr; }
            if (!is("then")) {
                d.error(ErrorCode::E_PARSE, "expected 'then'", loc());
                return nullptr;
            }
            eat();
            H::ExprPtr a = expr(d);
            if (!a) { return nullptr; }
            if (!is("else")) {
                d.error(ErrorCode::E_PARSE, "expected 'else'", loc());
                return nullptr;
            }
            eat();
            H::ExprPtr b = expr(d);
            if (!b) { return nullptr; }
            return H::mkOp(H::Op::ITE, {c, a, b}, at);
        }
        if (is("old")) {
            // `old(e)` is e evaluated in the PRE-state. Under SSA that is
            // already a name this frontend has: assignments create `x@2`,
            // `x@3`, ..., so the unversioned `x` never stops meaning the entry
            // value.
            //
            // It cannot be emitted AS `x`, because finalise() rewrites every
            // identifier whose name is a program variable to its final version
            // -- that is what makes an `ensures` mean the post-state. So an
            // entry ALIAS is declared instead, tied to the entry name once. The
            // tie is timing-independent for the same reason: `x` is never
            // reassigned, so `x@old = x` holds wherever it is stated.
            //
            // Which identifiers get an alias is This is Boogie 2 §4.3's rule:
            // old distributes to the leaves and is THE IDENTITY on every leaf
            // that is not a global variable, so a local or an out-parameter
            // keeps its current version. At a call site the "pre-state" is the
            // state at call entry, not the caller's entry -- old_overrides_.
            // A precondition may not use old at all (§8).
            if (in_requires_) {
                d.error(ErrorCode::E_TYPE,
                        "a precondition is not allowed to use old expressions "
                        "(This is Boogie 2 §8)",
                        loc());
                return nullptr;
            }
            const Uir::SourceLoc at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            const bool saved = in_old_;
            in_old_ = true;
            H::ExprPtr e = expr(d);
            in_old_ = saved;
            if (!e || !expectP(")", d)) { return nullptr; }
            (void)at;
            // `old(a)[i]` -- the index applies to the RESULT. A suffix can
            // follow any expression that has a map sort, not only a bare name.
            return mapReads(e, "old(...)", d);
        }
        if (tok_.kind == Token::IDENT) {
            const std::string name = tok_.text;
            const Uir::SourceLoc at = loc();
            // A quantifier-bound variable is looked up FIRST and is not a free
            // variable of the model: putting it in sorts_ would let it escape
            // into decls and be reported as one.
            const auto bit = bound_.find(name);
            if (bit != bound_.end()) {
                eat();
                if (chc_mode_ && in_old_ && global_vars_.count(name) != 0) {
                    // In the Horn route old(g) is the global's ENTRY binder.
                    const auto eit = bound_.find(name + "!entry");
                    if (eit != bound_.end()) {
                        return mapReads(H::mkBoundVar(renamed_binders_.at(
                                                          name + "!entry"),
                                                      eit->second, at),
                                        name, d);
                    }
                }
                const auto rn = renamed_binders_.find(name);
                // A bound variable of map sort reads through it: `forall m:
                // [int]int :: m[k] ...`.
                return mapReads(H::mkBoundVar(rn == renamed_binders_.end()
                                                  ? name
                                                  : rn->second,
                                              bit->second, at),
                                name, d);
            }
            // A formal of a contract clause being re-read at a call site
            // stands for the caller-side expression bindCallFormals gave it.
            const auto cfit = call_formals_.find(name);
            if (cfit != call_formals_.end()) {
                eat();
                return mapReads(cfit->second, name, d);
            }
            if (contract_forbidden_.count(name) != 0) {
                d.error(ErrorCode::E_TYPE,
                        "a precondition cannot refer to out-parameter `" + name + "`",
                        at);
                return nullptr;
            }
            const auto fit = funs_.find(name);
            if (fit != funs_.end()) {
                eat();
                H::ExprPtr call = application(name, fit->second, at, d);
                if (!call) { return nullptr; }
                return mapReads(call, name, d);
            }
            const auto it = sorts_.find(name);
            if (it == sorts_.end()) {
                d.error(ErrorCode::E_TYPE, "'" + name + "' is not declared", loc());
                return nullptr;
            }
            if (contract_scope_ && global_vars_.count(name) == 0
                && consts_.count(name) == 0) {
                // A contract clause's scope is the globals, the constants, the
                // functions and the callee's formals -- not whatever the
                // caller happens to have in scope under the same name.
                d.error(ErrorCode::E_TYPE,
                        "'" + name + "' is a local variable, which a contract clause "
                            "cannot name",
                        at);
                return nullptr;
            }
            eat();
            // A constant has no versions -- see constDecl -- so it is named
            // directly rather than through current(), which would hand back a
            // version that was never declared if a local shared its name.
            // A constant has the same value in both states, so `old(c)` is
            // `c` and needs no alias.
            if (in_old_) {
                const auto ov = old_overrides_.find(name);
                if (ov != old_overrides_.end()) {
                    return mapReads(ov->second, name, d);
                }
            }
            const std::string resolved =
                consts_.count(name) != 0 ? name
                : in_old_ && global_vars_.count(name) != 0
                    ? oldAlias(name, it->second)
                    // old() is the identity on a non-global (§4.3): a local or
                    // an out-parameter keeps its current version.
                    : current(name);
            H::ExprPtr base = H::mkIdent(resolved, it->second, at);
            // `m[i]`, and `m[i][j]` for a map whose values are maps. A read is
            // `select`, exactly, because both a Boogie map and an SMT-LIB array
            // are total.
            return mapReads(base, name, d);
        }
        d.error(ErrorCode::E_PARSE, "unexpected '" + tok_.text + "' in an expression",
                loc());
        return nullptr;
    }

    Lexer       lex_;
    std::string file_;
    Token       tok_;
    H::ConstraintModelPtr model_;
    Uir::TranslationReport* report_ = nullptr;
    std::unordered_map<std::string, H::Sort> sorts_;
    std::unordered_map<std::string, NamedType> named_types_;
    std::unordered_map<std::string, H::Sort> global_sorts_;
    std::unordered_set<std::string> global_vars_;
    std::unordered_map<std::string, unsigned> version_;
    /** Monotone mint counter per name -- see fresh(). */
    std::unordered_map<std::string, unsigned> mint_;
    /** True while parsing the argument of `old(...)`, so an identifier
     *  resolves to its entry alias instead of its current version. */
    bool in_old_ = false;
    /** True while reading a `requires` clause, where old() is not allowed
     *  (This is Boogie 2 §8). */
    bool in_requires_ = false;
    /** True while re-reading a contract clause at a call site: an identifier's
     *  scope there is the globals, constants, functions and the callee's
     *  formals -- not the caller's locals. */
    bool contract_scope_ = false;
    /** Program variable -> its entry alias, declared on first use. */
    std::unordered_map<std::string, std::string> old_aliases_;
    /** Global -> its SSA version at the current procedure's entry, recorded
     *  there so old() and contract parsing name the right entry state. */
    std::unordered_map<std::string, std::string> entry_versions_;
    /** At a call site, old(g) for a global g is g's version at CALL entry,
     *  not the caller's procedure entry; the map is populated per call. */
    std::unordered_map<std::string, H::ExprPtr> old_overrides_;
    std::unordered_map<std::string, ProcSig> procs_;
    /** Formal -> caller-side expression, while a contract clause is re-read at
     *  a call site. See bindCallFormals. */
    std::unordered_map<std::string, H::ExprPtr> call_formals_;
    /** Out-parameter names while a `requires` clause is re-read: a
     *  precondition may not name one (This is Boogie 2 §8). */
    std::unordered_set<std::string> contract_forbidden_;
    /** Quantifier-bound variables in scope. Kept apart from sorts_ because a
     *  bound variable is not a free variable of the model. */
    std::unordered_map<std::string, H::Sort> bound_;
    /** Source binder name -> emitted name, for a binder alpha-renamed because
     *  it collided with a model variable. See quantifier(). */
    std::unordered_map<std::string, std::string> renamed_binders_;
    unsigned qv_ = 0;
    /** Declared functions: arity and result sort, for checking an application. */
    std::unordered_map<std::string, std::size_t> funs_;
    std::unordered_map<std::string, H::Sort>     funResult_;
    std::unordered_map<std::string, std::vector<H::Sort>> funParams_;
    std::unordered_map<std::string, BuiltinFunction> builtins_;
    std::vector<FunctionBody> pending_functions_;
    /** Constants, which are never versioned -- see constDecl. */
    std::unordered_set<std::string> consts_;
    /** Incoming formals are immutable; outgoing formals and locals are mutable. */
    std::unordered_set<std::string> input_formals_;
    /** Mutable globals the current procedure is allowed to assign. */
    std::unordered_set<std::string> procedure_modifies_;
    bool infer_modifies_ = false;
    std::vector<Mark> inference_implementations_;
    std::vector<std::pair<std::string, Mark>> inference_bodies_;
    std::unordered_set<std::string>* inference_calls_ = nullptr;
    /** All unique constants by source type; uniqueness crosses declarations. */
    std::unordered_map<std::string, std::vector<std::string>> unique_constants_;
    /** True while collecting declarations; see parse(). */
    bool decl_pass_ = false;
    /** Whether the declaration just parsed carried a `uses { ... }` block,
     *  which takes the place of its terminating semicolon. */
    bool had_uses_ = false;
    /** `uses { ... }` blocks recorded during the declaration pass, read once
     *  every declaration exists. See usesClause. */
    std::vector<Mark> pending_uses_;
    bool saw_procedure_ = false;
    unsigned procedure_count_ = 0;
    std::vector<H::ExprPtr> procedure_refutations_;
    /** A proof obligation and the end of the constraint prefix in force where
     *  it occurs. The timestamp is semantic: later assumptions must not alter
     *  whether an earlier assertion has a counterexample. */
    struct ObligationPoint {
        H::ExprPtr formula;
        std::size_t prefix_end = 0;
    };
    std::vector<ObligationPoint> obligations_;
    /** The conjunction of assumptions that must hold for control to reach the
     *  current point, or null for "no condition". Loops and branches create
     *  one; a join resets it. */
    H::ExprPtr path_guard_;
    /** True between a transfer command (`return`; with 2b also `goto`/`break`)
     *  and the next label: the code is parsed and type-checked but has no VC
     *  effect, matching the reference's pruning of unreachable blocks. */
    bool dead_ = false;
    /** The current procedure's checked postconditions, obligatorified at every
     *  exit point (the final fall-through and each `return`). */
    std::vector<H::ExprPtr> body_ensures_;
    /** The current procedure body's pre-scan; computed once at the body's
     *  `{`, before any statement is processed. */
    BodyScan body_scan_;
    /** Scan-time state: per-list builds (segments), every goto with its
     *  nesting chain, whether each list is a while body, and the recursion
     *  stack of list ids. */
    std::map<std::size_t, ScanListBuild> scan_builds_;
    std::vector<GotoRecord> scan_gotos_;
    std::unordered_map<std::size_t, bool> list_while_;
    std::vector<std::size_t> scan_stack_;
    /** The open statement lists, innermost last. */
    std::vector<ListFrame> frames_;
    /** The enclosing break targets, innermost last. */
    std::vector<Breakable> breakables_;
    /** Labels just processed, waiting to see whether they name the `while` or
     *  `if` that follows them (`L: while ...` makes L a break target). */
    std::vector<std::string> pending_labels_;
    /** Constraint indices where enclosing `while` bodies began, outermost
     *  first -- the fold point for escaping edges. */
    std::vector<std::size_t> while_body_starts_;
    /** Head contexts (invariants and guard) of enclosing `while` bodies,
     *  outermost first -- what an escaping edge must carry. */
    std::vector<H::ExprPtr> while_body_contexts_;
    /** Counter naming the fresh Boolean of an `if (*)` condition. */
    unsigned star_ = 0;
    /** Counter naming the fresh Boolean gate of a multi-edge join. */
    unsigned edge_ = 0;

    /** D7's Horn route (boogie.md §4.6): emit constrained Horn clauses from
     *  the same parse instead of the formula VC. Set by the `chc` option. */
    bool chc_mode_ = false;
    /** Axioms (and ground function definitions) by MARK: re-read inside each
     *  procedure's entry clause, where constants are tuple binders. */
    std::vector<Mark> chc_axioms_;
    /** The current procedure's name prefix, per-point relation counter, and
     *  state tuple: in-formals, globals now, globals at entry, out-formals,
     *  locals. */
    std::string chc_proc_;
    std::string chc_body_;
    std::unordered_map<std::string, std::string> chc_contract_names_;
    unsigned chc_point_ = 0;
    std::vector<std::string> chc_names_;
    std::vector<H::Sort> chc_sorts_;
    std::unordered_map<std::string, H::Sort> chc_sort_of_;
    std::vector<std::string> chc_globals_;
    std::vector<std::string> chc_outs_;
    std::size_t chc_sum_in_ = 0;
    std::unordered_set<std::string> chc_rels_;
    std::vector<H::Binder> chc_binders_;
    /** The current clause's tuple binder names -- for the fresh-vs-component
     *  distinction in chcStateDistinct. */
    std::unordered_set<std::string> chc_tuple_binders_;
    std::vector<ChcBreakable> chc_breakables_;
    bool said_axiom_ = false;
    bool said_map_profile_ = false;
    bool said_modifies_ = false;
    bool said_call_ = false;
};

class BoogieLanguage : public Language {
public:
    BoogieLanguage() {
        // Sixteen, not twelve. `const`, `function` (declared and defined),
        // quantifiers, and the declaration order Boogie actually has were four
        // targets the table did not count, and running Boogie's own
        // Test/textbook -- 0 of 6 -- is what named them. See
        // instances/upstream/PROVENANCE.md.
        // Seventeen, and the last row split. Maps and old() both landed, and
        // the corpus is what says why they belong together: after them, every
        // remaining failure in Boogie's own Test/textbook is CONTROL FLOW.
        // That is one decision -- how a loop's invariant is encoded, §4.3 --
        // rather than the five separate gaps this table used to list, so the
        // rows below name the decision instead of its symptoms.
        //
        // A one-index map is exact: a Boogie map and an SMT-LIB array are both
        // TOTAL functions, so `[int]int` is `(Array Int Int)` with nothing
        // approximated. The multi-index form is separate because it is a
        // CHOICE -- curry, or index by a tuple -- and the two say different
        // things about what a map is.
        // Loops landed on 2026-08-17 under §4.3's INVARIANT strategy, which
        // the user chose: the invariant is checked on entry and preserved
        // across the body, the loop's targets are havoc'd, and the
        // continuation is reasoned about from an arbitrary exited iteration.
        // Exact, and no bound -- the invariant is verified rather than
        // trusted. What remains of control flow is branching, and that is the
        // same decision seen from the other side.
        // Calls landed on 2026-09-19 as the two-sided contract at the call
        // site (checked requires asserted per clause, checked modifies and
        // out-targets havoc'd, every ensures assumed with old() at call entry)
        // plus free requires/ensures/modifies, free call and call forall --
        // This is Boogie 2 §8.2/§9.9/§9.10. async call, `where` clauses and
        // type parameters are named refusals.
        //
        // Branching landed 2026-09-20: `if`/`else if`/`else`/`if (*)` are the
        // §9.7 two-edge join (branches under their guards, disagreeing
        // versions merged by ite), and `return` obligatorifies the ensures at
        // every exit point, with unreachable code parsed but without effect.
        //
        // The rest of control flow landed the same day: labels and `goto`
        // (This is Boogie 2 §9.5) via the edge join with gate booleans, goto
        // loops via the reference's implicit-true-invariant cut
        // (RemoveBackEdges.cs), and `break` as a forward edge. What refuses:
        // a goto into a structured statement's body, and a goto loop crossing
        // a `while` boundary.
        coverage_.total = 17;
        coverage_.supported = 16;
        coverage_.missing = {
            "multi-index map types, which need a currying or tupling choice "
            "this frontend will not make silently",
        };
    }

    std::string id() const override { return "boogie"; }
    std::string displayName() const override { return "Boogie (structured core)"; }
    std::string version() const override { return "verification-core+chc"; }
    std::vector<std::string> extensions() const override { return {".bpl"}; }
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
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            BoogieParser p(src, name);
            const auto infer_it = opts.options.find("infer_modifies");
            if (infer_it != opts.options.end()) {
                if (infer_it->second != "1") {
                    out.diagnostics.error(
                        ErrorCode::E_PARSE,
                        "boogie's 'infer_modifies' option takes the value 1, not '"
                            + infer_it->second + "'");
                    return out;
                }
                p.setInferModifies(true);
            }
            // D7's cross-check route: `options: chc=1` emits Horn clauses from
            // the same parse (boogie.md §4.6); anything else errors by name.
            const auto chc_it = opts.options.find("chc");
            if (chc_it != opts.options.end()) {
                if (chc_it->second != "1") {
                    out.diagnostics.error(
                        ErrorCode::E_PARSE,
                        "boogie's 'chc' option takes the value 1, not '"
                            + chc_it->second + "'");
                    return out;
                }
                p.setChcMode(true);
            }
            out.model = p.parse(out.diagnostics, out.report);
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "boogie", out.report.fidelity()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("boogie frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkBoogieLanguage() { return std::make_shared<BoogieLanguage>(); }

} // namespace SOMTParser::Lang
