/* -*- Source -*-
 * Essence' frontend.
 *
 * The format is docs/languages/essence-prime.md; its `implicit-constraints`
 * block is the specification this file implements, and each entry has a fixture
 * in languages/essence/instances.
 *
 * Four obligations, none of them written in any line of a model:
 *
 *   1. **A sparse domain is a set, not a pair of bounds.** `int(1, 3, 5)` is
 *      not `int(1..5)`. The HIR's VarDecl carries a lower and an upper bound
 *      and nothing else, so a sparse domain must ALSO emit a membership
 *      constraint. Without it the model admits 2 and 4, which is a strictly
 *      larger solution set than the one written down -- and every one of the
 *      extra solutions type-checks.
 *   2. **A matrix index must be constrained to its declared index domain**,
 *      which need not start at 1. SMT-LIB arrays are total, so `q[0]` on a
 *      matrix indexed by `int(1..n)` reads a value the model never declared and
 *      the solver is free to choose it.
 *   3. **A quantifier over a domain is EXPANDED**, against the substituted
 *      parameter. `forall i : int(1..n) . P(i)` with n = 3 is a conjunction of
 *      three instances, not a bound variable: the range is a materialised set,
 *      so the quantifier has no meaning until the parameter is known.
 *   4. **A `where` clause is a validity condition on the .param file**, not a
 *      constraint on the model. Lowering it as a constraint would let a solver
 *      satisfy the model by choosing parameters, which are not its to choose.
 *
 * Parameters arrive in a separate `.param` file, so acceptsDataFiles() is
 * overridden -- without it translate() refuses the pair outright rather than
 * silently translating the model alone.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/essence.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/core/checked_integer.h"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <filesystem>
#include <fstream>
#include <cerrno>
#include <cstdlib>
#include <limits>
#include <memory>
#include <sstream>
#include <string>
#include <tuple>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

struct Token {
    enum Kind { IDENT, INT, PUNCT, END } kind = END;
    std::string text;
    long long   value = 0;
    bool        fits_int64 = true;
    int         line = 1;
};

/** `$` starts a comment, which is the one lexical surprise in the language. */
class Lexer {
public:
    explicit Lexer(std::string src) : src_(std::move(src)) {}

    Token next() {
        skipTrivia();
        Token t;
        t.line = line_;
        if (pos_ >= src_.size()) { t.kind = Token::END; return t; }
        const char c = src_[pos_];
        if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
            const std::size_t s = pos_;
            while (pos_ < src_.size()
                   && (std::isalnum(static_cast<unsigned char>(src_[pos_]))
                       || src_[pos_] == '_' || src_[pos_] == '\'')) {
                advance();
            }
            t.kind = Token::IDENT;
            t.text = src_.substr(s, pos_ - s);
            return t;
        }
        if (std::isdigit(static_cast<unsigned char>(c))) {
            const std::size_t s = pos_;
            while (pos_ < src_.size() && std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
                advance();
            }
            t.kind = Token::INT;
            t.text = src_.substr(s, pos_ - s);
            const char* first = t.text.data();
            const char* last = first + t.text.size();
            const auto parsed = std::from_chars(first, last, t.value);
            t.fits_int64 = parsed.ec == std::errc() && parsed.ptr == last;
            return t;
        }
        static const char* kMulti[] = {"..", "->", "=>", "<->", "**", "!=", "<=", ">=", "/\\", "\\/",
                                       nullptr};
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

private:
    void advance() {
        if (src_[pos_] == '\n') { ++line_; }
        ++pos_;
    }
    void skipTrivia() {
        while (pos_ < src_.size()) {
            const char c = src_[pos_];
            if (c == '$') {
                while (pos_ < src_.size() && src_[pos_] != '\n') { advance(); }
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

/** An integer domain: a low/high pair, plus the enumeration when the domain is
 *  sparse. `values` empty means the range is contiguous and the bounds say
 *  everything. */
struct Domain {
    long long lo = 0, hi = 0;
    std::vector<long long> values;      // non-empty only when sparse
    bool is_bool = false;
    bool has_lower = true;
    bool has_upper = true;

    bool finite() const { return has_lower && has_upper; }
    bool empty() const { return finite() && lo > hi; }
};

/** A declared matrix: its index domains in SOURCE ORDER, and its element
 *  domain.
 *
 *  A vector rather than one Domain because `matrix indexed by [a, b]` is
 *  TWO index sets and an HIR array holds one, so the dimensions are
 *  flattened row-major -- the same convention `mzn_minimal.cpp`'s
 *  flatIndex uses, and the decision is recorded per matrix rather than
 *  made silently (nothing in the emitted script distinguishes a flattened
 *  two-dimensional matrix from a one-dimensional one). */
/** How many matrices a single generator over a matrix domain may range over.
 *
 *  This frontend expands its generators (§4.2), so the count IS the cost: a
 *  `matrix indexed by [int(1..8)] of int(1..9)` is 43 million bodies, and the
 *  honest answer for one is a refusal naming the shape rather than an
 *  apparently-running translation. Generous enough for what Conjure writes --
 *  the corpus's largest is 5^4 = 625 -- and small enough that hitting it is a
 *  message rather than a machine. */
constexpr long long kElaboratorLimit = 100000;

struct Matrix {
    std::vector<Domain> index;
    Domain              elem;

    long long cells() const {
        long long n = 1;
        for (const Domain& d : index) { n *= (d.hi - d.lo + 1); }
        return n;
    }
    /** Row-major offset, zero-based for more than one dimension and the
     *  SOURCE index for exactly one -- so `q[3]` still reads
     *  `(select q 3)` and every existing fixture is unchanged. */
    long long offsetOf(const std::vector<long long>& at) const {
        if (index.size() == 1) { return at[0]; }
        long long off = 0;
        for (std::size_t k = 0; k < index.size(); ++k) {
            off = off * (index[k].hi - index[k].lo + 1) + (at[k] - index[k].lo);
        }
        return off;
    }
    std::string shapeText() const {
        std::string out;
        for (std::size_t k = 0; k < index.size(); ++k) {
            if (k != 0) { out += ", "; }
            out += "int(" + std::to_string(index[k].lo) + ".."
                 + std::to_string(index[k].hi) + ")";
        }
        return out;
    }
};

/** A matrix bound to CONSTANT cells by a generator over a matrix domain.
 *
 *  Distinct from `Matrix`, which records the SHAPE of a declared decision
 *  matrix and whose reads lower to `(select m offset)`. A cell of one of these
 *  is a literal, so a read must check for it FIRST -- a name in both would
 *  otherwise emit a select on a variable the model never declared. The
 *  generator refuses a name already taken, so nothing can be in both. */
struct ConstMatrix {
    std::vector<Domain>    index;
    Domain                 elem;
    std::vector<long long> cells;   // row-major, offsetOf order
};

struct ParameterValues {
    std::unordered_map<std::string, long long> scalars;
    std::unordered_set<std::string> booleans;
    std::unordered_map<std::string, ConstMatrix> matrices;
};

class EssenceParser {
public:
    EssenceParser(std::string src, std::string file) : file_(std::move(file)) {
        // The WHOLE token stream, up front. A quantifier body is parsed once
        // per tuple of its range -- `forall i : int(1..n) . P(i)` is a
        // conjunction of n instances, not a bound variable -- so the parser has
        // to return to a position it has already passed. A single-pass lexer
        // cannot do that.
        Lexer lex(std::move(src));
        for (;;) {
            Token t = lex.next();
            toks_.push_back(t);
            if (t.kind == Token::END) { break; }
        }
        tok_ = toks_[0];
    }

    /** @p params are `letting` assignments from the .param file, already read. */
    H::ConstraintModelPtr parse(const ParameterValues& params,
                                Uir::Diagnostics& diags,
                                Uir::TranslationReport& report) {
        report_ = &report;
        consts_ = params.scalars;
        boolean_consts_ = params.booleans;
        const_matrices_ = params.matrices;
        model_ = std::make_shared<H::ConstraintModel>();

        while (tok_.kind != Token::END) {
            if (is("language")) {
                const auto declaration_line = tok_.line;
                eat();
                while (tok_.kind != Token::END && tok_.line == declaration_line
                       && !is("given") && !is("letting") && !is("find")
                       && !is("such") && !is("where") && !is("minimising")
                       && !is("maximising")) {
                    eat();
                }
            } else if (is("given")) {
                if (!given(diags)) { return nullptr; }
            } else if (is("letting")) {
                if (!letting(diags)) { return nullptr; }
            } else if (is("where")) {
                if (!where(diags)) { return nullptr; }
            } else if (is("find")) {
                if (!find(diags)) { return nullptr; }
            } else if (is("such")) {
                if (!suchThat(diags)) { return nullptr; }
            } else if (is("minimising") || is("maximising")) {
                if (!objective(diags)) { return nullptr; }
            } else if (is("branching") || is("heuristic")) {
                if (!searchDirective(diags)) { return nullptr; }
            } else {
                diags.error(ErrorCode::E_PARSE, "unexpected '" + tok_.text + "'", loc());
                return nullptr;
            }
        }
        // OMT objective labels occupy a binding namespace. Delay naming until
        // all source declarations and parameters, including later ones, exist.
        std::unordered_set<std::string> used;
        for (const auto& entry : consts_) { used.insert(entry.first); }
        for (const auto& entry : const_matrices_) { used.insert(entry.first); }
        for (const auto& entry : domains_) { used.insert(entry.first); }
        for (const auto& entry : sorts_) { used.insert(entry.first); }
        for (const auto& entry : matrices_) { used.insert(entry.first); }
        for (const auto& declaration : model_->decls) { used.insert(declaration.name); }
        for (auto& objective : model_->objectives) {
            std::string candidate = "obj";
            std::size_t suffix = 0;
            while (used.count(candidate)) { candidate = "obj" + std::to_string(++suffix); }
            objective.name = candidate;
            used.insert(candidate);
        }
        // Constant constraints still need evaluation even without variables.
        if (model_->decls.empty()) {
            diags.warn(ErrorCode::E_PARSE,
                       "this model declares no decision variables; satisfiability "
                       "depends on its constant constraints", loc());
        }
        return model_;
    }

    bool readParameterAssignments(ParameterValues& values, Uir::Diagnostics& d) {
        consts_ = values.scalars;
        boolean_consts_ = values.booleans;
        const_matrices_ = values.matrices;
        while (tok_.kind != Token::END) {
            if (is("language")) {
                eat();
                while (tok_.kind != Token::END && !is("letting")) { eat(); }
                continue;
            }
            if (!is("letting")) {
                d.error(ErrorCode::E_PARSE, "expected `letting` in parameter file", loc());
                return false;
            }
            const std::size_t start = mark();
            eat();
            const std::string name = tok_.text;
            if (consts_.count(name) || const_matrices_.count(name)) {
                d.error(ErrorCode::E_PARSE, "parameter '" + name + "' is assigned more than once", loc());
                return false;
            }
            reset(start);
            if (!letting(d)) { return false; }
            if (domains_.count(name)) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a parameter assignment must be a scalar or constant matrix", loc());
                return false;
            }
        }
        values.scalars = std::move(consts_);
        values.booleans = std::move(boolean_consts_);
        values.matrices = std::move(const_matrices_);
        return true;
    }

    Uir::Sem::TranslationContract semanticContract(
        const H::ConstraintModel& model, const Uir::Fidelity& frontend_fidelity) const {
        Uir::Sem::ModelProjection projection;
        for (const H::VarDecl& declaration : model.decls) {
            const auto matrix = matrices_.find(declaration.name);
            if (matrix == matrices_.end()) {
                projection.observables.push_back(
                    {declaration.name, declaration.name,
                     Uir::Sem::ProjectionKind::DIRECT});
                continue;
            }
            // One observable per CELL, named the way the source names it.
            // For more than one dimension that is the subscript TUPLE and not
            // the flattened offset: the projection is what a reader maps a
            // solution back through, and `q[2,3]` is what they wrote.
            const Matrix& m = matrix->second;
            std::vector<long long> at;
            for (const Domain& dim : m.index) { at.push_back(dim.lo); }
            for (long long n = 0; n < m.cells(); ++n) {
                std::string subscripts;
                for (std::size_t k = 0; k < at.size(); ++k) {
                    if (k != 0) { subscripts += ","; }
                    subscripts += std::to_string(at[k]);
                }
                const std::string cell = declaration.name + "[" + subscripts + "]";
                projection.observables.push_back(
                    {cell, "(select " + declaration.name + " "
                               + std::to_string(m.offsetOf(at)) + ")",
                     Uir::Sem::ProjectionKind::DIRECT});
                // Odometer over the index domains, last dimension fastest --
                // the same order the flattening uses.
                for (std::size_t k = at.size(); k-- > 0;) {
                    if (++at[k] <= m.index[k].hi) { break; }
                    at[k] = m.index[k].lo;
                }
            }
        }
        return Uir::Sem::essencePrimeToRelationalContract(
            model, frontend_fidelity, std::move(projection));
    }

private:
    Uir::SourceLoc loc() const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = tok_.line;
        return l;
    }
    bool is(const std::string& t) const { return tok_.kind == Token::IDENT && tok_.text == t; }
    bool isP(const std::string& t) const { return tok_.kind == Token::PUNCT && tok_.text == t; }
    void eat() {
        if (pos_ + 1 < toks_.size()) { ++pos_; }
        tok_ = toks_[pos_];
    }
    std::size_t mark() const { return pos_; }
    /** Is the token after the current one this punctuation? */
    bool peekIsP(const char* t) const {
        return pos_ + 1 < toks_.size() && toks_[pos_ + 1].kind == Token::PUNCT
            && toks_[pos_ + 1].text == t;
    }
    void reset(std::size_t p) { pos_ = p; tok_ = toks_[pos_]; }
    bool expectP(const std::string& t, Uir::Diagnostics& d) {
        if (!isP(t)) {
            d.error(ErrorCode::E_PARSE, "expected '" + t + "', found '" + tok_.text + "'",
                    loc());
            return false;
        }
        eat();
        return true;
    }
    bool expectId(const std::string& t, Uir::Diagnostics& d) {
        if (!is(t)) {
            d.error(ErrorCode::E_PARSE, "expected '" + t + "', found '" + tok_.text + "'",
                    loc());
            return false;
        }
        eat();
        return true;
    }

    /** An integer expression over PARAMETERS only, evaluated now. Domain bounds
     *  and quantifier ranges are `par` in MiniZinc's sense: they must be known
     *  before the model exists, because the quantifier is expanded against
     *  them. */
    bool constExpr(long long& out, Uir::Diagnostics& d) {
        long long lhs = 0;
        if (!constProduct(lhs, d)) { return false; }
        while (isP("+") || isP("-")) {
            const bool add = isP("+");
            eat();
            long long rhs = 0;
            long long result = 0;
            if (!constProduct(rhs, d)) { return false; }
            const bool overflow = add ? SOMTParser::detail::addOverflow(lhs, rhs, &result)
                                      : SOMTParser::detail::subOverflow(lhs, rhs, &result);
            if (overflow) {
                d.error(ErrorCode::E_TYPE,
                        "constant expression overflows the Essence integer range", loc());
                return false;
            }
            lhs = result;
        }
        out = lhs;
        return true;
    }
    // Parameters determine domains and generator ranges. Their arithmetic
    // must use the same precedence as expressions over decision variables.
    bool constProduct(long long& out, Uir::Diagnostics& d) {
        long long lhs = 0;
        if (!constUnary(lhs, d)) { return false; }
        while (isP("*") || isP("/") || isP("%") || is("div") || is("mod")) {
            const bool mul = isP("*");
            const bool quotient = isP("/") || is("div");
            eat();
            long long rhs = 0, result = 0;
            if (!constUnary(rhs, d)) { return false; }
            if (mul) {
                if (SOMTParser::detail::mulOverflow(lhs, rhs, &result)) {
                    d.error(ErrorCode::E_TYPE,
                            "constant expression overflows the Essence integer range", loc());
                    return false;
                }
            } else {
                if (rhs == 0 || (lhs == std::numeric_limits<long long>::min() && rhs == -1)) {
                    d.error(ErrorCode::E_TYPE,
                            "constant division is undefined or overflows the Essence integer range", loc());
                    return false;
                }
                long long q = lhs / rhs, r = lhs % rhs;
                if (r != 0 && (r < 0) != (rhs < 0)) { --q; r += rhs; }
                result = quotient ? q : r;
            }
            lhs = result;
        }
        out = lhs;
        return true;
    }
    bool constUnary(long long& out, Uir::Diagnostics& d) {
        if (isP("-")) {
            eat();
            long long value = 0;
            if (!constUnary(value, d)) { return false; }
            if (SOMTParser::detail::subOverflow(0LL, value, &out)) {
                d.error(ErrorCode::E_TYPE,
                        "constant expression overflows the Essence integer range", loc());
                return false;
            }
            return true;
        }
        return constPower(out, d);
    }
    bool constPower(long long& out, Uir::Diagnostics& d) {
        if (!constAtom(out, d)) { return false; }
        if (!isP("**")) { return true; }
        eat();
        long long exponent = 0;
        if (!constUnary(exponent, d)) { return false; }
        if (exponent < 0 || (out == 0 && exponent == 0)) {
            d.error(ErrorCode::E_TYPE, "constant power is undefined", loc());
            return false;
        }
        long long base = out, result = 1;
        while (exponent != 0) {
            bool overflow = false;
            if (exponent & 1) { overflow = SOMTParser::detail::mulOverflow(result, base, &result); }
            exponent >>= 1;
            if (!overflow && exponent) { overflow = SOMTParser::detail::mulOverflow(base, base, &base); }
            if (overflow) {
                d.error(ErrorCode::E_TYPE,
                        "constant power overflows the Essence integer range", loc());
                return false;
            }
        }
        out = result;
        return true;
    }
    bool constAtom(long long& out, Uir::Diagnostics& d) {
        if (isP("(")) {
            eat();
            if (!constExpr(out, d)) { return false; }
            return expectP(")", d);
        }
        if (is("true") || is("false")) {
            out = is("true") ? 1 : 0;
            eat();
            return true;
        }
        if (tok_.kind == Token::INT) {
            if (!tok_.fits_int64) {
                d.error(ErrorCode::E_TYPE,
                        "integer constant '" + tok_.text
                            + "' is outside the finite elaborator range", loc());
                return false;
            }
            out = tok_.value;
            eat();
            return true;
        }
        if (tok_.kind == Token::IDENT) {
            // A CONSTANT matrix cell: `t[q10]`, where `t` is bound by a
            // generator over a matrix domain. Checked before `consts_` because
            // the two maps are disjoint and before the failure below, which
            // would otherwise report a matrix as a parameter with no value.
            const auto cm = const_matrices_.find(tok_.text);
            if (cm != const_matrices_.end()) {
                const std::string name = tok_.text;
                eat();
                std::vector<long long> at;
                if (!expectP("[", d)) { return false; }
                for (;;) {
                    long long one = 0;
                    if (!constExpr(one, d)) { return false; }
                    at.push_back(one);
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (!expectP("]", d)) { return false; }
                return constMatrixCell(cm->second, name, at, out, d);
            }
            const auto it = consts_.find(tok_.text);
            if (it == consts_.end()) {
                // A `given` with no value in the .param file. Refused by name:
                // a quantifier's range is expanded against it, so the model has
                // no meaning without it -- and guessing one would silently
                // produce a different problem of a different size.
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "parameter '" + tok_.text + "' has no value; a quantifier range "
                        "and a domain bound are expanded against it, so the model has "
                        "no meaning until the .param file supplies it", loc());
                return false;
            }
            out = it->second;
            eat();
            return true;
        }
        d.error(ErrorCode::E_PARSE, "expected a constant expression", loc());
        return false;
    }

    /** One generator variable of a comprehension, and the space it ranges over.
     *
     *  A scalar generator ranges over `range`; a MATRIX generator ranges over
     *  every matrix of `shape`, which is |vals|^cells of them. Both are a
     *  count and a decoder, so the tuple loop is one mixed-radix walk over
     *  `size` whichever kind each variable is -- the alternative was two
     *  nested enumerations that agree about ordering by inspection. */
    struct GenVar {
        std::string            name;
        bool                   is_matrix = false;
        bool                   is_bool = false;
        std::vector<long long> range;    // scalar
        ConstMatrix            shape;    // matrix: index + element domain
        std::vector<long long> vals;     // matrix: the element domain's values
        std::size_t            cells = 0;
        std::size_t            size = 0; // how many bindings this variable has
    };

    /** Bind `g` to its `k`-th value. */
    void bindGenVar(const GenVar& g, std::size_t k) {
        if (!g.is_matrix) {
            consts_[g.name] = g.range[k];
            const_matrices_.erase(g.name);
            if (g.is_bool) { boolean_consts_.insert(g.name); }
            else { boolean_consts_.erase(g.name); }
            return;
        }
        consts_.erase(g.name);
        boolean_consts_.erase(g.name);
        ConstMatrix bound = g.shape;
        bound.cells.assign(g.cells, 0);
        // Least-significant cell first, which is the same mixed-radix
        // convention the tuple loop uses for the variables themselves. The
        // ORDER is arbitrary and it does not matter that it is: every matrix
        // in the space is produced exactly once, and nothing downstream reads
        // `k`.
        for (std::size_t c = 0; c < g.cells; ++c) {
            bound.cells[c] = g.vals[k % g.vals.size()];
            k /= g.vals.size();
        }
        const_matrices_[g.name] = std::move(bound);
    }

    /** One cell of a constant matrix, with the SAME bounds check a declared
     *  matrix read gets. A generator binds every cell, so an out-of-range
     *  subscript here is a model error rather than a missing binding, and it
     *  must not read a neighbouring cell. */
    bool constMatrixCell(const ConstMatrix& m, const std::string& name,
                         const std::vector<long long>& at, long long& out,
                         Uir::Diagnostics& d) {
        if (at.size() != m.index.size()) {
            d.error(ErrorCode::E_TYPE,
                    "'" + name + "' is indexed by " + std::to_string(m.index.size())
                        + " subscript(s) but is read with " + std::to_string(at.size()),
                    loc());
            return false;
        }
        for (std::size_t k = 0; k < at.size(); ++k) {
            if (at[k] < m.index[k].lo || at[k] > m.index[k].hi) {
                d.error(ErrorCode::E_TYPE,
                        "index " + std::to_string(at[k]) + " is outside '" + name
                            + "''s declared index domain int("
                            + std::to_string(m.index[k].lo) + ".."
                            + std::to_string(m.index[k].hi) + ")",
                        loc());
                return false;
            }
        }
        // `Matrix::offsetOf`, over the same index domains -- the one-dimension
        // short circuit included, so a constant matrix and a declared one of
        // the same shape address their cells identically.
        Matrix shape;
        shape.index = m.index;
        shape.elem = m.elem;
        long long off = shape.offsetOf(at);
        if (m.index.size() == 1) { off -= m.index[0].lo; }
        if (off < 0 || static_cast<std::size_t>(off) >= m.cells.size()) {
            d.error(ErrorCode::E_INTERNAL,
                    "constant matrix '" + name + "' has no cell at that offset", loc());
            return false;
        }
        out = m.cells[static_cast<std::size_t>(off)];
        return true;
    }

    /** A guard as a CONSTANT truth value, evaluated over the HIR the ordinary
     *  expression parser produced.
     *
     *  A matrix generator's guards are the folds Conjure writes over the bound
     *  matrix -- `and([t[q] < t[q+1] \\/ t[q] = b+1 | q : int(1..3)])` -- and
     *  the token-level `constGuard` reads comparisons and connectives, not
     *  comprehensions. Rather than teach it a second comprehension expander,
     *  the guard is parsed by `expr()`, which already expands one, and the
     *  result is evaluated here: every leaf is a literal because every name in
     *  it is bound.
     *
     *  Returns false, without a diagnostic, when it meets something that is not
     *  constant -- the caller reports that in its own words, because "this
     *  guard mentions a decision variable" is a different statement from "this
     *  expression has no constant value". */
    bool constEval(const H::ExprPtr& e, bool& out) const {
        if (!e || e->sort.kind != H::SortKind::BOOL) { return false; }
        long long v = 0;
        if (!constEvalInt(e, v)) { return false; }
        out = v != 0;
        return true;
    }

    /** The integer (or 0/1 Boolean) value of a constant HIR expression. */
    bool constEvalInt(const H::ExprPtr& e, long long& out) const {
        if (!e) { return false; }
        // Evaluation can remove a guard or fallback from the final model.
        // Check its types before folding so Bool's internal 0/1 storage cannot
        // turn an ill-typed arithmetic expression into a valid integer literal.
        H::ConstraintModel constants;
        Uir::Diagnostics types;
        if (!H::typeCheckTerms(constants, {{e, e->loc}}, types)) { return false; }
        return constEvalValue(e, out);
    }

    bool constEvalValue(const H::ExprPtr& e, long long& out) const {
        if (!e) { return false; }
        if (e->kind == H::ExprKind::LIT_BOOL) { out = e->bool_value ? 1 : 0; return true; }
        if (e->kind == H::ExprKind::LIT_INT) {
            if (e->name.empty()) { return false; }
            errno = 0;
            char* end = nullptr;
            const long long v = std::strtoll(e->name.c_str(), &end, 10);
            if (errno != 0 || end == nullptr || *end != '\0') { return false; }
            out = v;
            return true;
        }
        if (e->kind != H::ExprKind::OP) { return false; }
        if (e->op == H::Op::ITE && e->args.size() == 3) {
            long long condition = 0;
            return constEvalValue(e->args[0], condition)
                && constEvalValue(e->args[condition != 0 ? 1 : 2], out);
        }
        std::vector<long long> a;
        a.reserve(e->args.size());
        for (const H::ExprPtr& c : e->args) {
            long long one = 0;
            if (!constEvalValue(c, one)) { return false; }
            a.push_back(one);
        }
        switch (e->op) {
        case H::Op::AND: {
            out = 1;
            for (long long x : a) { out = out && x != 0; }
            return true;
        }
        case H::Op::OR: {
            out = 0;
            for (long long x : a) { out = out || x != 0; }
            return true;
        }
        case H::Op::NOT:     if (a.size() != 1) { return false; } out = a[0] == 0; return true;
        case H::Op::IMPLIES: if (a.size() != 2) { return false; } out = a[0] == 0 || a[1] != 0; return true;
        case H::Op::EQ:      if (a.size() != 2) { return false; } out = a[0] == a[1]; return true;
        case H::Op::DISTINCT:if (a.size() != 2) { return false; } out = a[0] != a[1]; return true;
        case H::Op::LT:      if (a.size() != 2) { return false; } out = a[0] <  a[1]; return true;
        case H::Op::LE:      if (a.size() != 2) { return false; } out = a[0] <= a[1]; return true;
        case H::Op::GT:      if (a.size() != 2) { return false; } out = a[0] >  a[1]; return true;
        case H::Op::GE:      if (a.size() != 2) { return false; } out = a[0] >= a[1]; return true;
        case H::Op::ADD: {
            out = 0;
            for (long long x : a) { if (SOMTParser::detail::addOverflow(out, x, &out)) { return false; } }
            return true;
        }
        case H::Op::MUL: {
            out = 1;
            for (long long x : a) { if (SOMTParser::detail::mulOverflow(out, x, &out)) { return false; } }
            return true;
        }
        case H::Op::ABS:
            if (a.size() != 1) { return false; }
            if (a[0] < 0) { return !SOMTParser::detail::subOverflow(0LL, a[0], &out); }
            out = a[0]; return true;
        case H::Op::NEG:
            return a.size() == 1 && !SOMTParser::detail::subOverflow(0LL, a[0], &out);
        case H::Op::SUB:
            if (a.size() == 1) { return !SOMTParser::detail::subOverflow(0LL, a[0], &out); }
            return a.size() == 2 && !SOMTParser::detail::subOverflow(a[0], a[1], &out);
        case H::Op::DIV_FLOOR:
        case H::Op::MOD_FLOOR: {
            if (a.size() != 2 || a[1] == 0
                || (a[0] == std::numeric_limits<long long>::min() && a[1] == -1)) { return false; }
            long long q = a[0] / a[1], r = a[0] % a[1];
            if (r != 0 && (r < 0) != (a[1] < 0)) { --q; r += a[1]; }
            out = e->op == H::Op::DIV_FLOOR ? q : r;
            return true;
        }
        case H::Op::ITE:
            if (a.size() != 3) { return false; }
            out = a[0] != 0 ? a[1] : a[2];
            return true;
        default:
            // Everything else -- division, the globals, anything with a
            // declared variable under it -- is not evaluated here. Refusing to
            // guess is the point: a guard this cannot read is reported, never
            // assumed true.
            return false;
        }
    }

    /** `matrix indexed by [D1, ..., Dk] of Delem`, after the `matrix` keyword.
     *
     *  One reader for the two places a matrix domain appears -- a declaration
     *  and a comprehension generator. Written once because the index domains
     *  carry the layout, and two readings of a layout is how `offsetOf` and
     *  `flatOffsetTerm` would have come to disagree if the recurrence had been
     *  written twice (§4.4). */
    bool matrixDomain(std::vector<Domain>& index, Domain& elem, Uir::Diagnostics& d) {
        if (!expectId("indexed", d)) { return false; }
        if (!expectId("by", d)) { return false; }
        if (!expectP("[", d)) { return false; }
        for (;;) {
            Domain one;
            if (!domain(one, d)) { return false; }
            if (!one.finite()) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a matrix index domain must be finite before it can be "
                        "materialised as an SMT array", loc());
                return false;
            }
            if (one.empty()) {
                d.error(ErrorCode::E_TYPE,
                        "a matrix over an empty index domain has no elements", loc());
                return false;
            }
            index.push_back(one);
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP("]", d)) { return false; }
        if (!expectId("of", d)) { return false; }
        return domain(elem, d);
    }

    /** `int(1..5)`, `int(1, 3, 5)`, `int(1..n)`, `bool`, or a named domain. */
    bool domain(Domain& out, Uir::Diagnostics& d) {
        if (is("bool")) { eat(); out.is_bool = true; out.lo = 0; out.hi = 1; return true; }
        if (tok_.kind == Token::IDENT && !is("int") && !is("matrix")) {
            const auto it = domains_.find(tok_.text);
            if (it == domains_.end()) {
                d.error(ErrorCode::E_TYPE, "'" + tok_.text + "' is not a declared domain",
                        loc());
                return false;
            }
            out = it->second;
            eat();
            return true;
        }
        // A MATRIX domain reaches here only from a generator -- a declaration
        // parses its own `matrix indexed by [...] of ...`. It is a quantifier
        // over a function space: `| t : matrix indexed by [int(1..4)] of
        // int(1..5)` ranges over all 5^4 matrices of that shape.
        //
        // Named with E_UNSUPPORTED_CONSTRUCT rather than left to `expectId`,
        // which reported `E_PARSE: expected 'int', found 'matrix'`. That is
        // true of the token and wrong about the file: `matrix` is exactly what
        // Conjure meant to write, the input is well formed, and the two codes
        // feed different statistics -- "malformed input" against "coverage
        // gap". A refusal message that mentions punctuation is the signal for
        // this class of mistake (docs/languages/essence-prime.md §4.7).
        if (is("matrix")) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "a generator whose domain is a MATRIX quantifies over a "
                    "function space -- every matrix of that shape -- and this "
                    "subset expands generators over scalar domains only",
                    loc());
            return false;
        }
        if (!expectId("int", d)) { return false; }
        // Essence integer ranges may omit either bound, and the whole range
        // list is optional. These forms are infinite but still exact as SMT
        // Int domains; finite expansion sites reject them explicitly below.
        if (!isP("(")) {
            out.has_lower = false;
            out.has_upper = false;
            return true;
        }
        if (!expectP("(", d)) { return false; }
        if (isP(")")) {
            eat();
            out.has_lower = false;
            out.has_upper = false;
            return true;
        }
        if (isP("..")) {
            eat();
            out.has_lower = false;
            if (isP(")")) {
                eat();
                out.has_upper = false;
                return true;
            }
            if (!constExpr(out.hi, d)) { return false; }
            if (!expectP(")", d)) { return false; }
            return true;
        }
        std::vector<long long> vals;
        bool ranged = false;
        for (;;) {
            long long a = 0;
            if (!constExpr(a, d)) { return false; }
            if (isP("..")) {
                eat();
                if (isP(")")) {
                    eat();
                    out.lo = a;
                    out.has_upper = false;
                    return true;
                }
                long long b = 0;
                if (!constExpr(b, d)) { return false; }
                if (isP(")") && vals.empty()) {
                    eat();
                    out.lo = a;
                    out.hi = b;
                    return true;
                }
                ranged = true;
                const unsigned long long width =
                    static_cast<unsigned long long>(b)
                    - static_cast<unsigned long long>(a);
                if (b >= a && width > 100000) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a range inside a sparse integer domain has more than "
                            "100000 values and cannot be materialised", loc());
                    return false;
                }
                if (a <= b) {
                    for (long long v = a;; ++v) {
                        vals.push_back(v);
                        if (v == b) { break; }
                    }
                }
            } else {
                vals.push_back(a);
            }
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(")", d)) { return false; }
        if (vals.empty()) {
            // An EMPTY domain, which `int(3..1)` is. Legal as a quantifier
            // range -- `forall` over nothing is true and refusing it would
            // reject a legal model -- and an error for a `find`, where it means
            // the variable has no possible value. So it is recorded here and
            // judged by the caller: lo > hi marks it.
            out.lo = 1;
            out.hi = 0;
            return true;
        }
        out.lo = *std::min_element(vals.begin(), vals.end());
        out.hi = *std::max_element(vals.begin(), vals.end());
        // A domain is SPARSE when its values do not fill the range. The bounds
        // alone would admit the holes, so the enumeration is kept and turned
        // into a membership constraint at declaration.
        bool contiguous = ranged;
        for (std::size_t i = 1; i < vals.size() && contiguous; ++i) {
            contiguous = vals[i - 1] != std::numeric_limits<long long>::max()
                && vals[i] == vals[i - 1] + 1;
        }
        if (!contiguous) {
            std::sort(vals.begin(), vals.end());
            vals.erase(std::unique(vals.begin(), vals.end()), vals.end());
            contiguous = true;
            for (std::size_t i = 1; i < vals.size() && contiguous; ++i) {
                contiguous = vals[i - 1] != std::numeric_limits<long long>::max()
                    && vals[i] == vals[i - 1] + 1;
            }
            if (!contiguous) {
                out.values = vals;
            }
        }
        return true;
    }

    static bool contains(const Domain& domain, long long value) {
        if (domain.is_bool) { return value == 0 || value == 1; }
        return domain.values.empty()
            ? (!domain.has_lower || value >= domain.lo) && (!domain.has_upper || value <= domain.hi)
            : std::binary_search(domain.values.begin(), domain.values.end(), value);
    }

    // Savile Row ConstantMatrixStore.makeLettingsConstantMatrix infers a
    // plain unknown range endpoint from the supplied matrix extent. No
    // arbitrary expression is solved and two unknown endpoints are rejected.
    bool parameterIndex(Domain& out, long long extent, Uir::Diagnostics& d) {
        const std::size_t start = mark();
        if (is("int") && peekIsP("(")) {
            eat(); eat();
            if (tok_.kind == Token::IDENT && !consts_.count(tok_.text) && peekIsP("..")) {
                const std::string lower = tok_.text;
                eat(); eat();
                long long high = 0, low = 0;
                if (!constExpr(high, d) || !expectP(")", d)) { return false; }
                if (SOMTParser::detail::subOverflow(high, extent - 1, &low)) {
                    d.error(ErrorCode::E_TYPE, "inferred matrix index overflows", loc());
                    return false;
                }
                consts_[lower] = low;
                out.lo = low; out.hi = high;
                return true;
            }
            long long low = 0;
            Uir::Diagnostics speculative;
            if (constExpr(low, speculative) && isP("..")) {
                eat();
                if (tok_.kind == Token::IDENT && !consts_.count(tok_.text) && peekIsP(")")) {
                    const std::string upper = tok_.text;
                    eat(); eat();
                    long long high = 0;
                    if (SOMTParser::detail::addOverflow(low, extent - 1, &high)) {
                        d.error(ErrorCode::E_TYPE, "inferred matrix index overflows", loc());
                        return false;
                    }
                    consts_[upper] = high;
                    out.lo = low; out.hi = high;
                    return true;
                }
            }
        }
        reset(start);
        return domain(out, d);
    }

    bool givenMatrix(const std::vector<std::string>& names, Uir::Diagnostics& d) {
        const Uir::SourceLoc at = loc();
        const auto first = const_matrices_.find(names.front());
        if (first == const_matrices_.end()) {
            d.error(ErrorCode::E_TYPE, "matrix parameter '" + names.front()
                    + "' has no supplied constant matrix", at);
            return false;
        }
        const ConstMatrix shape = first->second;
        eat(); // matrix
        if (!expectId("indexed", d) || !expectId("by", d) || !expectP("[", d)) { return false; }
        std::vector<Domain> indices;
        for (;;) {
            if (indices.size() >= shape.index.size()) {
                d.error(ErrorCode::E_TYPE, "matrix parameter dimension count does not match its given domain", at);
                return false;
            }
            const Domain& physical = shape.index[indices.size()];
            const long long extent = physical.hi - physical.lo + 1;
            Domain index;
            if (!parameterIndex(index, extent, d)) { return false; }
            if (!index.finite() || !index.values.empty() || index.is_bool) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "matrix parameter indices require finite contiguous integer domains", at);
                return false;
            }
            if (index.hi < index.lo || static_cast<unsigned long long>(index.hi)
                - static_cast<unsigned long long>(index.lo) + 1 != static_cast<unsigned long long>(extent)) {
                d.error(ErrorCode::E_TYPE, "matrix parameter extent does not match its given domain", at);
                return false;
            }
            indices.push_back(index);
            if (!isP(",")) { break; }
            eat();
        }
        if (!expectP("]", d) || !expectId("of", d)) { return false; }
        Domain element;
        if (!domain(element, d)) { return false; }
        for (const std::string& name : names) {
            auto it = const_matrices_.find(name);
            if (it == const_matrices_.end() || it->second.index.size() != indices.size()
                || it->second.elem.is_bool != element.is_bool) {
                d.error(ErrorCode::E_TYPE, "matrix parameter shape or element type disagrees with given", at);
                return false;
            }
            ConstMatrix& value = it->second;
            bool reindex = false;
            for (std::size_t k = 0; k < indices.size(); ++k) {
                if (value.index[k].hi - value.index[k].lo != indices[k].hi - indices[k].lo) {
                    d.error(ErrorCode::E_TYPE, "matrix parameter extent does not match its given domain", at);
                    return false;
                }
                reindex = reindex || value.index[k].lo != indices[k].lo;
            }
            for (long long cell : value.cells) {
                if (!contains(element, cell)) {
                    d.error(ErrorCode::E_TYPE, "matrix parameter cell is outside its given element domain", at);
                    return false;
                }
            }
            if (reindex) {
                d.warn(ErrorCode::E_TYPE, "matrix parameter '" + name
                       + "' is reindexed to its given domain in row-major order", at);
                if (report_) {
                    Uir::EncodingChoice choice;
                    choice.site = name; choice.unified_op = "matrix-parameter-index";
                    choice.strategy = "given-domain-row-major-reindex";
                    choice.fidelity = Uir::Fidelity::exact();
                    Matrix before; before.index = value.index;
                    Matrix after; after.index = indices;
                    choice.rationale = before.shapeText() + " -> " + after.shapeText()
                        + "; Savile Row parameter index alignment; cell order unchanged";
                    report_->addChoice(std::move(choice));
                }
            }
            value.index = indices;
            value.elem = element;
            given_names_.push_back(name);
        }
        return true;
    }

    bool given(Uir::Diagnostics& d) {
        const Uir::SourceLoc declaration_loc = loc();
        eat();                                   // 'given'
        std::vector<std::string> names;
        for (;;) {
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected a parameter name", loc());
                return false;
            }
            if (std::find(given_names_.begin(), given_names_.end(), tok_.text)
                != given_names_.end()) {
                d.error(ErrorCode::E_PARSE,
                        "parameter '" + tok_.text + "' is declared by `given` twice",
                        loc());
                return false;
            }
            names.push_back(tok_.text);
            eat();
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(":", d)) { return false; }
        if (is("matrix")) { return givenMatrix(names, d); }
        // The declared domain of a parameter is a validity condition on the
        // .param file, like `where`, and not a constraint on the model. It must
        // nevertheless be parsed and checked here: accepting `n = 12` for
        // `given n : int(1..10)` changes every domain and quantifier expanded
        // against n, even though the resulting target formula is well-typed.
        Domain declared;
        if (!domain(declared, d)) { return false; }
        for (const std::string& name : names) {
            const auto value = consts_.find(name);
            if (value == consts_.end()) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "parameter '" + name + "' has no value; source domains and "
                        "quantifier ranges may be expanded against it, so the model has "
                        "no meaning until the .param file supplies it",
                        declaration_loc);
                return false;
            }
            if (declared.is_bool != (boolean_consts_.count(name) != 0)) {
                d.error(ErrorCode::E_TYPE, "parameter value type disagrees with its given domain", declaration_loc);
                return false;
            }
            const bool in_domain = declared.is_bool
                ? value->second == 0 || value->second == 1
                : declared.values.empty()
                    ? (!declared.has_lower || declared.lo <= value->second)
                        && (!declared.has_upper || value->second <= declared.hi)
                    : std::binary_search(declared.values.begin(), declared.values.end(),
                                         value->second);
            if (!in_domain) {
                d.error(ErrorCode::E_TYPE,
                        "parameter '" + name + "' has value "
                            + std::to_string(value->second)
                            + ", which is outside its declared `given` domain; this "
                              ".param file is not valid for the model",
                        declaration_loc);
                return false;
            }
            given_names_.push_back(name);
        }
        return true;
    }

    /** A rectangular constant matrix literal, retaining every source index
     *  domain. Nested rows are stored in the same row-major order as decision
     *  matrices. No decision declaration or auxiliary variable is introduced. */
    bool constantMatrixLiteral(ConstMatrix& out, Uir::Diagnostics& d) {
        const Uir::SourceLoc at = loc();
        if (!expectP("[", d)) { return false; }
        if (isP("]") || isP(";")) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "an empty named matrix literal needs an explicit element type", at);
            return false;
        }
        const bool nested = isP("[");
        std::vector<Domain> inner_index;
        bool bool_elements = false;
        std::size_t entries = 0;
        for (;;) {
            if (isP("[") != nested) {
                d.error(ErrorCode::E_TYPE, "a matrix literal must be rectangular", loc());
                return false;
            }
            if (nested) {
                ConstMatrix child;
                if (!constantMatrixLiteral(child, d)) { return false; }
                if (entries == 0) {
                    inner_index = child.index;
                    bool_elements = child.elem.is_bool;
                } else {
                    bool same = inner_index.size() == child.index.size()
                             && bool_elements == child.elem.is_bool;
                    for (std::size_t k = 0; same && k < inner_index.size(); ++k) {
                        same = inner_index[k].lo == child.index[k].lo
                            && inner_index[k].hi == child.index[k].hi
                            && inner_index[k].is_bool == child.index[k].is_bool;
                    }
                    if (!same) {
                        d.error(ErrorCode::E_TYPE,
                                "a matrix literal's rows must have identical index domains and element types", at);
                        return false;
                    }
                }
                out.cells.insert(out.cells.end(), child.cells.begin(), child.cells.end());
            } else {
                const bool is_bool = is("true") || is("false");
                long long value = 0;
                if (is_bool) { value = is("true") ? 1 : 0; eat(); }
                else if (!constExpr(value, d)) { return false; }
                if (entries != 0 && bool_elements != is_bool) {
                    d.error(ErrorCode::E_TYPE,
                            "a constant matrix cannot mix Boolean and integer elements", at);
                    return false;
                }
                bool_elements = is_bool;
                out.cells.push_back(value);
            }
            ++entries;
            if (out.cells.size() > static_cast<std::size_t>(kElaboratorLimit)) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a named matrix literal exceeds the finite elaborator range", at);
                return false;
            }
            if (!isP(",")) { break; }
            eat();
            if (isP("]") || isP(";")) { break; }
        }
        Domain index;
        index.lo = 1;
        index.hi = static_cast<long long>(entries);
        if (isP(";")) {
            eat();
            if (!domain(index, d)) { return false; }
            if (!index.finite() || !index.values.empty() || index.is_bool) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a named matrix literal requires a finite contiguous integer index domain", at);
                return false;
            }
            if (index.hi < index.lo
                || static_cast<unsigned long long>(index.hi)
                   - static_cast<unsigned long long>(index.lo) + 1 != entries) {
                d.error(ErrorCode::E_TYPE,
                        "a matrix literal's index domain must match its number of elements", at);
                return false;
            }
        }
        if (!expectP("]", d)) { return false; }
        out.index.push_back(index);
        out.index.insert(out.index.end(), inner_index.begin(), inner_index.end());
        out.elem.is_bool = bool_elements;
        return true;
    }

    bool letting(Uir::Diagnostics& d) {
        eat();                                   // 'letting'
        if (tok_.kind != Token::IDENT) {
            d.error(ErrorCode::E_PARSE, "expected a name", loc());
            return false;
        }
        const std::string name = tok_.text;
        if (const_matrices_.count(name)) {
            d.error(ErrorCode::E_TYPE, "'" + name + "' is already declared as a constant matrix", loc());
            return false;
        }
        eat();
        if (isP("=")) { eat(); }
        else if (!expectId("be", d)) { return false; }
        if (isP("[")) {
            ConstMatrix value;
            if (!constantMatrixLiteral(value, d)) { return false; }
            if (consts_.count(name) || const_matrices_.count(name)
                || matrices_.count(name) || sorts_.count(name) || domains_.count(name)) {
                d.error(ErrorCode::E_TYPE, "'" + name + "' is already declared", loc());
                return false;
            }
            const_matrices_[name] = std::move(value);
            return true;
        }
        if (is("domain")) {
            eat();
            Domain dom;
            if (!domain(dom, d)) { return false; }
            domains_[name] = dom;
            return true;
        }
        const std::size_t before = definedness_.size();
        H::ExprPtr value = expr(d);
        if (!value) { return false; }
        H::ExprPtr defined = takeDefinedness(before);
        bool is_defined = true;
        long long v = 0;
        if ((defined && (!constEval(defined, is_defined) || !is_defined))
            || !constEvalInt(value, v)) {
            d.error(ErrorCode::E_TYPE,
                    "constant assignment is undefined, nonconstant, or overflows the Essence integer range", loc());
            return false;
        }
        consts_[name] = v;
        if (value->sort.kind == H::SortKind::BOOL) { boolean_consts_.insert(name); }
        else { boolean_consts_.erase(name); }
        return true;
    }

    /** `branching on [x, y, z]` and `heuristic static` -- SEARCH ORDER.
     *
     *  Skipped with a note, not refused and not lowered. They say which
     *  variable a solver should try first; the set of solutions is identical
     *  either way, and this frontend emits constraints rather than a search
     *  strategy, so there is nothing for them to become. That is the same
     *  reading MiniZinc's annotations get, and for the same reason.
     *
     *  Skipping is only safe BECAUSE the semantics are declarative. It is
     *  reported rather than silent, because "this frontend ignored something
     *  the file said" is a fact the reader is entitled to, even when ignoring
     *  it is correct.
     *
     *  Fifteen of the twenty-four upstream files stopped on `branching`, all
     *  with `E_PARSE: unexpected 'branching'`. A uniform failure on one token
     *  across most of a corpus is never a semantic gap -- it is the same shape
     *  as MiniZinc's corpus failing 16 of 16 at line 1 column 1 on a comment
     *  syntax the lexer did not know. */
    bool searchDirective(Uir::Diagnostics& d) {
        const std::string kind = tok_.text;
        const Uir::SourceLoc at = loc();
        eat();                                   // 'branching' | 'heuristic'
        if (!said_search_) {
            said_search_ = true;
            d.note(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                   "'" + kind + "' states a search order and is skipped: it selects "
                   "which variable a solver tries first and leaves the set of "
                   "solutions unchanged, and this frontend emits constraints rather "
                   "than a search strategy",
                   at);
        }
        // Consume to the next item keyword. The directive's payload is a
        // bracketed list or a bare name, and both are skipped wholesale rather
        // than parsed: parsing them would mean resolving names this frontend
        // has no use for, and a `branching on []` would still have to be
        // accepted.
        int depth = 0;
        while (tok_.kind != Token::END) {
            if (isP("[") || isP("(")) { ++depth; }
            else if (isP("]") || isP(")")) { --depth; }
            else if (depth == 0
                     && (is("given") || is("letting") || is("find") || is("such")
                         || is("where") || is("minimising") || is("maximising")
                         || is("branching") || is("heuristic"))) {
                break;
            }
            eat();
        }
        return true;
    }

    /** §3: a `where` clause is a condition on the PARAMETERS. It is checked
     *  here and reported as E_TYPE, not lowered as a constraint -- lowering it
     *  would let a solver satisfy the model by choosing parameter values, which
     *  are not its to choose. */
    bool where(Uir::Diagnostics& d) {
        eat();                                   // 'where'
        for (;;) {
            long long lhs = 0;
            if (!constExpr(lhs, d)) { return false; }
            std::string op;
            if (tok_.kind == Token::PUNCT
                && (tok_.text == "<" || tok_.text == ">" || tok_.text == "="
                    || tok_.text == "<=" || tok_.text == ">=" || tok_.text == "!=")) {
                op = tok_.text;
                eat();
            } else {
                d.error(ErrorCode::E_PARSE, "expected a comparison in a `where` clause",
                        loc());
                return false;
            }
            long long rhs = 0;
            if (!constExpr(rhs, d)) { return false; }
            const bool holds =
                op == "<"  ? lhs < rhs  : op == ">"  ? lhs > rhs  :
                op == "="  ? lhs == rhs : op == "<=" ? lhs <= rhs :
                op == ">=" ? lhs >= rhs : lhs != rhs;
            if (!holds) {
                d.error(ErrorCode::E_TYPE,
                        "the `where` clause " + std::to_string(lhs) + " " + op + " "
                            + std::to_string(rhs) + " does not hold for the supplied "
                            "parameters, so this .param file is not valid for this model",
                        loc());
                return false;
            }
            if (isP(",")) { eat(); continue; }
            break;
        }
        return true;
    }

    void declareVar(const std::string& name, const H::Sort& s, const Domain& dom) {
        H::VarDecl v;
        v.name = name;
        v.sort = s;
        v.loc = loc();
        if (!dom.is_bool) {
            if (dom.has_lower) { v.lower_bound = H::mkInt(std::to_string(dom.lo)); }
            if (dom.has_upper) { v.upper_bound = H::mkInt(std::to_string(dom.hi)); }
        }
        model_->decls.push_back(std::move(v));
    }

    void addConstraint(const H::ExprPtr& e) {
        H::Constraint c;
        c.loc = loc();
        c.formula = e;
        model_->constraints.push_back(c);
    }

    // Savile Row manual 1.11.1, section 3: undefined numeric values
    // propagate to the nearest SOURCE Boolean expression, which becomes false.
    // Keep these separate from declaration/domain constraints. Generated SMT
    // comparisons (e.g. inside min) must not create extra source boundaries.
    H::ExprPtr takeDefinedness(std::size_t before) {
        if (definedness_.size() == before) { return nullptr; }
        std::vector<H::ExprPtr> guards(definedness_.begin() + before, definedness_.end());
        definedness_.resize(before);
        return guards.size() == 1 ? guards.front() : H::mkOp(H::Op::AND, guards);
    }

    H::ExprPtr closeBoolean(std::size_t before, H::ExprPtr value) {
        if (!value || value->sort.kind != H::SortKind::BOOL) { return value; }
        H::ExprPtr defined = takeDefinedness(before);
        return defined ? H::mkOp(H::Op::AND, {defined, value}) : value;
    }

    void requireDefined(const H::ExprPtr& guard) {
        definedness_.push_back(guard);
        if (said_partiality_ || report_ == nullptr) { return; }
        said_partiality_ = true;
        report_->addChoice(
            {file_ + ":" + std::to_string(tok_.line), "partial-expression",
             "relational-definedness", Uir::Fidelity::exact(),
             "Undefined numeric expressions make the nearest source Boolean "
             "expression false; Boolean matrix reads close at the read itself. "
             "catchUndef totalizes numeric values before that boundary"});
    }

    /** The membership constraint a sparse domain needs. */
    void addMembership(const H::ExprPtr& term, const Domain& dom) {
        if (dom.values.empty()) { return; }
        H::ExprPtr acc;
        for (const long long v : dom.values) {
            H::ExprPtr eq = H::mkOp(H::Op::EQ, {term, H::mkInt(std::to_string(v))});
            acc = acc ? H::mkOp(H::Op::OR, {acc, eq}) : eq;
        }
        addConstraint(acc);
    }

    /** Record that a matrix's dimensions were flattened.
     *
     *  Nothing in the emitted script distinguishes a flattened
     *  two-dimensional matrix from a one-dimensional one, so a reader of the
     *  output alone cannot recover what the source said -- which is precisely
     *  when a decision has to be recorded rather than made silently. */
    void recordFlattening(const std::string& name, const Matrix& m) {
        if (report_ == nullptr) { return; }
        Uir::EncodingChoice choice;
        choice.site = name;
        choice.unified_op = "matrix-index";
        choice.strategy = "matrix-flatten-row-major";
        choice.fidelity = Uir::Fidelity::exact();
        choice.rationale =
            "matrix '" + name + "' is indexed by " + m.shapeText()
            + "; an HIR array holds one index, so the dimensions are flattened "
              "row-major over a zero-based space. The emitted script shows only "
              "the offset, so the source shape is recoverable from this entry "
              "and from nowhere else";
        report_->addChoice(std::move(choice));
    }

    bool find(Uir::Diagnostics& d) {
        eat();                                   // 'find'
        std::vector<std::string> names;
        for (;;) {
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected a variable name", loc());
                return false;
            }
            if (const_matrices_.count(tok_.text)) {
                d.error(ErrorCode::E_TYPE,
                        "'" + tok_.text + "' is already declared as a constant matrix", loc());
                return false;
            }
            names.push_back(tok_.text);
            eat();
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(":", d)) { return false; }

        if (is("matrix")) {
            eat();
            // `matrix indexed by [a, b]` is TWO index sets, flattened
            // row-major below. Refused outright until 2026-09-20.
            std::vector<Domain> index;
            Domain elem;
            if (!matrixDomain(index, elem, d)) { return false; }
            const H::Sort es = elem.is_bool ? H::Sort::boolean() : H::Sort::integer();
            for (const std::string& n : names) {
                H::VarDecl v;
                v.name = n;
                v.sort = H::Sort::array(H::Sort::integer(), es);
                v.loc = loc();
                model_->decls.push_back(v);
                Matrix m;
                m.index = index;
                m.elem = elem;
                matrices_[n] = m;
                if (index.size() > 1) { recordFlattening(n, m); }
                // The element domain must be stated per index: an SMT-LIB array
                // is total, so nothing bounds q[i] otherwise. Materialised over
                // every cell, which is known because the index domains are
                // `par` -- for more than one dimension that is the whole
                // flattened space rather than one span.
                for (long long off = 0; off < m.cells(); ++off) {
                    const long long flat =
                        index.size() == 1 ? index[0].lo + off : off;
                    H::ExprPtr sel = H::mkOp(
                        H::Op::SELECT,
                        {H::mkIdent(n, v.sort), H::mkInt(std::to_string(flat))});
                    if (!elem.is_bool && elem.has_lower) {
                        addConstraint(H::mkOp(H::Op::GE,
                                              {sel, H::mkInt(std::to_string(elem.lo))}));
                    }
                    if (!elem.is_bool && elem.has_upper) {
                        addConstraint(H::mkOp(H::Op::LE,
                                              {sel, H::mkInt(std::to_string(elem.hi))}));
                    }
                    addMembership(sel, elem);
                }
            }
            return true;
        }

        Domain dom;
        if (!domain(dom, d)) { return false; }
        if (dom.empty()) {
            d.error(ErrorCode::E_TYPE,
                    "a `find` over an empty domain has no possible value", loc());
            return false;
        }
        for (const std::string& n : names) {
            const H::Sort s = dom.is_bool ? H::Sort::boolean() : H::Sort::integer();
            sorts_[n] = s;
            declareVar(n, s, dom);
            if (!dom.values.empty()) {
                addMembership(H::mkIdent(n, s), dom);
            }
        }
        return true;
    }

    bool suchThat(Uir::Diagnostics& d) {
        eat();                                   // 'such'
        if (!expectId("that", d)) { return false; }
        for (;;) {
            H::ExprPtr e = expr(d);
            if (!e) { return false; }
            addConstraint(e);
            if (isP(",")) { eat(); continue; }
            break;
        }
        return true;
    }

    bool objective(Uir::Diagnostics& d) {
        const bool minimise = is("minimising");
        eat();
        const std::size_t before = definedness_.size();
        H::ExprPtr e = expr(d);
        if (!e) { return false; }
        if (H::ExprPtr defined = takeDefinedness(before)) { addConstraint(defined); }
        H::Objective o;
        o.kind = minimise ? H::ObjKind::MINIMIZE : H::ObjKind::MAXIMIZE;
        o.term = asInteger(e);
        model_->objectives.push_back(std::move(o));
        return true;
    }

    // ---- Expressions -------------------------------------------------------

    H::ExprPtr asInteger(H::ExprPtr value) {
        if (value && value->sort.kind == H::SortKind::BOOL) {
            return H::mkOp(H::Op::ITE, {value, H::mkInt("1"), H::mkInt("0")}, value->loc);
        }
        return value;
    }

    H::ExprPtr expr(Uir::Diagnostics& d) { return parseImp(d); }

    H::ExprPtr parseImp(Uir::Diagnostics& d) {
        H::ExprPtr l = parseOr(d);
        if (!l) { return nullptr; }
        if (isP("->") || isP("=>")) {
            eat();
            H::ExprPtr r = parseImp(d);
            if (!r) { return nullptr; }
            return H::mkOp(H::Op::IMPLIES, {l, r});
        }
        // `<->` was LEXED and never parsed, so a legal Essence' operator read as
        // `unexpected '<->'` -- a parse error naming punctuation the lexer had
        // just recognised. There is no Op::IFF; on two Booleans, EQ is exactly
        // bi-implication, and using it keeps this a mapping rather than an
        // encoding decision.
        if (isP("<->")) {
            eat();
            H::ExprPtr r = parseImp(d);
            if (!r) { return nullptr; }
            return H::mkOp(H::Op::EQ, {l, r});
        }
        return l;
    }
    H::ExprPtr parseOr(Uir::Diagnostics& d) {
        H::ExprPtr l = parseAnd(d);
        if (!l) { return nullptr; }
        while (isP("\\/")) {
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
        while (isP("/\\")) {
            eat();
            H::ExprPtr r = parseCmp(d);
            if (!r) { return nullptr; }
            l = H::mkOp(H::Op::AND, {l, r});
        }
        return l;
    }
    H::ExprPtr parseCmp(Uir::Diagnostics& d) {
        const std::size_t before = definedness_.size();
        return closeBoolean(before, parseCmpValue(d));
    }

    H::ExprPtr parseCmpValue(Uir::Diagnostics& d) {
        H::ExprPtr l = parseAdd(d);
        if (!l) { return nullptr; }
        static const std::unordered_map<std::string, H::Op> kCmp = {
            {"=", H::Op::EQ}, {"<", H::Op::LT}, {">", H::Op::GT},
            {"<=", H::Op::LE}, {">=", H::Op::GE},
        };
        if (tok_.kind == Token::PUNCT) {
            if (tok_.text == "!=") {
                eat();
                H::ExprPtr r = parseAdd(d);
                if (!r) { return nullptr; }
                return H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {asInteger(l), asInteger(r)})});
            }
            const auto it = kCmp.find(tok_.text);
            if (it != kCmp.end()) {
                const H::Op op = it->second;
                eat();
                H::ExprPtr r = parseAdd(d);
                if (!r) { return nullptr; }
                return H::mkOp(op, {asInteger(l), asInteger(r)});
            }
        }
        return l;
    }
    H::ExprPtr parseAdd(Uir::Diagnostics& d) {
        H::ExprPtr l = parseMul(d);
        if (!l) { return nullptr; }
        while (isP("+") || isP("-")) {
            const bool plus = isP("+");
            eat();
            H::ExprPtr r = parseMul(d);
            if (!r) { return nullptr; }
            l = H::mkOp(plus ? H::Op::ADD : H::Op::SUB, {asInteger(l), asInteger(r)});
        }
        return l;
    }
    H::ExprPtr parseMul(Uir::Diagnostics& d) {
        H::ExprPtr l = parseUnary(d);
        if (!l) { return nullptr; }
        for (;;) {
            if (isP("*")) {
                eat();
                H::ExprPtr r = parseUnary(d);
                if (!r) { return nullptr; }
                l = H::mkOp(H::Op::MUL, {asInteger(l), asInteger(r)});
            } else if (is("div") || is("mod") || isP("/") || isP("%")) {
                // Savile Row manual 2.1.9: floor division; the remainder has
                // the divisor's sign. Undefinedness remains at the nearest
                // source Boolean boundary (section 3).
                const bool is_div = is("div") || isP("/");
                eat();
                H::ExprPtr r = asInteger(parseUnary(d));
                if (!r) { return nullptr; }
                H::ExprPtr defined = H::mkOp(H::Op::NOT,
                    {H::mkOp(H::Op::EQ, {r, H::mkInt("0")})});
                requireDefined(defined);
                l = H::mkOp(H::Op::ITE,
                    {defined, H::mkOp(is_div ? H::Op::DIV_FLOOR : H::Op::MOD_FLOOR,
                                     {asInteger(l), r}), H::mkInt("0")});
            } else { break; }
        }
        return l;
    }

    H::ExprPtr parseUnary(Uir::Diagnostics& d) {
        if (isP("-")) {
            eat();
            H::ExprPtr value = parseUnary(d);
            return value ? H::mkOp(H::Op::NEG, {asInteger(value)}) : nullptr;
        }
        return parsePower(d);
    }

    H::ExprPtr parsePower(Uir::Diagnostics& d) {
        H::ExprPtr base = parseAtom(d);
        if (!base || !isP("**")) { return base; }
        const Uir::SourceLoc at = loc();
        eat();
        H::ExprPtr exponent_term = asInteger(parseUnary(d));
        if (!exponent_term) { return nullptr; }
        long long exponent = 0;
        if (!constEvalInt(exponent_term, exponent)) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "power currently requires a constant integer exponent", at);
            return nullptr;
        }
        base = asInteger(base);
        if (exponent < 0) {
            requireDefined(H::mkBool(false, at));
            return H::mkInt("0", at);
        }
        if (exponent > kElaboratorLimit) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "power exponent exceeds the finite elaborator range", at);
            return nullptr;
        }
        if (exponent == 0) {
            H::ExprPtr defined = H::mkOp(H::Op::NOT,
                {H::mkOp(H::Op::EQ, {base, H::mkInt("0")}, at)}, at);
            requireDefined(defined);
            return H::mkOp(H::Op::ITE, {defined, H::mkInt("1"), H::mkInt("0")}, at);
        }
        H::ExprPtr result = H::mkInt("1", at);
        while (exponent != 0) {
            if (exponent & 1) { result = H::mkOp(H::Op::MUL, {result, base}, at); }
            exponent >>= 1;
            if (exponent) { base = H::mkOp(H::Op::MUL, {base, base}, at); }
        }
        return result;
    }

    /** The values `vars` SHADOW, captured before a quantifier binds them.
     *
     *  Every expansion site used to `consts_.erase` its variables on the way
     *  out, which is right exactly when nothing of that name was bound before.
     *  Conjure generates unique names (`q1`, `q15`, `q18`), so no corpus file
     *  reaches the case -- but an inner comprehension reusing an OUTER's
     *  variable name then destroyed the outer binding, and every later
     *  reference to it refused with "parameter has no value". It failed safe,
     *  which is why it survived a review: a refusal, never a wrong answer.
     *
     *  Saved as (name, had_value, value) rather than as a map, because one
     *  generator group may name the same variable twice and the restore has to
     *  be the exact inverse of the binding order. `mzn_minimal.cpp` keeps a
     *  `shadowed_` map for the same reason. */
    struct Shadow {
        std::string name;
        bool        had_const = false;
        bool        was_bool = false;
        long long   value = 0;
        bool        had_matrix = false;
        ConstMatrix matrix;
    };
    using Shadowed = std::vector<Shadow>;

    Shadowed shadow(const std::vector<std::string>& vars) {
        Shadowed saved;
        saved.reserve(vars.size());
        for (const std::string& v : vars) {
            Shadow one;
            one.name = v;
            one.was_bool = boolean_consts_.count(v) != 0;
            const auto c = consts_.find(v);
            if (c != consts_.end()) { one.had_const = true; one.value = c->second; }
            // Both maps, because a generator variable may bind either -- a
            // scalar domain writes `consts_` and a matrix domain writes
            // `const_matrices_`. Saving only the one this generator happens to
            // use would leave the other's entry to be restored by nobody.
            const auto m = const_matrices_.find(v);
            if (m != const_matrices_.end()) { one.had_matrix = true; one.matrix = m->second; }
            saved.push_back(std::move(one));
        }
        return saved;
    }

    void unshadow(const Shadowed& saved) {
        // In reverse, so a repeated name ends at what it had before the FIRST
        // binding rather than before the last.
        for (auto it = saved.rbegin(); it != saved.rend(); ++it) {
            if (it->had_const) { consts_[it->name] = it->value; }
            else               { consts_.erase(it->name); }
            if (it->was_bool) { boolean_consts_.insert(it->name); }
            else { boolean_consts_.erase(it->name); }
            if (it->had_matrix) { const_matrices_[it->name] = it->matrix; }
            else                { const_matrices_.erase(it->name); }
        }
    }

    /** `forall i : dom . body`, `exists i : dom . body`, `sum i : dom . body`.
     *  Expanded, because the range is `par` and the HIR has no comprehension. */
    // BY VALUE, not by reference. The caller passes tok_.text and the first
    // thing this does is eat(), which replaces tok_ wholesale -- so a reference
    // parameter silently starts naming the NEXT token, every comparison below
    // fails, and the `sum` branch runs for a `forall`. The symptom was
    // "argument 1 of '+' is Bool": a conjunction being summed. The same trap is
    // documented at parsePredicateCall in the MiniZinc frontend.
    H::ExprPtr quantified(std::string kind, Uir::Diagnostics& d) {
        if (kind == "forAll") { kind = "forall"; }
        eat();                                   // forall / exists / sum
        std::vector<std::string> vars;
        for (;;) {
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected a quantifier variable", loc());
                return nullptr;
            }
            vars.push_back(tok_.text);
            eat();
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP(":", d)) { return nullptr; }
        Domain dom;
        if (!domain(dom, d)) { return nullptr; }
        if (!dom.finite()) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "a quantifier domain must be finite because this frontend "
                    "expands it before SMT lowering", loc());
            return nullptr;
        }
        if (!expectP(".", d)) { return nullptr; }

        // The body's position, returned to once per tuple. Expanding rather
        // than binding is what §4.2 requires: the range is a materialised set
        // and the quantifier has no meaning until the parameters are known.
        const std::size_t body_at = mark();
        std::vector<long long> range;
        if (dom.values.empty()) {
            // lo > hi is the empty domain, and the loop below produces nothing
            // for it -- which is what makes `forall` over an empty range true.
            for (long long v = dom.lo; v <= dom.hi; ++v) { range.push_back(v); }
        } else {
            range = dom.values;
        }

        H::ExprPtr acc;
        const Shadowed saved = shadow(vars);
        // A cartesian product over several variables, which is what
        // `forall i, j : int(1..n)` means.
        const std::size_t n = range.size();
        std::size_t total = n == 0 ? 0 : 1;
        for (std::size_t v = 0; v < vars.size() && total != 0; ++v) { total *= n; }
        std::size_t after = body_at;
        for (std::size_t k = 0; k < total; ++k) {
            std::size_t t = k;
            for (std::size_t v = 0; v < vars.size(); ++v) {
                consts_[vars[v]] = range[t % n];
                const_matrices_.erase(vars[v]);
                if (dom.is_bool) { boolean_consts_.insert(vars[v]); }
                else { boolean_consts_.erase(vars[v]); }
                t /= n;
            }
            reset(body_at);
            H::ExprPtr one = expr(d);
            if (!one) { return nullptr; }
            after = mark();
            if (kind == "forall") {
                acc = acc ? H::mkOp(H::Op::AND, {acc, one}) : one;
            } else if (kind == "exists") {
                acc = acc ? H::mkOp(H::Op::OR, {acc, one}) : one;
            } else {
                one = asInteger(one);
                acc = acc ? H::mkOp(H::Op::ADD, {acc, one}) : one;
            }
        }
        unshadow(saved);
        // Land after the body, whichever iteration parsed it last. An empty
        // range parses it once and discards the result, so the position is
        // still correct.
        if (total == 0) {
            const std::size_t before = definedness_.size();
            reset(body_at);
            (void)expr(d);
            definedness_.resize(before);
            after = mark();
        }
        reset(after);
        if (!acc) {
            // An empty range: `forall` over nothing is true, `exists` false,
            // `sum` zero. Refusing would reject a legal model.
            acc = kind == "forall" ? H::mkBool(true)
                : kind == "exists" ? H::mkBool(false)
                                   : H::mkInt("0");
        }
        return acc;
    }

    /** `and([ body | q : D, r : E ])` -- a COMPREHENSION FOLD.
     *
     *  Conjure writes every quantifier this way, so it is the shape of every
     *  file it produces: twelve of the twenty-four upstream ones stopped on it,
     *  reported as `'and' is not declared` -- a name the LANGUAGE provides,
     *  blamed on the model for not declaring it.
     *
     *  Semantically it is `quantified()` with the generator written AFTER the
     *  body instead of before, so the expansion is the same and the only new
     *  work is finding the `|`: the body has to be skipped before its
     *  generators can be read, and then re-parsed once per tuple. Expanding
     *  rather than binding is what §4.2 requires -- the range is materialised
     *  and the quantifier has no meaning until the parameters are known.
     *
     *  `and`, `or` and `sum` fold with AND, OR and ADD; `min`/`max` are refused,
     *  because a fold needs an identity for the empty range and neither has one.
     */
    /** @p kind is taken BY VALUE, not by reference. The caller passes
     *  `tok_.text`, and the first `eat()` overwrites `tok_` -- a reference would
     *  then name whatever token came next, so every comparison against "and"
     *  and "or" failed and every fold became a `sum`, which is how a conjunction
     *  of Booleans came out as `+` over them. */
    /** Whether the item at the cursor is a GENERATOR (`name[, name]* :`) and
     *  not a guard.
     *
     *  A comprehension's `|` is followed by a comma-separated list whose items
     *  are generators or conditions, in any order and any number -- Conjure
     *  writes `| q123 : int(1..2), q124 : int(1..2), q123 < q124` and also
     *  `| 2 = q124`, a list with no generator at all. The two are told apart
     *  by what follows the leading names: a generator always reaches a `:`
     *  through identifiers and commas, and nothing else can. Read-only
     *  lookahead over the token vector, because deciding this by parsing and
     *  backtracking would have to run `constExpr`, which reports.
     */
    bool looksLikeGenerator() const {
        std::size_t i = pos_;
        for (;;) {
            if (i >= toks_.size() || toks_[i].kind != Token::IDENT) { return false; }
            ++i;
            if (i >= toks_.size() || toks_[i].kind != Token::PUNCT) { return false; }
            if (toks_[i].text == ":") { return true; }
            if (toks_[i].text != ",") { return false; }
            ++i;
        }
    }

    /** Move past one guard, stopping at the `,` or `]` that ends it.
     *
     *  Bracket-counted: a guard may contain a nested comprehension, whose own
     *  commas and `]` must not be mistaken for this list's. */
    bool skipGuard(Uir::Diagnostics& d) {
        int depth = 0;
        for (;;) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE,
                        "a comprehension guard is not closed by ',' or ']'", loc());
                return false;
            }
            if (depth == 0 && (isP(",") || isP("]"))) { return true; }
            if (isP("(") || isP("[")) { ++depth; }
            else if (isP(")") || isP("]")) { --depth; }
            eat();
        }
    }

    /** A guard, evaluated at parse time against the tuple's bindings.
     *
     *  Parse-time and not lowered, for a reason that is about correctness
     *  rather than output size. A guard exists to EXCLUDE tuples, and the body
     *  need not be meaningful for the tuples it excludes -- an index may leave
     *  its matrix's range there. Emitting `guard -> body` instead would
     *  elaborate the body for every tuple and refuse the file on one the
     *  comprehension never denotes.
     *
     *  A guard that is not a parse-time constant is refused by name rather
     *  than approximated: every guard in the corpus mentions only the
     *  comprehension's own variables, and the lowered form is a different
     *  construct with the hazard above. */
    bool peekIsId(const std::string& t) const {
        return pos_ + 1 < toks_.size() && toks_[pos_ + 1].kind == Token::IDENT
            && toks_[pos_ + 1].text == t;
    }

    /** `[e1, e2; int(1..2)]` as a list of parse-time constants. The index
     *  domain is accepted and its size checked, for the same reason
     *  `literalFold` checks it: a domain disagreeing with the element count
     *  describes a different matrix. */
    bool constList(std::vector<long long>& out, Uir::Diagnostics& d) {
        if (!expectP("[", d)) { return false; }
        out.clear();
        if (!isP("]")) {
            for (;;) {
                long long v = 0;
                if (!constExpr(v, d)) { return false; }
                out.push_back(v);
                if (isP(",")) { eat(); continue; }
                break;
            }
        }
        if (isP(";")) {
            const Uir::SourceLoc at = loc();
            eat();
            Domain dom;
            if (!domain(dom, d)) { return false; }
            if (!dom.finite()) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a matrix literal's index domain must be finite", at);
                return false;
            }
            const long long size = dom.values.empty() ? dom.hi - dom.lo + 1
                                 : static_cast<long long>(dom.values.size());
            if (size != static_cast<long long>(out.size())) {
                d.error(ErrorCode::E_TYPE,
                        "a matrix literal with " + std::to_string(out.size())
                            + " element(s) is indexed by a domain of size "
                            + std::to_string(size),
                        at);
                return false;
            }
        }
        return expectP("]", d);
    }

    bool constGuardAtom(bool& out, Uir::Diagnostics& d) {
        if (isP("(")) {
            eat();
            if (!constGuard(out, d)) { return false; }
            return expectP(")", d);
        }
        if (isP("!")) {
            eat();
            bool inner = false;
            if (!constGuardAtom(inner, d)) { return false; }
            out = !inner;
            return true;
        }
        // `[q1; int(1)] <lex [q2; int(1)]` -- Conjure writes a lexicographic
        // comparison of two matrix literals as a comprehension guard, which is
        // how it says "each unordered pair once". Both sides are lists of
        // parse-time constants here, so the comparison is one too.
        if (isP("[")) {
            std::vector<long long> lhs_list;
            if (!constList(lhs_list, d)) { return false; }
            const bool strict = isP("<");
            if (!(isP("<") || isP("<=")) || !peekIsId("lex")) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a matrix literal in a guard is only read as the operand of "
                        "`<lex` or `<=lex` in this subset",
                        loc());
                return false;
            }
            eat();                               // '<' or '<='
            eat();                               // 'lex'
            std::vector<long long> rhs_list;
            if (!constList(rhs_list, d)) { return false; }
            const bool less = std::lexicographical_compare(
                lhs_list.begin(), lhs_list.end(), rhs_list.begin(), rhs_list.end());
            out = less || (!strict && lhs_list == rhs_list);
            return true;
        }
        long long lhs = 0;
        if (!constExpr(lhs, d)) { return false; }
        std::string op;
        if (isP("=") || isP("!=") || isP("<") || isP("<=") || isP(">") || isP(">=")) {
            op = tok_.text;
            eat();
        } else {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "a comprehension guard must be a parse-time comparison in this "
                    "subset; this one is not, and lowering it would elaborate the "
                    "body for tuples the comprehension does not denote",
                    loc());
            return false;
        }
        long long rhs = 0;
        if (!constExpr(rhs, d)) { return false; }
        out = op == "="  ? lhs == rhs
            : op == "!=" ? lhs != rhs
            : op == "<"  ? lhs <  rhs
            : op == "<=" ? lhs <= rhs
            : op == ">"  ? lhs >  rhs
                         : lhs >= rhs;
        return true;
    }

    bool constGuard(bool& out, Uir::Diagnostics& d) {
        if (!constGuardAtom(out, d)) { return false; }
        for (;;) {
            if (isP("/\\")) {
                eat();
                bool rhs = false;
                if (!constGuardAtom(rhs, d)) { return false; }
                out = out && rhs;
            } else if (isP("\\/")) {
                eat();
                bool rhs = false;
                if (!constGuardAtom(rhs, d)) { return false; }
                out = out || rhs;
            } else {
                break;
            }
        }
        return true;
    }

    /** `flatten([L1, L2; int(1..2)])` -- the CONCATENATION of its inner
     *  lists, in order.
     *
     *  Conjure emits it to compare two tuples of unequal shape position by
     *  position: `flatten([[a; int(1)], [b | q : int(1..3)]; int(1..2)])` is
     *  the four-element list `a, b_1, b_2, b_3`. The outer list is parsed here
     *  rather than through `bracketItems` because its ELEMENTS are lists, and
     *  a nested `[` in expression position means a lex comparison.
     *
     *  The outer index domain is checked against the number of inner LISTS,
     *  not against the flattened length -- that is what it indexes. */
    bool flattenItems(std::vector<H::ExprPtr>& out, Uir::Diagnostics& d) {
        if (!expectP("[", d)) { return false; }
        std::size_t inner_lists = 0;
        for (;;) {
            if (!isP("[")) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'flatten' is read over a list OF LISTS in this subset; this "
                        "element is not a list, and flattening a scalar would silently "
                        "change the length of the result",
                        loc());
                return false;
            }
            if (!bracketItems("flatten", out, d)) { return false; }
            ++inner_lists;
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (isP(";")) {
            const Uir::SourceLoc at = loc();
            eat();
            Domain dom;
            if (!domain(dom, d)) { return false; }
            if (!dom.finite()) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a matrix literal's index domain must be finite", at);
                return false;
            }
            const long long size = dom.values.empty() ? dom.hi - dom.lo + 1
                                 : static_cast<long long>(dom.values.size());
            if (size != static_cast<long long>(inner_lists)) {
                d.error(ErrorCode::E_TYPE,
                        "'flatten' over " + std::to_string(inner_lists)
                            + " list(s) is indexed by a domain of size "
                            + std::to_string(size),
                        at);
                return false;
            }
        }
        return expectP("]", d);
    }

    /** A matrix or a slice with `..` for each retained dimension.
     *  Fixed subscripts keep the ordinary matrix read's local definedness.
     *  Without flatten, exactly one dimension must remain: a scalar is not a
     *  singleton list and a matrix of rows is not implicitly concatenated. */
    bool matrixItems(std::vector<H::ExprPtr>& out, Uir::Diagnostics& d,
                     bool flatten = false) {
        const Uir::SourceLoc at = loc();
        const std::string name = tok_.text;
        const auto found = matrices_.find(name);
        const auto known = const_matrices_.find(name);
        if (tok_.kind != Token::IDENT
            || (found == matrices_.end() && known == const_matrices_.end())) {
            d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "expected a declared matrix or matrix slice", at);
            return false;
        }
        // A binder in a subscript may temporarily shadow this matrix name.
        // Keep its value alive while parsing that subscript.
        ConstMatrix constant_value;
        const ConstMatrix* constant = nullptr;
        if (known != const_matrices_.end()) {
            constant_value = known->second;
            constant = &constant_value;
        }
        Matrix mat;
        if (constant) { mat.index = constant->index; mat.elem = constant->elem; }
        else { mat = found->second; }
        for (const Domain& index : mat.index) {
            if (!index.values.empty() || index.is_bool) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "matrix slices require contiguous integer index domains", at);
                return false;
            }
        }
        eat();
        const std::size_t before = definedness_.size();
        std::vector<H::ExprPtr> fixed(mat.index.size());
        if (isP("[")) {
            eat();
            std::size_t dimension = 0;
            for (;;) {
                if (dimension == mat.index.size()) {
                    d.error(ErrorCode::E_TYPE, "too many matrix slice subscripts", at);
                    return false;
                }
                if (isP("..")) { eat(); }
                else {
                    fixed[dimension] = expr(d);
                    if (!fixed[dimension]) { return false; }
                    if (fixed[dimension]->sort.kind != H::SortKind::INT) {
                        d.error(ErrorCode::E_TYPE, "a matrix subscript must be integer", at);
                        return false;
                    }
                }
                ++dimension;
                if (!isP(",")) { break; }
                eat();
            }
            if (!expectP("]", d)) { return false; }
            if (dimension != mat.index.size()) {
                d.error(ErrorCode::E_TYPE, "incorrect number of matrix slice subscripts", at);
                return false;
            }
        }
        std::size_t rank = 0;
        std::size_t size = 1;
        for (std::size_t k = 0; k < fixed.size(); ++k) {
            const Domain& index = mat.index[k];
            if (fixed[k]) {
                requireDefined(H::mkOp(H::Op::AND,
                    {H::mkOp(H::Op::GE, {fixed[k], H::mkInt(std::to_string(index.lo))}),
                     H::mkOp(H::Op::LE, {fixed[k], H::mkInt(std::to_string(index.hi))})}));
            } else {
                ++rank;
                const auto length = static_cast<unsigned long long>(index.hi)
                                  - static_cast<unsigned long long>(index.lo) + 1;
                if (length == 0 || length > static_cast<unsigned long long>(kElaboratorLimit)
                    || size > static_cast<std::size_t>(kElaboratorLimit) / length) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a matrix slice exceeds the finite elaborator range", at);
                    return false;
                }
                size *= static_cast<std::size_t>(length);
            }
        }
        if (rank == 0 || (!flatten && rank != 1)) {
            d.error(ErrorCode::E_TYPE,
                    "a list operand must retain one matrix dimension; use flatten for multiple dimensions", at);
            return false;
        }
        const H::ExprPtr defined = takeDefinedness(before);
        const H::Sort array_sort = H::Sort::array(H::Sort::integer(),
            mat.elem.is_bool ? H::Sort::boolean() : H::Sort::integer());
        H::ExprPtr array;
        auto literal = [&](long long cell) {
            return mat.elem.is_bool ? H::mkBool(cell != 0, at)
                                    : H::mkInt(std::to_string(cell), at);
        };
        for (std::size_t cell = 0; cell < size; ++cell) {
            std::size_t remaining = cell;
            std::vector<H::ExprPtr> subs = fixed;
            for (std::size_t k = subs.size(); k-- > 0;) {
                if (subs[k]) { continue; }
                const auto length = static_cast<std::size_t>(mat.index[k].hi - mat.index[k].lo + 1);
                subs[k] = H::mkInt(std::to_string(mat.index[k].lo
                                               + static_cast<long long>(remaining % length)));
                remaining /= length;
            }
            const H::ExprPtr offset = subs.size() == 1 ? subs[0] : flatOffsetTerm(mat, subs, at);
            H::ExprPtr value;
            long long position = 0;
            if (constant && constEvalInt(offset, position)) {
                if (subs.size() == 1) { position -= mat.index[0].lo; }
                // The per-dimension definedness guards exclude invalid reads.
                // The placeholder below is never observed in a defined value.
                value = literal(position >= 0 && static_cast<std::size_t>(position) < constant->cells.size()
                                    ? constant->cells[static_cast<std::size_t>(position)] : 0);
            } else {
                if (!array) {
                    array = constant ? H::mkConstArray(array_sort, literal(0), at)
                                     : H::mkIdent(name, array_sort, at);
                    if (constant) {
                        for (std::size_t k = 0; k < constant->cells.size(); ++k) {
                            const long long index = static_cast<long long>(k)
                                                  + (subs.size() == 1 ? mat.index[0].lo : 0);
                            array = H::mkOp(H::Op::STORE,
                                {array, H::mkInt(std::to_string(index), at), literal(constant->cells[k])}, at);
                        }
                    }
                }
                value = H::mkOp(H::Op::SELECT, {array, offset}, at);
            }
            if (defined && mat.elem.is_bool) {
                value = H::mkOp(H::Op::AND, {defined, value}, at);
            }
            out.push_back(std::move(value));
        }
        if (defined && !mat.elem.is_bool) { requireDefined(defined); }
        return true;
    }

    bool constantMatrixItems(std::vector<H::ExprPtr>& out, Uir::Diagnostics& d,
                             bool flatten = false) {
        const auto found = const_matrices_.find(tok_.text);
        if (found == const_matrices_.end()) { return false; }
        if (peekIsP("[")) { return matrixItems(out, d, flatten); }
        const ConstMatrix& value = found->second;
        if (!flatten && value.index.size() != 1) {
            d.error(ErrorCode::E_TYPE, "a list operand requires a one-dimensional matrix", loc());
            return false;
        }
        eat();
        for (long long cell : value.cells) {
            out.push_back(value.elem.is_bool ? H::mkBool(cell != 0) : H::mkInt(std::to_string(cell)));
        }
        return true;
    }

    /** Elements consumed by a fold, allDiff or a lexicographic comparison. */
    bool listOperand(std::vector<H::ExprPtr>& out, Uir::Diagnostics& d) {
        if (is("flatten") && peekIsP("(")) {
            eat();
            if (!expectP("(", d)) { return false; }
            if (isP("[")) {
                if (!flattenItems(out, d)) { return false; }
            } else if (tok_.kind == Token::IDENT && const_matrices_.count(tok_.text)) {
                if (!constantMatrixItems(out, d, true)) { return false; }
            } else if (!matrixItems(out, d, true)) { return false; }
            return expectP(")", d);
        }
        if (isP("[")) { return bracketItems("list", out, d); }
        if (tok_.kind == Token::IDENT && const_matrices_.count(tok_.text)) {
            return constantMatrixItems(out, d);
        }
        if (tok_.kind == Token::IDENT && matrices_.count(tok_.text)) {
            return matrixItems(out, d);
        }
        d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "expected a bracketed list, decision matrix slice or flatten operand", loc());
        return false;
    }

    /** The row-major flattened offset of a subscript list, as a TERM.
     *
     *  Exactly the recurrence `Matrix::offsetOf` folds -- Horner's form,
     *  `off = off * size_k + (sub_k - lo_k)` -- built out of HIR arithmetic
     *  instead of evaluated. A constant subscript gives a term the engine's
     *  builders fold back to the same literal `offsetOf` would have produced,
     *  so the two paths cannot disagree about the layout: there is one
     *  recurrence and it is written once.
     *
     *  Used only when at least one subscript is not a literal. The all-constant
     *  path still calls `offsetOf`, because `(select a 5)` is checkable in a
     *  way that `(select a (+ (* 0 3) 5))` is not -- the same argument
     *  `flatIndex` makes in the MiniZinc frontend.
     *
     *  Also only for `index.size() > 1`, and that precondition is load-bearing
     *  rather than incidental: `offsetOf` SHORT-CIRCUITS one dimension to a
     *  raw `at[0]`, subtracting no `lo`, because a one-dimensional matrix is
     *  addressed by its declared index and not by a flattened offset. This
     *  loop would subtract `lo`, so on one dimension the two DO disagree. The
     *  caller returns `subs[0]` before reaching here, matching `offsetOf`. */
    H::ExprPtr flatOffsetTerm(const Matrix& mat, const std::vector<H::ExprPtr>& subs,
                              const Uir::SourceLoc& at) {
        H::ExprPtr off = H::mkInt("0", at);
        for (std::size_t k = 0; k < mat.index.size(); ++k) {
            const long long size = mat.index[k].hi - mat.index[k].lo + 1;
            off = H::mkOp(H::Op::MUL,
                          {off, H::mkInt(std::to_string(size), at)}, at);
            off = H::mkOp(H::Op::ADD,
                          {off,
                           H::mkOp(H::Op::SUB,
                                   {subs[k],
                                    H::mkInt(std::to_string(mat.index[k].lo), at)},
                                   at)},
                          at);
        }
        return off;
    }

    /** `a <lex b` as a term, from position `i` on.
     *
     *  `a_i < b_i \/ (a_i = b_i /\ <rest>)`, ending at the last position with
     *  `<` for `<lex` and `<=` for `<=lex` -- which is the whole difference
     *  between them, and it only shows on lists that are equal. Two empty
     *  lists are not less-than and are less-than-or-equal, which is what the
     *  base case returns. */
    H::ExprPtr lexChain(const std::vector<H::ExprPtr>& a,
                        const std::vector<H::ExprPtr>& b, bool strict,
                        std::size_t i, const Uir::SourceLoc& at) {
        if (i >= a.size()) { return H::mkBool(!strict, at); }
        if (i + 1 == a.size()) {
            return H::mkOp(strict ? H::Op::LT : H::Op::LE, {a[i], b[i]}, at);
        }
        return H::mkOp(
            H::Op::OR,
            {H::mkOp(H::Op::LT, {a[i], b[i]}, at),
             H::mkOp(H::Op::AND,
                     {H::mkOp(H::Op::EQ, {a[i], b[i]}, at),
                      lexChain(a, b, strict, i + 1, at)},
                     at)},
            at);
    }

    /** Fold a list of elements with `and`, `or` or `sum`, identity if empty. */
    H::ExprPtr foldItems(const std::string& kind,
                         const std::vector<H::ExprPtr>& items) {
        H::ExprPtr acc;
        for (const H::ExprPtr& item : items) {
            const H::ExprPtr one = kind == "sum" ? asInteger(item) : item;
            if (!acc) { acc = one; continue; }
            acc = kind == "and" ? H::mkOp(H::Op::AND, {acc, one})
                : kind == "or"  ? H::mkOp(H::Op::OR,  {acc, one})
                                : H::mkOp(H::Op::ADD, {acc, one});
        }
        if (!acc) {
            acc = kind == "and" ? H::mkBool(true)
                : kind == "or"  ? H::mkBool(false)
                                : H::mkInt("0");
        }
        return acc;
    }

    /** `[e1, e2, e3; int(1..3)]` -- a MATRIX LITERAL's elements.
     *
     *  Essence' writes a matrix literal as its elements, then `;`, then the
     *  index domain. The index domain is CHECKED rather than skipped: it
     *  carries no term, but a domain whose size disagrees with the element
     *  count describes a different matrix from the one written, and reading
     *  one against the other is a wrong answer rather than a parse error.
     *
     *  Cursor starts just inside the `[`; ends just past the matching `]`. */
    bool literalItems(std::size_t body_at, std::vector<H::ExprPtr>& out,
                      Uir::Diagnostics& d) {
        reset(body_at);
        std::vector<H::ExprPtr> items;
        for (;;) {
            H::ExprPtr one = expr(d);
            if (!one) { return false; }
            items.push_back(one);
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (isP(";")) {
            const Uir::SourceLoc at = loc();
            eat();
            Domain dom;
            if (!domain(dom, d)) { return false; }
            if (!dom.finite()) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a matrix literal's index domain must be finite", at);
                return false;
            }
            const long long size = dom.values.empty() ? dom.hi - dom.lo + 1
                                 : static_cast<long long>(dom.values.size());
            if (size != static_cast<long long>(items.size())) {
                d.error(ErrorCode::E_TYPE,
                        "a matrix literal with " + std::to_string(items.size())
                            + " element(s) is indexed by a domain of size "
                            + std::to_string(size),
                        at);
                return false;
            }
        }
        if (!expectP("]", d)) { return false; }
        out.insert(out.end(), items.begin(), items.end());
        return true;
    }

    /** The ELEMENTS of a bracketed list, whether it is written as a
     *  comprehension (`[body | generators, guards]`) or as a matrix literal
     *  (`[e1, e2; int(1..2)]`).
     *
     *  Separated from the fold so that a list can be consumed by something
     *  other than `and`/`or`/`sum` -- `alldifferent_except([...], v)` takes
     *  the same list and builds a pairwise constraint from it, and `flatten`
     *  would take one too. `label` names the caller in diagnostics.
     *
     *  Cursor starts AT the `[`; ends just past the matching `]`. */
    bool bracketItems(const std::string& label, std::vector<H::ExprPtr>& out,
                      Uir::Diagnostics& d) {
        if (!expectP("[", d)) { return false; }
        const std::size_t body_at = mark();

        // Skip the body to its `|`, counting brackets so a nested comprehension
        // does not end this one.
        int depth = 0;
        bool literal = false;
        while (!(depth == 0 && isP("|"))) {
            if (tok_.kind == Token::END) {
                d.error(ErrorCode::E_PARSE,
                        "'" + label + "([...])' has no '|' before its generator", loc());
                return false;
            }
            if (isP("[") || isP("(")) { ++depth; }
            else if (isP("]") || isP(")")) {
                // `and([e])`: a one-element list.
                if (depth == 0) { literal = true; break; }
                --depth;
            }
            // `[e1, e2, e3; int(1..3)]` -- a MATRIX LITERAL rather than a
            // comprehension. Conjure writes both, and the two are told apart
            // by which separator is reached first at depth 0.
            else if (depth == 0 && (isP(",") || isP(";"))) { literal = true; break; }
            eat();
        }
        if (literal) { return literalItems(body_at, out, d); }
        eat();                                   // '|'

        std::vector<GenVar> gens;
        bool saw_matrix_generator = false;
        // The guards' token positions, returned to once per tuple. Positions
        // rather than expressions: a guard is evaluated against the tuple's
        // bindings, so it has no meaning until one exists.
        std::vector<std::size_t> guards;
        for (;;) {
            if (!looksLikeGenerator()) {
                const std::size_t before = mark();
                guards.push_back(before);
                if (!skipGuard(d)) { return false; }
                if (mark() == before) {
                    d.error(ErrorCode::E_PARSE,
                            "expected a generator or a guard after '|'", loc());
                    return false;
                }
                if (isP(",")) { eat(); continue; }
                break;
            }
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE, "expected a generator variable", loc());
                return false;
            }
            std::vector<std::string> group;
            group.push_back(tok_.text);
            eat();
            while (isP(",") ) {
                // `q, r : D` shares one domain; `q : D, r : E` does not. A comma
                // before the `:` continues the group, one after it starts the
                // next generator -- unambiguous, since a generator always ends
                // with its domain.
                const std::size_t save = mark();
                eat();
                if (tok_.kind == Token::IDENT) {
                    const std::string nm = tok_.text;
                    eat();
                    if (isP(":") || isP(",")) { group.push_back(nm); continue; }
                }
                reset(save);
                break;
            }
            if (!expectP(":", d)) { return false; }
            // A MATRIX domain quantifies over a function space: `t : matrix
            // indexed by [int(1..4)] of int(1..5)` ranges over all 5^4 matrices
            // of that shape. Expanded like every other generator here -- the
            // range is finite and the frontend's strategy is expansion (§4.2)
            // -- but the count is |values|^|cells| rather than |values|, so it
            // is checked against the elaborator range before anything is built.
            if (is("matrix")) {
                eat();
                std::vector<Domain> index;
                Domain elem;
                if (!matrixDomain(index, elem, d)) { return false; }
                if (!elem.finite()) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a matrix generator's ELEMENT domain must be finite: the "
                            "generator ranges over every matrix of the shape, and an "
                            "infinite element domain makes that uncountable", loc());
                    return false;
                }
                ConstMatrix shape;
                shape.index = index;
                shape.elem = elem;
                std::vector<long long> vals;
                if (elem.values.empty()) {
                    for (long long v = elem.lo; v <= elem.hi; ++v) { vals.push_back(v); }
                } else {
                    vals = elem.values;
                }
                Matrix cells_of;
                cells_of.index = index;
                cells_of.elem = elem;
                const long long cells = cells_of.cells();
                // |values|^|cells|, computed WITHOUT pow: the count overflows
                // long long for shapes a reader may plausibly write, and the
                // whole point of the guard is to refuse those by name rather
                // than to wrap around into a small number and expand happily.
                long long total_matrices = 1;
                bool overflow = cells < 0 || vals.empty();
                for (long long c = 0; c < cells && !overflow; ++c) {
                    if (total_matrices > kElaboratorLimit / static_cast<long long>(vals.size())) {
                        overflow = true;
                        break;
                    }
                    total_matrices *= static_cast<long long>(vals.size());
                }
                if (overflow || total_matrices > kElaboratorLimit) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a generator over `matrix indexed by [" + cells_of.shapeText()
                                + "]` of a domain with " + std::to_string(vals.size())
                                + " value(s) ranges over more matrices than the finite "
                                  "elaborator range allows; this frontend expands its "
                                  "generators, so the count is the cost", loc());
                    return false;
                }
                for (const std::string& g : group) {
                    GenVar gv;
                    gv.name = g;
                    gv.is_matrix = true;
                    gv.shape = shape;
                    gv.vals = vals;
                    gv.cells = static_cast<std::size_t>(cells);
                    gv.size = static_cast<std::size_t>(total_matrices);
                    gens.push_back(std::move(gv));
                }
                saw_matrix_generator = true;
                if (isP(",")) { eat(); continue; }
                break;
            }
            Domain dom;
            if (!domain(dom, d)) { return false; }
            if (!dom.finite()) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a comprehension generator domain must be finite because "
                        "this frontend expands it before SMT lowering", loc());
                return false;
            }
            std::vector<long long> range;
            if (dom.values.empty()) {
                for (long long v = dom.lo; v <= dom.hi; ++v) { range.push_back(v); }
            } else {
                range = dom.values;
            }
            for (const std::string& g : group) {
                GenVar gv;
                gv.name = g;
                gv.range = range;
                gv.is_bool = dom.is_bool;
                gv.size = range.size();
                gens.push_back(std::move(gv));
            }
            if (isP(",")) { eat(); continue; }
            break;
        }
        if (!expectP("]", d)) { return false; }
        const std::size_t after_all = mark();
        std::vector<std::string> vars;
        vars.reserve(gens.size());
        for (const GenVar& g : gens) { vars.push_back(g.name); }
        const Shadowed saved = shadow(vars);

        std::size_t total = 1;
        for (const GenVar& g : gens) { total *= g.size; }
        for (std::size_t k = 0; k < total; ++k) {
            std::size_t t = k;
            for (const GenVar& g : gens) {
                bindGenVar(g, t % g.size);
                t /= g.size;
            }
            // Filtered BEFORE the body is elaborated. A guard excludes tuples,
            // and the body need not be meaningful for the ones it excludes.
            bool keep = true;
            for (const std::size_t g : guards) {
                reset(g);
                bool holds = false;
                // Tried against a SINK, then reported once in this frontend's
                // own words. `constExpr` fails with "parameter 'b' has no
                // value" for a guard mentioning a decision variable, which is
                // true of the lookup and names the wrong thing: `b` is not a
                // missing parameter, it is a guard this subset cannot evaluate
                // at parse time.
                Uir::Diagnostics sink;
                if (!constGuard(holds, sink)) {
                    // A matrix generator's guards are the FOLDS Conjure writes
                    // over the bound matrix -- `and([t[q] < t[q+1] \/ ... | q :
                    // int(1..3)])` -- and `constGuard` reads comparisons and
                    // connectives, not comprehensions. Rather than give it a
                    // second comprehension expander, the guard is parsed by
                    // `expr()`, which already has one, and the result is
                    // evaluated: every leaf is a literal because every name in
                    // it is bound.
                    //
                    // Tried only AFTER the token path and only when a matrix
                    // generator is present, so that no existing comprehension
                    // changes which of the two read its guards.
                    bool via_expr = false;
                    if (saw_matrix_generator) {
                        reset(g);
                        Uir::Diagnostics sink2;
                        const H::ExprPtr ge = expr(sink2);
                        if (ge && !sink2.hasErrors() && constEval(ge, holds)) {
                            via_expr = true;
                        }
                    }
                    if (via_expr) {
                        if (!holds) { keep = false; break; }
                        continue;
                    }
                    reset(g);
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "a comprehension guard must be a parse-time condition over "
                            "the comprehension's own variables in this subset; this one "
                            "is not, and lowering it would elaborate the body for tuples "
                            "the comprehension does not denote",
                            loc());
                    unshadow(saved);
                    return false;
                }
                if (!holds) { keep = false; break; }
            }
            if (!keep) { continue; }
            reset(body_at);
            H::ExprPtr one = expr(d);
            if (!one) { return false; }
            out.push_back(std::move(one));
        }
        unshadow(saved);
        if (total == 0) {
            // The body's tokens are consumed either way; the result is
            // discarded.
            const std::size_t before = definedness_.size();
            reset(body_at);
            (void)expr(d);
            definedness_.resize(before);
        }
        reset(after_all);
        return true;
    }

    /** `and([...])`, `or([...])`, `sum([...])` over either list form. */
    H::ExprPtr comprehensionFold(std::string kind, Uir::Diagnostics& d) {
        eat();                                   // and / or / sum
        if (!expectP("(", d)) { return nullptr; }
        std::vector<H::ExprPtr> items;
        if (!listOperand(items, d)) { return nullptr; }
        if (!expectP(")", d)) { return nullptr; }
        return foldItems(kind, items);
    }

    H::ExprPtr parseAtom(Uir::Diagnostics& d) {
        const std::size_t before = definedness_.size();
        return closeBoolean(before, parseAtomValue(d));
    }

    H::ExprPtr parseAtomValue(Uir::Diagnostics& d) {
        // A fold before the identifier path, or `and` resolves as a name.
        if ((is("and") || is("or") || is("sum")) && peekIsP("(")) {
            return comprehensionFold(tok_.text, d);
        }
        // `toInt(b)` -- Essence' spells the Bool-to-Int coercion explicitly, and
        // Conjure emits it wherever a Boolean is summed. Exact: `ite(b, 1, 0)`
        // is the coercion, not an encoding of it, so there is nothing to record.
        if (is("toInt") && peekIsP("(")) {
            const Uir::SourceLoc at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            H::ExprPtr b = expr(d);
            if (!b || !expectP(")", d)) { return nullptr; }
            return H::mkOp(H::Op::ITE, {b, H::mkInt("1", at), H::mkInt("0", at)}, at);
        }
        // `[a1, a2] <lex [b1, b2]` -- a LEXICOGRAPHIC comparison of two lists,
        // in expression position and over decision-variable elements.
        //
        // Conjure writes this as a symmetry-breaking constraint between two
        // rows of a representation matrix. The guard path reads the same
        // spelling at parse time (`constGuardAtom`), where both sides are
        // constants; here they are terms, so the comparison has to be built:
        //
        //   a1 < b1 \/ (a1 = b1 /\ (a2 < b2 \/ (a2 = b2 /\ ... )))
        //
        // with the innermost comparison `<` for `<lex` and `<=` for `<=lex`,
        // which is what makes the two differ on equal lists.
        //
        // A bare `[...]` has no other meaning in this subset -- there is no
        // term for a matrix -- so reaching one here means a lex comparison or
        // a construct this frontend does not read, and both are named.
        if (isP("[") || (is("flatten") && peekIsP("("))) {
            const Uir::SourceLoc at = loc();
            std::vector<H::ExprPtr> lhs;
            if (!listOperand(lhs, d)) { return nullptr; }
            const bool strict = isP("<");
            if (!(isP("<") || isP("<=")) || !peekIsId("lex")) {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "a bracketed list is only read as the operand of `<lex` or "
                        "`<=lex` in this subset; this one is not, and a matrix has no "
                        "term here to be anything else",
                        at);
                return nullptr;
            }
            eat();                               // '<' or '<='
            eat();                               // 'lex'
            std::vector<H::ExprPtr> rhs;
            if (!listOperand(rhs, d)) { return nullptr; }
            if (lhs.size() != rhs.size()) {
                // Essence' orders a shorter list before a longer one that
                // extends it. Refused rather than implemented, because no
                // file here writes it and guessing the tie-break would be a
                // silent choice between two orderings.
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "`<lex` between lists of different lengths ("
                            + std::to_string(lhs.size()) + " and "
                            + std::to_string(rhs.size())
                            + ") is not implemented in this subset",
                        at);
                return nullptr;
            }
            return lexChain(lhs, rhs, strict, 0, at);
        }

        // `min([...])` / `max([...])` over a bracketed list.
        //
        // The HIR has no integer MIN or MAX -- only the FloatingPoint ones --
        // so this is an ITE fold: `min(a, b)` is `ite(a <= b, a, b)`, chained
        // left to right. That is the operator, not an encoding of it: no
        // choice is made and nothing is approximated, so there is nothing to
        // record.
        //
        // Lists, matrix slices and constant parameter matrices share the
        // same element enumeration used by sum and table scope operands.
        if ((is("min") || is("max")) && peekIsP("(")) {
            const bool want_min = is("min");
            const Uir::SourceLoc at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            std::vector<H::ExprPtr> items;
            if (!listOperand(items, d) || !expectP(")", d)) { return nullptr; }
            if (items.empty()) { requireDefined(H::mkBool(false)); return H::mkInt("0", at); }
            H::ExprPtr acc = asInteger(items.front());
            for (std::size_t k = 1; k < items.size(); ++k) {
                const H::ExprPtr one = asInteger(items[k]);
                acc = H::mkOp(H::Op::ITE,
                    {H::mkOp(want_min ? H::Op::LE : H::Op::GE, {acc, one}, at), acc, one}, at);
            }
            return acc;
        }

        // `alldifferent_except(L, v)` -- every element of L distinct, EXCEPT
        // that elements equal to `v` may repeat. Conjure emits it for a set
        // or relation representation where `v` is the "unused slot" marker.
        //
        // Emitted pairwise as `a_i = v \/ a_j = v \/ a_i != a_j`, which is
        // the implication `(a_i != v /\ a_j != v) -> a_i != a_j` written
        // without the negations. Pairwise rather than an n-ary `distinct`
        // because the exemption is per-pair: `distinct` over the non-`v`
        // elements is not expressible without knowing WHICH are `v`, and that
        // is exactly what the model leaves to the solver.
        //
        // The list is read through the same `bracketItems` a fold uses, so a
        // comprehension, a matrix literal and a one-element list all work
        // here for the same reason they work there.
        if (is("alldifferent_except") && peekIsP("(")) {
            const Uir::SourceLoc at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            if (!isP("[")) {
                // A bare matrix NAME is legal Essence' and is not read here:
                // this subset has no term for a matrix, so the elements could
                // not be enumerated. Refused by name rather than approximated.
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "'alldifferent_except' is read over a bracketed list in this "
                        "subset; over a matrix name it would need the matrix as a term",
                        at);
                return nullptr;
            }
            std::vector<H::ExprPtr> items;
            if (!bracketItems("alldifferent_except", items, d)) { return nullptr; }
            if (!expectP(",", d)) { return nullptr; }
            H::ExprPtr except = expr(d);
            if (!except || !expectP(")", d)) { return nullptr; }
            std::vector<H::ExprPtr> pairs;
            for (std::size_t a = 0; a < items.size(); ++a) {
                for (std::size_t b = a + 1; b < items.size(); ++b) {
                    pairs.push_back(H::mkOp(
                        H::Op::OR,
                        {H::mkOp(H::Op::EQ, {items[a], except}, at),
                         H::mkOp(H::Op::EQ, {items[b], except}, at),
                         H::mkOp(H::Op::NOT,
                                 {H::mkOp(H::Op::EQ, {items[a], items[b]}, at)}, at)},
                        at));
                }
            }
            // Fewer than two elements constrains nothing, and that is the
            // answer rather than an error: a one-element list HAS no repeated
            // pair.
            return foldItems("and", pairs);
        }

        // A numeric catch consumes its own pending guards. Boolean subterms
        // already close at their nearest relation and cannot escape as undef.
        if (is("catchUndef") && peekIsP("(")) {
            const Uir::SourceLoc at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            const std::size_t before = definedness_.size();
            H::ExprPtr e = expr(d);
            if (!e || !expectP(",", d)) { return nullptr; }
            H::ExprPtr defined = takeDefinedness(before);
            H::ExprPtr fallback = expr(d);
            if (!fallback || !expectP(")", d)) { return nullptr; }
            long long constant = 0;
            if (definedness_.size() != before || e->sort.kind != fallback->sort.kind
                || !constEvalInt(fallback, constant)) {
                d.error(ErrorCode::E_TYPE,
                        "catchUndef requires a defined constant fallback of the same type", at);
                return nullptr;
            }
            return defined ? H::mkOp(H::Op::ITE, {defined, e, fallback}, at) : e;
        }
        if (isP("(")) {
            eat();
            H::ExprPtr e = expr(d);
            if (!e || !expectP(")", d)) { return nullptr; }
            return e;
        }
        if (isP("|")) {
            // |x| is absolute value.
            eat();
            H::ExprPtr e = expr(d);
            if (!e || !expectP("|", d)) { return nullptr; }
            return H::mkOp(H::Op::ABS, {asInteger(e)});
        }
        if (isP("!")) {
            eat();
            H::ExprPtr e = parseAtom(d);
            if (!e) { return nullptr; }
            return H::mkOp(H::Op::NOT, {e});
        }
        if (tok_.kind == Token::INT) {
            const std::string v = tok_.text;
            eat();
            return H::mkInt(v);
        }
        if (is("true") || is("false")) {
            const bool v = is("true");
            eat();
            return H::mkBool(v);
        }
        if (is("forall") || is("forAll") || is("exists") || is("sum")) {
            return quantified(tok_.text, d);
        }
        if (is("gcc") && peekIsP("(")) {
            const Uir::SourceLoc at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            std::vector<H::ExprPtr> targets, values, counts;
            auto operand = [&](std::vector<H::ExprPtr>& items) {
                if (isP("[") && peekIsP("]")) { eat(); eat(); return true; }
                return listOperand(items, d);
            };
            if (!operand(targets) || !expectP(",", d)
                || !operand(values) || !expectP(",", d)
                || !operand(counts) || !expectP(")", d)) { return nullptr; }
            if (values.size() != counts.size()) {
                d.error(ErrorCode::E_TYPE,
                        "gcc value and occurrence matrices must have equal lengths", at);
                return nullptr;
            }
            for (auto* items : {&targets, &values, &counts}) {
                for (H::ExprPtr& item : *items) {
                    item = asInteger(item);
                    if (item->sort.kind != H::SortKind::INT) {
                        d.error(ErrorCode::E_TYPE, "gcc operands must have integer-compatible elements", at);
                        return nullptr;
                    }
                }
            }
            // Savile Row manual Table 1: each Vals[i] has exactly C[i]
            // occurrences. This is open cardinality: unlisted values remain
            // legal. Repeated target expressions count repeatedly, and repeated
            // cover values impose both corresponding count equalities.
            std::vector<H::ExprPtr> equalities;
            for (std::size_t i = 0; i < values.size(); ++i) {
                long long value = 0;
                if (!constEvalInt(values[i], value)) {
                    d.error(ErrorCode::E_TYPE,
                            "gcc values must be non-decision expressions", at);
                    return nullptr;
                }
                const H::ExprPtr constant = H::mkInt(std::to_string(value), at);
                std::vector<H::ExprPtr> matches;
                for (H::ExprPtr target : targets) {
                    matches.push_back(H::mkOp(H::Op::EQ, {target, constant}, at));
                }
                equalities.push_back(H::mkOp(H::Op::EQ,
                    {foldItems("sum", matches), counts[i]}, at));
            }
            return foldItems("and", equalities);
        }
        if (is("table") && peekIsP("(")) {
            const Uir::SourceLoc at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            std::vector<H::ExprPtr> scope;
            if (isP("[") && peekIsP("]")) { eat(); eat(); }
            else if (!listOperand(scope, d)) { return nullptr; }
            if (!expectP(",", d)) { return nullptr; }
            ConstMatrix tuples;
            bool empty_rows = false;
            if (isP("[") && peekIsP("]")) {
                eat(); eat(); empty_rows = true;
            } else if (isP("[")) {
                if (!constantMatrixLiteral(tuples, d)) { return nullptr; }
            } else if (tok_.kind == Token::IDENT && const_matrices_.count(tok_.text)) {
                tuples = const_matrices_.at(tok_.text);
                eat();
            } else {
                d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "table tuples require a constant matrix literal or named constant matrix", loc());
                return nullptr;
            }
            if (!expectP(")", d)) { return nullptr; }
            if (empty_rows) { return H::mkBool(false, at); }
            if (tuples.index.size() != 2) {
                d.error(ErrorCode::E_TYPE, "table tuples must be a two-dimensional matrix", at);
                return nullptr;
            }
            const long long columns = tuples.index[1].hi - tuples.index[1].lo + 1;
            const long long rows = tuples.index[0].hi - tuples.index[0].lo + 1;
            if (columns != static_cast<long long>(scope.size())) {
                d.error(ErrorCode::E_TYPE, "table tuple width must equal the scope size", at);
                return nullptr;
            }
            std::vector<H::ExprPtr> args{H::mkInt(std::to_string(columns)),
                                         H::mkInt(std::to_string(rows))};
            for (H::ExprPtr value : scope) { args.push_back(asInteger(value)); }
            for (long long value : tuples.cells) { args.push_back(H::mkInt(std::to_string(value))); }
            return H::mkGlobal("table", std::move(args), at);
        }
        if (is("allDiff") || is("alldifferent")) {
            const Uir::SourceLoc all_at = loc();
            eat();
            if (!expectP("(", d)) { return nullptr; }
            // `allDiff([e1, e2, e3])` -- the terms given explicitly, which is
            // how Conjure writes it over a comprehension. Emitted as the LIST
            // shape of `Hir::Global`, which `decompose-globals` tells apart
            // from the indexed one by the first argument's sort and encodes
            // pairwise under both styles -- explicitly so, because a list has
            // no index set to quantify over.
            if (isP("[") || (tok_.kind == Token::IDENT && peekIsP("["))
                || (tok_.kind == Token::IDENT && const_matrices_.count(tok_.text))
                || (is("flatten") && peekIsP("("))) {
                std::vector<H::ExprPtr> items;
                if (!listOperand(items, d)) { return nullptr; }
                if (!expectP(")", d)) { return nullptr; }
                // Fewer than two terms have no pair to constrain, the same
                // answer the indexed form gives for a one-cell matrix.
                if (items.size() < 2) { return H::mkBool(true, all_at); }
                for (H::ExprPtr& item : items) { item = asInteger(item); }
                return H::mkGlobal("alldifferent", items, all_at);
            }
            if (tok_.kind != Token::IDENT) {
                d.error(ErrorCode::E_PARSE,
                        "allDiff takes a matrix name or a bracketed list", loc());
                return nullptr;
            }
            const std::string m = tok_.text;
            const auto it = matrices_.find(m);
            if (it == matrices_.end()) {
                d.error(ErrorCode::E_TYPE, "'" + m + "' is not a matrix", loc());
                return nullptr;
            }
            eat();
            if (!expectP(")", d)) { return nullptr; }
            // Emitted as `Hir::Global` in the INDEXED shape, which this
            // frontend is the only one besides MiniZinc that can use: it
            // already declares a real HIR array, so there is an index set to
            // hand over, and the indexed shape is the one where ground and
            // quantified actually differ. The list shape is pairwise under
            // both styles -- explicitly, since a list has no index set to
            // quantify over -- so a frontend that flattens its matrix to
            // scalars can be routed through the pass but cannot vary the axis.
            //
            // This used to materialise the selects here and emit an n-ary
            // `DISTINCT`. That was terser output than the pass's ground
            // encoding produces, and it was also this frontend deciding the
            // encoding: `--profile quantified` did nothing. Whether the ground
            // encoding should itself emit n-ary `distinct` rather than pairwise
            // disequalities is a real question about a third point on the axis,
            // and it belongs to the pass rather than to one frontend.
            const H::Sort as = H::Sort::array(H::Sort::integer(),
                                              it->second.elem.is_bool
                                                  ? H::Sort::boolean()
                                                  : H::Sort::integer());
            // alldifferent's index bounds are over the FLATTENED space, which
            // for one dimension is the source span and for more is
            // 0..cells-1. Taking dimension one's span for a multi-dimensional
            // matrix would constrain the first row and leave the rest free --
            // a strictly weaker constraint that still translates.
            const long long lo = it->second.index.size() == 1
                                     ? it->second.index[0].lo : 0;
            const long long hi = it->second.index.size() == 1
                                     ? it->second.index[0].hi
                                     : it->second.cells() - 1;
            if (hi - lo + 1 < 2) { return H::mkBool(true); }
            return H::mkGlobal("alldifferent",
                               {H::mkIdent(m, as),
                                H::mkInt(std::to_string(lo)),
                                H::mkInt(std::to_string(hi + 1))});   // -> half-open
        }
        if (tok_.kind == Token::IDENT) {
            const std::string name = tok_.text;
            eat();
            // A parameter or a quantifier variable, substituted by value.
            const auto ci = consts_.find(name);
            if (ci != consts_.end() && !isP("[")) {
                return boolean_consts_.count(name) ? H::mkBool(ci->second != 0)
                                                   : H::mkInt(std::to_string(ci->second));
            }
            // A CONSTANT matrix bound by a generator over a matrix domain.
            // Before `matrices_`, which holds DECLARED decision matrices whose
            // reads lower to `(select m offset)`: a cell of this one is a
            // literal, and emitting a select would name a variable the model
            // never declared.
            const auto cmi = const_matrices_.find(name);
            if (cmi != const_matrices_.end()) {
                if (!expectP("[", d)) { return nullptr; }
                std::vector<long long> at;
                for (;;) {
                    long long one = 0;
                    if (!constExpr(one, d)) { return nullptr; }
                    at.push_back(one);
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (!expectP("]", d)) { return nullptr; }
                const ConstMatrix& mat = cmi->second;
                if (at.size() == mat.index.size()) {
                    for (std::size_t k = 0; k < at.size(); ++k) {
                        if (at[k] < mat.index[k].lo || at[k] > mat.index[k].hi) {
                            requireDefined(H::mkBool(false));
                            return mat.elem.is_bool ? H::mkBool(false) : H::mkInt("0");
                        }
                    }
                }
                long long cell = 0;
                if (!constMatrixCell(mat, name, at, cell, d)) { return nullptr; }
                return cmi->second.elem.is_bool ? H::mkBool(cell != 0)
                                                : H::mkInt(std::to_string(cell));
            }
            const auto mi = matrices_.find(name);
            if (mi != matrices_.end()) {
                if (!expectP("[", d)) { return nullptr; }
                std::vector<H::ExprPtr> subs;
                for (;;) {
                    H::ExprPtr one = expr(d);
                    if (!one) { return nullptr; }
                    subs.push_back(std::move(one));
                    if (isP(",")) { eat(); continue; }
                    break;
                }
                if (!expectP("]", d)) { return nullptr; }
                const Matrix& mat = mi->second;
                if (subs.size() != mat.index.size()) {
                    // Wrong ARITY is not an out-of-range index, and reporting
                    // it as one sends the reader to look at the bounds.
                    d.error(ErrorCode::E_TYPE,
                            "'" + name + "' is indexed by "
                                + std::to_string(mat.index.size())
                                + " subscript(s) but is read with "
                                + std::to_string(subs.size()), loc());
                    return nullptr;
                }
                const H::Sort as = H::Sort::array(H::Sort::integer(),
                                                  mat.elem.is_bool
                                                      ? H::Sort::boolean()
                                                      : H::Sort::integer());
                // Each dimension has its own definition domain; a flattened
                // offset alone cannot distinguish an invalid column from the
                // next valid row. Even constant invalid reads are expressions,
                // not type errors (manual section 3).
                std::vector<long long> fixed;
                bool all_const = true;
                bool outside = false;
                for (std::size_t k = 0; k < subs.size(); ++k) {
                    if (mat.index[k].is_bool && subs[k]->sort.kind != H::SortKind::BOOL) {
                        d.error(ErrorCode::E_TYPE, "a Boolean matrix index requires a Boolean subscript", loc());
                        return nullptr;
                    }
                    subs[k] = asInteger(subs[k]);
                    if (subs[k]->sort.kind != H::SortKind::INT) {
                        d.error(ErrorCode::E_TYPE, "a matrix subscript must be integer", loc());
                        return nullptr;
                    }
                    const long long lo = mat.index[k].lo, hi = mat.index[k].hi;
                    if (subs[k]->kind == H::ExprKind::LIT_INT) {
                        const long long v = std::stoll(
                            subs[k]->name.empty() ? std::to_string(subs[k]->int_value)
                                                  : subs[k]->name);
                        outside = outside || v < lo || v > hi;
                        fixed.push_back(v);
                    } else {
                        all_const = false;
                        requireDefined(H::mkOp(H::Op::AND,
                            {H::mkOp(H::Op::GE, {subs[k], H::mkInt(std::to_string(lo))}),
                             H::mkOp(H::Op::LE, {subs[k], H::mkInt(std::to_string(hi))})}));
                    }
                }
                if (outside) {
                    requireDefined(H::mkBool(false));
                    return mat.elem.is_bool ? H::mkBool(false) : H::mkInt("0");
                }
                if (mat.index.size() == 1) {
                    return H::mkOp(H::Op::SELECT, {H::mkIdent(name, as), subs[0]});
                }
                if (!all_const) {
                    // The flattened offset of a non-constant subscript is an
                    // arithmetic term rather than a number, so it is BUILT.
                    //
                    // This was refused until 2026-09-22 on the grounds that
                    // "every quantifier this frontend expands produces
                    // constants", so a surviving variable subscript meant
                    // something unread. That was true of the quantifiers and
                    // false of the corpus: Conjure writes a subscript that is
                    // an expression over comprehension variables --
                    // `m[q1 + 1, q2]` -- which expansion turns into a term,
                    // not a literal.
                    //
                    // Pending per-dimension guards make out-of-domain reads
                    // false at the source Boolean boundary, before lowering.
                    return H::mkOp(H::Op::SELECT,
                                   {H::mkIdent(name, as),
                                    flatOffsetTerm(mat, subs, loc())});
                }
                return H::mkOp(
                    H::Op::SELECT,
                    {H::mkIdent(name, as),
                     H::mkInt(std::to_string(mat.offsetOf(fixed)))});
            }
            const auto si = sorts_.find(name);
            if (si != sorts_.end()) { return H::mkIdent(name, si->second); }
            // A name Essence' DEFINES is a coverage gap, not an undeclared
            // identifier, and the two codes feed different statistics --
            // "malformed input" against "missing feature". Conjure writes
            // `and([...])` and `or([...])` for the n-ary folds over a
            // comprehension wherever this frontend's `forall`/`exists` would
            // appear in hand-written Essence', so twelve of the twenty-four
            // upstream files reported a name the language defines as one the
            // model forgot to declare.
            static const char* kBuiltins[] = {
                "product", "min", "max", "allDiff",
                "table", "atmost", "atleast",
                "freq", "hist", "together", "apart", nullptr};
            for (int i = 0; kBuiltins[i] != nullptr; ++i) {
                if (name == kBuiltins[i]) {
                    d.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "'" + name + "' is an Essence' operator this subset does "
                            "not implement; skipping it would drop a constraint and "
                            "weaken the model",
                            loc());
                    return nullptr;
                }
            }
            d.error(ErrorCode::E_TYPE, "'" + name + "' is not declared", loc());
            return nullptr;
        }
        d.error(ErrorCode::E_PARSE, "unexpected '" + tok_.text + "' in an expression",
                loc());
        return nullptr;
    }

    std::string file_;
    std::vector<Token> toks_;
    std::size_t pos_ = 0;
    Token       tok_;
    H::ConstraintModelPtr model_;
    Uir::TranslationReport* report_ = nullptr;
    /** Search directives are noted once, not once per occurrence. */
    bool said_search_ = false;
    bool said_partiality_ = false;
    std::vector<H::ExprPtr> definedness_;
    std::unordered_map<std::string, long long> consts_;
    std::unordered_set<std::string> boolean_consts_;
    std::unordered_map<std::string, ConstMatrix> const_matrices_;
    std::unordered_map<std::string, Domain> domains_;
    std::unordered_map<std::string, H::Sort> sorts_;
    std::unordered_map<std::string, Matrix> matrices_;
    std::vector<std::string> given_names_;
};


class EssenceLanguage : public Language {
public:
    EssenceLanguage() {
        // Multi-dimensional matrices landed 2026-09-20, flattened row-major
        // and recorded. Reading one at a NON-CONSTANT subscript is a separate
        // construct and enters `total` with it -- implementing the first is
        // what revealed the second, and a table that only moved the gap into
        // the supported column would report the ratio improving by forgetting
        // something.
        coverage_.total = 13;
        coverage_.supported = 10;
        coverage_.missing = {
            "set, relation, function and partition domains",
            "global constraints beyond allDiff",
            "quantifier bodies over matrix slices",
        };
    }

    std::string id() const override { return "essence"; }
    std::string displayName() const override { return "Essence' (Savile Row input)"; }
    std::string version() const override { return "1.0"; }
    std::vector<std::string> extensions() const override { return {".eprime"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    /** Parameters arrive in a .param file. Overriding this is not optional:
     *  translate() refuses a unit carrying data files unless the language says
     *  it reads them, so that a frontend which forgets cannot silently
     *  translate the model alone and report success on a problem it never
     *  fully read. */
    bool acceptsDataFiles() const override { return true; }

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

        // Parameter scalars and rectangular constant matrices are read before
        // the source model. Their values determine every range expanded
        // against, so they have to be known before the model is parsed.
        ParameterValues params;
        for (const std::string& path : unit.data_paths) {
            std::ifstream in(path, std::ios::binary);
            if (!in) {
                out.diagnostics.error(ErrorCode::E_IO, "cannot open '" + path + "'");
                return out;
            }
            std::ostringstream ss;
            ss << in.rdbuf();
            if (!readParams(ss.str(), path, params, out.diagnostics)) { return out; }
        }

        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            EssenceParser p(src, name);
            out.model = p.parse(params, out.diagnostics, out.report);
            if (out.model) {
                out.semantics.add(
                    p.semanticContract(*out.model, out.report.fidelity()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("essence frontend: ") + e.what());
        }
        return out;
    }

private:
    static bool readParams(const std::string& text, const std::string& path,
                           ParameterValues& out, Uir::Diagnostics& diags) {
        EssenceParser parameters(text, path);
        return parameters.readParameterAssignments(out, diags);
    }

    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkEssenceLanguage() { return std::make_shared<EssenceLanguage>(); }

} // namespace SOMTParser::Lang
