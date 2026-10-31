/* -*- Source -*-
 * OPB / WBO (pseudo-Boolean) frontend.
 *
 * The format is docs/languages/opb-wbo.md; its `implicit-constraints` block is
 * the specification this file implements, and each entry has a fixture in
 * languages/opb/instances.
 *
 * Three obligations, none of them written in any line of a file:
 *
 *   1. **Every variable is Boolean.** OPB uses `x` arithmetically in linear
 *      sums while its domain is {0,1}, and nothing declares that. Dropping it
 *      yields a strictly weaker model that parses, type-checks and answers a
 *      different question.
 *   2. **`~x` is `(1 - x)`**, not a separate variable. Treating it as one
 *      doubles the variable count and loses the relationship entirely.
 *   3. **A soft constraint's cost is incurred exactly when it is VIOLATED.**
 *      The objective term is the reification of its negation, which the file
 *      never writes.
 *
 * And the one that is written down and easy to read as decoration: **WBO's
 * `soft: T ;` is a hard admissibility bound**, not a presentational hint. The
 * format document's own Example 3 has minimum cost exactly 6 with `soft: 6;`,
 * and the correct answer is UNSATISFIABLE rather than "optimum 6". Dropping T
 * ADMITS assignments the format rejects -- more models, not fewer -- so the
 * direction of the loss is sound = false, complete = true.
 *
 * WCNF's `top` is the same word for a different thing: a marker saying "clauses
 * this heavy are hard". test/languages/test_pb_cross_format.cpp asserts the two
 * apart.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/opb.h"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <gmpxx.h>
#include <limits>
#include <memory>
#include <new>
#include <sstream>
#include <string>
#include <system_error>
#include <unordered_map>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

/** A coefficient and the literals it multiplies. One literal for a linear
 *  instance; several make a PRODUCT, which is a conjunction and, over {0,1}
 *  integers, is exactly their arithmetic product. */
constexpr std::size_t kMissingTermPart = std::numeric_limits<std::size_t>::max();

struct Term {
    // Text is interned per parse. Linear terms need no separately allocated
    // literal vector; products retain their original literal order.
    std::size_t coefficient = kMissingTermPart;
    std::size_t firstLiteral = kMissingTermPart;
    std::vector<std::size_t> additionalLiterals;
};

struct Constraint {
    std::vector<Term> sum;
    std::string       op;               // >=, =, >, <, <=, !=
    std::string       degree;
    std::string       cost;             // WBO soft cost; empty for a hard one
    int               line = 0;
};

class OpbParser {
public:
    OpbParser(std::istream& input, std::string file, bool strict)
        : input_(input), file_(std::move(file)), strict_(strict) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report,
                               const char*& allocationStage) {
        report_ = &report;
        allocationStage = "source records";
        if (!read(diags)) { return nullptr; }
        // Interning is complete; only the indexed coefficient values are
        // needed while constructing HIR, not their duplicate hash-table keys.
        decltype(coefficient_index_){}.swap(coefficient_index_);
        allocationStage = "HIR construction";
        return build(diags);
    }

private:
    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = line;
        l.column = 1;
        return l;
    }

    /** SMT-LIB numerals have no leading `+`; OPB's grammar does
     *  (`<integer>::= <unsigned_integer> | "+"... | "-"...`), and the engine's
     *  big-integer parser rejects one. Stripped at the boundary rather than
     *  everywhere downstream. */
    static std::string numeral(const std::string& s) {
        return (!s.empty() && s[0] == '+') ? s.substr(1) : s;
    }

    static bool isIntegerText(const std::string& s) {
        if (s.empty()) { return false; }
        std::size_t i = (s[0] == '+' || s[0] == '-') ? 1 : 0;
        if (i == s.size()) { return false; }
        for (; i < s.size(); ++i) {
            if (!std::isdigit(static_cast<unsigned char>(s[i]))) { return false; }
        }
        return true;
    }

    /** Statements end with `;` and "may be very long", so the file is read as a
     *  token stream split on `;` rather than line by line -- the format document
     *  warns explicitly against reading a line as a whole. */
    bool read(Uir::Diagnostics& diags) {
        std::istream& in = input_;
        std::string raw;
        int lineno = 0;
        std::string stmt;
        int stmt_line = 0;

        while (std::getline(in, raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            std::string trimmed = raw;
            const std::size_t a = trimmed.find_first_not_of(" \t");
            if (a == std::string::npos) { continue; }
            if (trimmed[a] == '*') { continue; }   // comment, incl. header hints
            if (stmt.empty()) { stmt_line = lineno; }
            stmt += " " + trimmed;
            std::size_t semi;
            while ((semi = stmt.find(';')) != std::string::npos) {
                const std::string one = stmt.substr(0, semi);
                stmt.erase(0, semi + 1);
                if (!statement(one, stmt_line, diags)) { return false; }
                stmt_line = lineno;
            }
        }
        if (in.bad()) {
            diags.error(ErrorCode::E_IO, "failed while reading OPB source", at(lineno));
            return false;
        }
        if (stmt.find_first_not_of(" \t") != std::string::npos) {
            diags.error(ErrorCode::E_PARSE, "the last statement is not terminated by ';'",
                        at(stmt_line));
            return false;
        }
        return true;
    }

    bool statement(const std::string& text, int line, Uir::Diagnostics& diags) {
        std::istringstream ts(text);
        std::vector<std::string> tok;
        std::string t;
        while (ts >> t) { tok.push_back(t); }
        if (tok.empty()) { return true; }

        if (tok[0] == "min:" || tok[0] == "max:") {
            if (!objective_.sum.empty() || objective_seen_) {
                diags.error(ErrorCode::E_PARSE, "more than one objective", at(line));
                return false;
            }
            objective_seen_ = true;
            maximise_ = (tok[0] == "max:");
            objective_.line = line;
            return terms(tok, 1, tok.size(), objective_.sum, line, diags);
        }
        if (tok[0] == "soft:") {
            // §2.4. `soft: T ;` opens a WBO file; `soft: ;` means T = infinity.
            if (wbo_) {
                diags.error(ErrorCode::E_PARSE, "more than one soft header", at(line));
                return false;
            }
            wbo_ = true;
            soft_line_ = line;
            if (tok.size() == 1) { return true; }        // T = infinity
            if (tok.size() != 2 || !isIntegerText(tok[1]) || tok[1][0] == '-') {
                diags.error(ErrorCode::E_PARSE,
                            "the soft header takes one non-negative integer or nothing",
                            at(line));
                return false;
            }
            top_ = nonnegativeDecimal(tok[1]);
            return true;
        }

        Constraint c;
        c.line = line;
        std::size_t i = 0;
        if (tok[0] == "[") {
            diags.error(ErrorCode::E_PARSE,
                        "a soft cost is written `[c]` without spaces inside", at(line));
            return false;
        }
        if (tok[0].size() >= 2 && tok[0].front() == '[') {
            // `[cost] <constraint>` -- a soft constraint. Only in a WBO file.
            const std::size_t close = tok[0].find(']');
            if (close == std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "unterminated soft cost", at(line));
                return false;
            }
            c.cost = tok[0].substr(1, close - 1);
            if (!isIntegerText(c.cost) || c.cost[0] == '-'
                || compareDecimal(numeral(c.cost), "0") == 0) {
                diags.error(ErrorCode::E_PARSE,
                            "a soft cost must be a strictly positive integer, not '"
                                + c.cost + "'",
                            at(line));
                return false;
            }
            c.cost = nonnegativeDecimal(c.cost);
            if (!wbo_) {
                diags.error(ErrorCode::E_PARSE,
                            "a soft constraint needs a `soft:` header; this file has none",
                            at(line));
                return false;
            }
            i = 1;
        }

        // Find the relational operator.
        static const char* kOps[] = {">=", "<=", "!=", "=", ">", "<", nullptr};
        std::size_t op_at = tok.size();
        for (std::size_t k = i; k < tok.size(); ++k) {
            for (int o = 0; kOps[o] != nullptr; ++o) {
                if (tok[k] == kOps[o]) { op_at = k; break; }
            }
            if (op_at != tok.size()) { break; }
        }
        if (op_at == tok.size() || op_at + 1 >= tok.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "a constraint is `<sum> <op> <degree>`", at(line));
            return false;
        }
        c.op = tok[op_at];
        if (op_at + 2 != tok.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "a constraint's degree is a single integer", at(line));
            return false;
        }
        c.degree = tok[op_at + 1];
        if (!isIntegerText(c.degree)) {
            diags.error(ErrorCode::E_PARSE,
                        "'" + c.degree + "' is not an integer degree", at(line));
            return false;
        }
        if (!terms(tok, i, op_at, c.sum, line, diags)) { return false; }
        constraints_.push_back(std::move(c));
        return true;
    }

    /** `<coeff> <lit>+` repeated. A coefficient always precedes its literals,
     *  which is what lets the two be told apart without lookahead. */
    bool terms(const std::vector<std::string>& tok, std::size_t from, std::size_t to,
               std::vector<Term>& out, int line, Uir::Diagnostics& diags) {
        Term cur;
        for (std::size_t k = from; k < to; ++k) {
            const std::string& s = tok[k];
            if (isIntegerText(s)) {
                if (cur.coefficient != kMissingTermPart) {
                    if (cur.firstLiteral == kMissingTermPart) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a coefficient must be followed by at least one "
                                    "literal", at(line));
                        return false;
                    }
                    out.push_back(std::move(cur));
                    cur = Term{};
                }
                auto entry = coefficient_index_.emplace(s, coefficients_.size());
                if (entry.second) { coefficients_.push_back(s); }
                cur.coefficient = entry.first->second;
                continue;
            }
            if (cur.coefficient == kMissingTermPart) {
                diags.error(ErrorCode::E_PARSE,
                            "'" + s + "' has no coefficient", at(line));
                return false;
            }
            const std::size_t variable = varOf(s);
            if (variable >= kMissingTermPart / 2) {
                diags.error(ErrorCode::E_RESOURCE, "OPB variable table exceeds addressable storage",
                            at(line));
                return false;
            }
            const std::size_t literal = variable * 2 + (!s.empty() && s[0] == '~');
            if (cur.firstLiteral == kMissingTermPart) { cur.firstLiteral = literal; }
            else { cur.additionalLiterals.push_back(literal); }
        }
        if (cur.coefficient != kMissingTermPart) {
            if (cur.firstLiteral == kMissingTermPart) {
                diags.error(ErrorCode::E_PARSE,
                            "a coefficient must be followed by at least one literal",
                            at(line));
                return false;
            }
            out.push_back(std::move(cur));
        }
        return true;
    }

    /** Register the variable a literal refers to, stripping `~`. */
    std::size_t varOf(const std::string& lit) {
        const std::string name = (!lit.empty() && lit[0] == '~') ? lit.substr(1) : lit;
        const auto it = var_index_.find(name);
        if (it != var_index_.end()) { return it->second; }
        // var_index_.size(), not vars_.size(): vars_ is never filled, so
        // every variable took index 0 and the ordered list came out with
        // empty names at every other position -- which typeCheck caught as
        // 'a declaration has no name', one layer down from the cause.
        return var_index_.emplace(name, var_index_.size()).first->second;
    }

    // ---- construction ----------------------------------------------------

    H::ExprPtr number(const std::string& text, int line) const {
        const std::string key = numeral(text);
        const auto found = numbers_.find(key);
        if (found != numbers_.end()) { return found->second; }
        return numbers_.emplace(key, H::mkInt(key, at(line))).first->second;
    }

    H::ExprPtr literal(std::size_t lit, int line) const {
        const auto found = literals_.find(lit);
        if (found != literals_.end()) { return found->second; }
        const bool neg = (lit & 1) != 0;
        const std::size_t index = lit / 2;
        H::ExprPtr& variable = symbols_[index];
        if (!variable) { variable = H::mkIdent(ordered_[index], H::Sort::integer(), at(line)); }
        // Obligation 2: `~x` is (1 - x). Not a separate variable, and not a
        // Boolean negation either -- these are Int-valued 0/1 terms summed
        // arithmetically, so the complement is arithmetic too.
        H::ExprPtr value = neg
            ? H::mkOp(H::Op::SUB, {number("1", line), variable}, at(line))
            : variable;
        return literals_.emplace(lit, std::move(value)).first->second;
    }

    H::ExprPtr sumOf(const std::vector<Term>& terms, int line) const {
        std::vector<H::ExprPtr> addends;
        addends.reserve(terms.size());
        for (const auto& t : terms) {
            const auto coefficient = number(coefficients_[t.coefficient], line);
            if (coefficient->name == "0") { continue; }
            std::vector<H::ExprPtr> factors;
            factors.reserve(t.additionalLiterals.size() + 2);
            if (coefficient->name != "1") { factors.push_back(coefficient); }
            // A PRODUCT of literals is a conjunction, and over {0,1} integers
            // that is exactly their arithmetic product -- which is why the
            // Boolean domain of obligation 1 has to be materialised: without
            // the [0,1] bounds this multiplication means something else.
            factors.push_back(literal(t.firstLiteral, line));
            for (const auto l : t.additionalLiterals) { factors.push_back(literal(l, line)); }
            addends.push_back(factors.size() == 1
                                  ? factors.front()
                                  : H::mkOp(H::Op::MUL, std::move(factors), at(line)));
        }
        if (addends.empty()) { return number("0", line); }
        if (addends.size() == 1) { return addends.front(); }
        return H::mkOp(H::Op::ADD, std::move(addends), at(line));
    }

    H::ExprPtr relation(const Constraint& c) const {
        H::ExprPtr lhs = sumOf(c.sum, c.line);
        H::ExprPtr rhs = number(c.degree, c.line);
        if (c.op == ">=") { return H::mkOp(H::Op::GE, {lhs, rhs}, at(c.line)); }
        if (c.op == "<=") { return H::mkOp(H::Op::LE, {lhs, rhs}, at(c.line)); }
        if (c.op == ">")  { return H::mkOp(H::Op::GT, {lhs, rhs}, at(c.line)); }
        if (c.op == "<")  { return H::mkOp(H::Op::LT, {lhs, rhs}, at(c.line)); }
        if (c.op == "=")  { return H::mkOp(H::Op::EQ, {lhs, rhs}, at(c.line)); }
        // `!=` is a DISEQUALITY and the one operator with no direct linear
        // counterpart -- it is the negation of an equality, not a comparison.
        return H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {lhs, rhs}, at(c.line))},
                       at(c.line));
    }

    bool packableHardRow(const Constraint& row) const {
        // Finite WBO admissibility is sum(violated weights) < top. Every
        // weight is positive, so a row weighted at least top must hold.
        // build() already enforces these rows as hard constraints; admit the
        // same exact comparison to compact storage without a relaxation or
        // objective contribution. The decimal comparison is unbounded.
        const bool required = row.cost.empty()
            || (wbo_ && !top_.empty() && compareDecimal(row.cost, top_) >= 0);
        if (!required || (row.op != "<=" && row.op != ">=" && row.op != "=")) {
            return false;
        }
        for (const auto& term : row.sum) {
            if ((term.firstLiteral & 1) != 0 || !term.additionalLiterals.empty()) {
                return false;
            }
        }
        return true;
    }

    static std::string canonicalInteger(const std::string& value) {
        const bool negative = !value.empty() && value.front() == '-';
        const std::size_t first = !value.empty() && (value.front() == '+' || negative) ? 1 : 0;
        const std::size_t nonzero = value.find_first_not_of('0', first);
        if (nonzero == std::string::npos) { return "0"; }
        return (negative ? "-" : "") + value.substr(nonzero);
    }

    std::uint64_t packedNumber(H::PackedLinearRows& data, const std::string& value) {
        const std::string canonical = canonicalInteger(value);
        const auto inserted = packed_number_index_.emplace(canonical, data.numbers.size());
        if (inserted.second) { data.numbers.push_back(canonical); }
        return inserted.first->second;
    }

    std::shared_ptr<H::PackedLinearRows> preparePackedRows() {
        // Source records already give exact declaration ordinals. Large hard
        // linear rows can use the shared checked matrix representation instead
        // of allocating an Expr for every occurrence of a product and sum.
        constexpr std::size_t threshold = 65536;
        std::size_t rows = 0;
        std::size_t terms = 0;
        for (const auto& row : constraints_) {
            if (!packableHardRow(row)) { continue; }
            ++rows;
            terms += std::min(row.sum.size(), threshold - terms);
            if (rows >= threshold || terms >= threshold) {
                report_->addChoice({file_, "OPB hard linear rows", "packed-linear-rows",
                    Uir::Fidelity::exact(),
                    "exact linear comparisons share compact coefficient and column storage; "
                    "all Int Boolean domains, objectives and other rows are retained"});
                return std::make_shared<H::PackedLinearRows>();
            }
        }
        return nullptr;
    }

    bool appendPackedHardRow(const Constraint& source, H::PackedLinearRows* data) {
        if (!data || !packableHardRow(source)) { return false; }
        constexpr std::size_t batch_rows = 4096;
        if (data->batches.empty() || data->batches.back().rows.size() >= batch_rows) {
            data->batches.emplace_back();
            data->batches.back().source_file = file_;
            data->batches.back().rows.reserve(batch_rows);
        }
        auto& batch = data->batches.back();
        H::PackedLinearRow row;
        row.begin = batch.terms.size();
        row.source_line = static_cast<std::uint32_t>(source.line);
        row.relation = source.op == "<=" ? H::LinearRowRelation::LE
                     : source.op == ">=" ? H::LinearRowRelation::GE : H::LinearRowRelation::EQ;
        row.rhs = packedNumber(*data, source.degree);
        for (const auto& term : source.sum) {
            batch.terms.push_back({term.firstLiteral / 2,
                                  packedNumber(*data, coefficients_[term.coefficient])});
        }
        row.end = batch.terms.size();
        batch.rows.push_back(row);
        return true;
    }

    bool usePackedWeightedRows() const {
        if (!wbo_) { return false; }
        constexpr std::size_t threshold = 65536;
        std::size_t rows = 0, terms = 0;
        bool genuine_soft = false;
        for (const auto& row : constraints_) {
            if (row.op != "<=" && row.op != ">=" && row.op != "=") { return false; }
            for (const auto& term : row.sum) {
                if (!term.additionalLiterals.empty()) { return false; }
            }
            genuine_soft |= !row.cost.empty()
                && (top_.empty() || compareDecimal(row.cost, top_) < 0);
            rows += rows < threshold;
            terms += std::min(row.sum.size(), threshold - terms);
        }
        return genuine_soft && (rows >= threshold || terms >= threshold);
    }

    void appendExactRow(H::PackedLinearRows& data,
                        const std::vector<H::PackedLinearTerm>& terms,
                        H::LinearRowRelation relation, const mpz_class& rhs, int line) {
        constexpr std::size_t batch_rows = 4096;
        if (data.batches.empty() || data.batches.back().rows.size() >= batch_rows) {
            data.batches.emplace_back();
            data.batches.back().source_file = file_;
            data.batches.back().rows.reserve(batch_rows);
        }
        auto& batch = data.batches.back();
        H::PackedLinearRow row;
        row.begin = batch.terms.size();
        batch.terms.insert(batch.terms.end(), terms.begin(), terms.end());
        row.end = batch.terms.size();
        row.relation = relation;
        row.rhs = packedNumber(data, rhs.get_str());
        row.source_line = static_cast<std::uint32_t>(line);
        batch.rows.push_back(row);
    }

    H::ConstraintModelPtr buildPackedWeightedRows(H::ConstraintModelPtr model) {
        auto data = std::make_shared<H::PackedLinearRows>();
        model->packed_linear_rows = data;
        std::string prefix = "!wbo";
        // General OPB identifiers need not be x followed by a numeral. Reserve
        // a whole fresh namespace, then disjoint violation/cost suffixes.
        while (std::any_of(ordered_.begin(), ordered_.end(), [&](const std::string& name) {
                   return name.rfind(prefix, 0) == 0;
               })) { prefix += '!'; }
        std::size_t violation_count = 0, cost_count = 0;
        std::uint64_t previous_cost = 0;
        bool has_previous_cost = false;
        std::vector<H::PackedLinearTerm> costs;
        constexpr std::size_t cost_batch = 256;
        const auto one = packedNumber(*data, "1");
        const auto minus_one = packedNumber(*data, "-1");

        const auto declare = [&](const std::string& name, bool binary, int line) {
            H::VarDecl declaration;
            declaration.name = name;
            declaration.sort = H::Sort::integer();
            declaration.loc = at(line);
            if (binary) {
                declaration.lower_bound = number("0", line);
                declaration.upper_bound = number("1", line);
            }
            const auto column = static_cast<std::uint64_t>(model->decls.size());
            model->decls.push_back(std::move(declaration));
            return column;
        };
        const auto flush_cost = [&]() {
            if (costs.empty()) { return; }
            const auto current = declare(prefix + "_cost" + std::to_string(cost_count++),
                                         false, soft_line_);
            if (has_previous_cost) { costs.push_back({previous_cost, one}); }
            costs.push_back({current, minus_one});
            // Every prefix is a uniquely defined, unrestricted Int. It must
            // not inherit the binary domains of source/violation coordinates.
            appendExactRow(*data, costs, H::LinearRowRelation::EQ, mpz_class(0), soft_line_);
            costs.clear();
            previous_cost = current;
            has_previous_cost = true;
        };

        for (auto& source : constraints_) {
            std::vector<H::PackedLinearTerm> terms;
            terms.reserve(source.sum.size() + 1);
            mpz_class rhs(canonicalInteger(source.degree));
            mpz_class lower(0), upper(0);
            for (const auto& term : source.sum) {
                mpz_class coefficient(canonicalInteger(coefficients_[term.coefficient]));
                if ((term.firstLiteral & 1) != 0) {
                    // c*(1-x) = c-c*x, including signed and repeated literals.
                    rhs -= coefficient;
                    coefficient = -coefficient;
                }
                if (coefficient < 0) { lower += coefficient; }
                else { upper += coefficient; }
                terms.push_back({term.firstLiteral / 2,
                                 packedNumber(*data, coefficient.get_str())});
            }
            const bool required = source.cost.empty()
                || (!top_.empty() && compareDecimal(source.cost, top_) >= 0);
            if (required) {
                const auto relation = source.op == ">=" ? H::LinearRowRelation::GE
                    : source.op == "<=" ? H::LinearRowRelation::LE : H::LinearRowRelation::EQ;
                appendExactRow(*data, terms, relation, rhs, source.line);
            } else {
                const auto weight = packedNumber(*data, source.cost);
                const auto violation = [&](bool ge) {
                    const auto column = declare(prefix + "_v" + std::to_string(violation_count++),
                                                true, source.line);
                    // S in [L,U] and r in {0,1}. Both rows together define
                    // r=1 iff the comparison is false, even away from an
                    // optimum, and even if its RHS is outside [L,U]. Bounds
                    // may be loose for repeated variables but remain valid.
                    mpz_class first = ge ? mpz_class(rhs - lower) : mpz_class(rhs - upper);
                    terms.push_back({column, packedNumber(*data, first.get_str())});
                    appendExactRow(*data, terms, ge ? H::LinearRowRelation::GE
                                                  : H::LinearRowRelation::LE,
                                   rhs, source.line);
                    mpz_class second = ge ? mpz_class(upper - rhs + 1) : mpz_class(lower - rhs - 1);
                    terms.back().coefficient = packedNumber(*data, second.get_str());
                    appendExactRow(*data, terms, ge ? H::LinearRowRelation::LE
                                                  : H::LinearRowRelation::GE,
                                   ge ? upper : lower, source.line);
                    terms.pop_back();
                    costs.push_back({column, weight});
                    if (costs.size() >= cost_batch) { flush_cost(); }
                };
                if (source.op == "=" || source.op == ">=") { violation(true); }
                if (source.op == "=" || source.op == "<=") { violation(false); }
                // Equality's two bits mean S<b and S>b; both cannot be 1.
                // Their sum is exactly [S!=b], so weight is charged once.
            }
            decltype(source.sum){}.swap(source.sum);
        }
        flush_cost();
        // Eligibility requires a genuine soft row, hence at least one cost.
        if (!top_.empty()) {
            const mpz_class bound = mpz_class(top_) - 1;
            appendExactRow(*data, {{previous_cost, one}}, H::LinearRowRelation::LE,
                           bound, soft_line_);
        }
        H::Objective objective;
        objective.kind = H::ObjKind::MINIMIZE;
        objective.term = H::mkIdent(model->decls[previous_cost].name, H::Sort::integer(), at(soft_line_));
        objective.name = "obj";
        objective.loc = at(soft_line_);
        model->objectives.push_back(std::move(objective));
        report_->addChoice({file_, "WBO linear rows", "packed-linear-rows",
            Uir::Fidelity::exact(),
            "exact source comparisons, violation equivalences and cost-prefix equalities use compact rows"});
        report_->addChoice({file_, "WBO weighted linear rows", "packed-exact-weighted-violations",
            Uir::Fidelity::exact(),
            "binary violation indicators and Int cost prefixes are uniquely determined by each "
            "source assignment; exact integer rows preserve every violated weight and the declared strict top"});
        return model;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags) {
        auto model = std::make_shared<H::ConstraintModel>();

        // Obligation 1: every variable is Boolean, taking values in {0,1}, and
        // NO LINE SAYS SO. It is used arithmetically in linear sums, so the
        // domain is materialised as bounds on an Int rather than as a Bool
        // sort -- a Bool cannot be multiplied by a coefficient.
        ordered_.resize(var_index_.size());
        symbols_.resize(var_index_.size());
        for (const auto& [name, idx] : var_index_) { ordered_[idx] = name; }
        // Literal IDs now resolve through ordered_; release the registration
        // dictionary before allocating declarations and expressions.
        decltype(var_index_){}.swap(var_index_);
        for (const auto& name : ordered_) {
            H::VarDecl d;
            d.name = name;
            d.sort = H::Sort::integer();
            d.lower_bound = number("0", 0);
            d.upper_bound = number("1", 0);
            model->decls.push_back(d);
        }

        if (usePackedWeightedRows()) { return buildPackedWeightedRows(std::move(model)); }

        auto packed = preparePackedRows();
        model->packed_linear_rows = packed;

        if (!wbo_) {
            for (auto& c : constraints_) {
                if (appendPackedHardRow(c, packed.get())) {
                    decltype(c.sum){}.swap(c.sum);
                    continue;
                }
                H::Constraint hc;
                hc.loc = at(c.line);
                hc.formula = relation(c);
                model->constraints.push_back(hc);
                decltype(c.sum){}.swap(c.sum);
            }
            if (objective_seen_) {
                H::Objective o;
                o.kind = maximise_ ? H::ObjKind::MAXIMIZE : H::ObjKind::MINIMIZE;
                o.term = sumOf(objective_.sum, objective_.line);
                o.name = "obj";
                o.loc = at(objective_.line);
                model->objectives.push_back(o);
            }
            return model;
        }

        // ---- WBO ----------------------------------------------------------
        //
        // §4.4's option B is exact only when the threshold is provably vacuous;
        // option A is the only complete one. Which applies is decided per
        // instance here rather than assumed, because option C -- dropping T
        // unchecked -- reports a cost-6 optimum on the format document's own
        // Example 3 where the correct answer is UNSATISFIABLE.
        //
        // The check has to be done in unbounded arithmetic: costs are big
        // integers by design. Summed as decimal text via a small helper rather
        // than as long long, since a corpus instance can exceed it.
        const bool infinite_top = top_.empty();
        std::string sumcost = "0";
        for (const auto& c : constraints_) {
            if (!c.cost.empty()) { sumcost = addDecimal(sumcost, c.cost); }
        }
        // T is vacuous when every assignment is admissible, i.e. when the worst
        // possible cost is already below it: T > sumcost.
        const bool vacuous = infinite_top || compareDecimal(top_, sumcost) > 0;

        if (vacuous) {
            // Recorded even though the flags match option A's. The two branches
            // build genuinely different scripts -- one with relaxation
            // variables and an objective, one with native soft constraints --
            // and `strategy` is the only field that says which ran. A report
            // that only carried fidelity would show these as identical
            // translations, and a solver-time difference between them would
            // look like noise rather than an encoding effect.
            Uir::EncodingChoice ch;
            ch.site       = file_;
            ch.unified_op = "wbo-threshold";
            ch.strategy   = "option-b-native-soft";
            ch.fidelity   = Uir::Fidelity::exact();
            ch.rationale =
                infinite_top
                    ? "no `soft` threshold declared, so it constrains nothing"
                    : "threshold " + top_ + " exceeds the total cost " + sumcost
                          + ", so no assignment can reach it and it is vacuous";
            report_->addChoice(std::move(ch));

            // Option B, and here it is exact(): no assignment can reach T, so
            // the threshold constrains nothing. Native soft constraints carry
            // obligation 3 -- the cost is incurred exactly when the constraint
            // is violated, which is what assert-soft means -- without a
            // hand-built reification sum that would double-count.
            for (auto& c : constraints_) {
                if (appendPackedHardRow(c, packed.get())) {
                    decltype(c.sum){}.swap(c.sum);
                    continue;
                }
                H::Constraint hc;
                hc.loc = at(c.line);
                hc.formula = relation(c);
                if (!c.cost.empty()) {
                    hc.soft = true;
                    // The TEXT, not a double: costs are big integers by design
                    // and 10^23 through a double comes out as scientific
                    // notation, which is not a numeral.
                    hc.weight_text = numeral(c.cost);
                }
                model->constraints.push_back(hc);
                decltype(c.sum){}.swap(c.sum);
            }
            return model;
        }

        // Option A: a relaxation variable per remaining soft constraint, the
        // threshold as a hard constraint, and the cost sum as the objective.
        // Each indicator equals the violation truth value, so every source
        // assignment retains its exact cost before any optimization occurs.
        {
            Uir::EncodingChoice ch;
            ch.site       = file_;
            ch.unified_op = "wbo-threshold";
            ch.strategy   = "option-a-relaxation-vars";
            ch.fidelity = Uir::Fidelity::exact();
            ch.rationale =
                "threshold " + top_ + " does not exceed the total cost " + sumcost
                + ", so exact violation indicators retain each source assignment's "
                  "cost under the strict threshold; rows whose cost is at least "
                  "the threshold must hold";
            report_->addChoice(std::move(ch));
        }

        std::vector<H::ExprPtr> cost_terms;
        int nth = 0;
        for (auto& c : constraints_) {
            if (appendPackedHardRow(c, packed.get())) {
                decltype(c.sum){}.swap(c.sum);
                continue;
            }
            H::Constraint hc;
            hc.loc = at(c.line);
            // Costs are strictly positive, and admissibility is STRICTLY
            // total cost < T. Violating even one row with cost >= T is
            // therefore impossible. Requiring it directly removes redundant
            // relaxation domains and objective terms while preserving all
            // source assignments and their attainable minimum costs.
            if (c.cost.empty() || compareDecimal(c.cost, top_) >= 0) {
                hc.formula = relation(c);
                model->constraints.push_back(hc);
                decltype(c.sum){}.swap(c.sum);
                continue;
            }
            const std::string r = "!r" + std::to_string(nth++);
            H::VarDecl rd;
            rd.name = r;
            rd.sort = H::Sort::integer();
            rd.lower_bound = H::mkInt(0);
            rd.upper_bound = H::mkInt(1);
            rd.loc = at(c.line);
            model->decls.push_back(rd);

            // (r_i = 0) iff C_i: a satisfied row must cost zero too.
            // A one-sided relaxation preserves an optimum but admits extra
            // positive costs for satisfied rows in the full target relation.
            hc.formula = H::mkOp(
                H::Op::EQ,
                {H::mkOp(H::Op::EQ,
                    {H::mkIdent(r, H::Sort::integer(), at(c.line)),
                     H::mkInt(0, at(c.line))}, at(c.line)),
                 relation(c)}, at(c.line));
            model->constraints.push_back(hc);
            cost_terms.push_back(H::mkOp(
                H::Op::MUL, {H::mkInt(numeral(c.cost), at(c.line)),
                             H::mkIdent(r, H::Sort::integer(), at(c.line))},
                at(c.line)));
            decltype(c.sum){}.swap(c.sum);
        }
        H::ExprPtr total = cost_terms.empty()
                               ? H::mkInt(0, at(soft_line_))
                               : (cost_terms.size() == 1
                                      ? cost_terms.front()
                                      : H::mkOp(H::Op::ADD, cost_terms, at(soft_line_)));
        // Σ c_i r_i <= T - 1, because the format says STRICTLY less than T.
        // Writing `< T` would be the same thing here; `<= T - 1` is what the
        // document prescribes and keeps the integer nature explicit.
        H::Constraint thresh;
        thresh.loc = at(soft_line_);
        thresh.formula = H::mkOp(H::Op::LE,
                                 {total, H::mkInt(subDecimalOne(top_), at(soft_line_))},
                                 at(soft_line_));
        model->constraints.push_back(thresh);

        H::Objective o;
        o.kind = H::ObjKind::MINIMIZE;
        o.term = total;
        o.name = "cost";
        o.loc = at(soft_line_);
        model->objectives.push_back(o);
        (void)diags;
        return model;
    }

    // ---- unbounded decimal helpers ---------------------------------------
    // Costs and the top are big integers by design, so the vacuity check cannot
    // go through long long. Only non-negative values reach these.

    static std::string nonnegativeDecimal(const std::string& s) {
        const std::size_t start = s[0] == '+' ? 1 : 0;
        const std::size_t first = s.find_first_not_of('0', start);
        return first == std::string::npos ? "0" : s.substr(first);
    }

    static std::string addDecimal(const std::string& a, const std::string& b) {
        std::string out;
        int carry = 0;
        auto ia = static_cast<int>(a.size()), ib = static_cast<int>(b.size());
        while (ia > 0 || ib > 0 || carry) {
            int d = carry;
            if (ia > 0) { d += a[--ia] - '0'; }
            if (ib > 0) { d += b[--ib] - '0'; }
            out.push_back(static_cast<char>('0' + d % 10));
            carry = d / 10;
        }
        std::reverse(out.begin(), out.end());
        return out.empty() ? "0" : out;
    }

    static int compareDecimal(const std::string& a, const std::string& b) {
        const std::string x = a.substr(std::min(a.find_first_not_of('0'), a.size() - 1));
        const std::string y = b.substr(std::min(b.find_first_not_of('0'), b.size() - 1));
        if (x.size() != y.size()) { return x.size() < y.size() ? -1 : 1; }
        return x.compare(y) < 0 ? -1 : (x == y ? 0 : 1);
    }

    static std::string subDecimalOne(const std::string& a) {
        // T may be zero. Its predecessor is -1, making the nonnegative
        // violation-cost bound unsatisfiable, rather than wrapping to 9.
        if (compareDecimal(a, "0") == 0) { return "-1"; }
        std::string out = a;
        int i = static_cast<int>(out.size()) - 1;
        while (i >= 0) {
            if (out[i] != '0') { out[i]--; break; }
            out[i] = '9';
            --i;
        }
        const std::size_t nz = out.find_first_not_of('0');
        return nz == std::string::npos ? "0" : out.substr(nz);
    }

    std::istream& input_;
    std::string file_;
    Uir::TranslationReport* report_ = nullptr;   // set by parse(), never null after
    bool        strict_ = false;

    bool        wbo_ = false;
    bool        objective_seen_ = false;
    bool        maximise_ = false;
    std::string top_;                    // empty: infinity
    int         soft_line_ = 1;
    Constraint  objective_;
    std::vector<Constraint> constraints_;
    std::unordered_map<std::string, std::size_t> var_index_;
    std::unordered_map<std::string, std::size_t> coefficient_index_;
    std::vector<std::string> coefficients_;
    std::unordered_map<std::string, std::uint64_t> packed_number_index_;
    std::vector<std::string> ordered_;
    // Only immutable leaves/complements are shared. Relation roots still carry
    // each source statement's location, and caches never cross model parses.
    mutable std::unordered_map<std::size_t, H::ExprPtr> literals_;
    mutable std::vector<H::ExprPtr> symbols_;
    mutable std::unordered_map<std::string, H::ExprPtr> numbers_;
};

class OpbLanguage : public Language {
public:
    OpbLanguage() {
        // Constraints with all six ASCII relational operators, products, an
        // objective in both directions, WBO's soft header and soft
        // constraints, comments and header hints.
        coverage_.total = 6;
        coverage_.supported = 6;
    }

    std::string id() const override { return "opb"; }
    std::string displayName() const override { return "OPB / WBO"; }
    std::string version() const override { return "general and restricted"; }
    std::vector<std::string> extensions() const override { return {".opb", ".wbo"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) override {
        ParseOutcome out;
        std::unique_ptr<std::istream> input;
        if (!unit.inline_source.empty()) {
            input = std::make_unique<std::istringstream>(unit.inline_source);
        } else {
            std::error_code ec;
            if (std::filesystem::is_directory(unit.main_path, ec)) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "'" + unit.main_path + "' is a directory");
                return out;
            }
            auto file = std::make_unique<std::ifstream>(unit.main_path, std::ios::binary);
            if (!*file) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "cannot open '" + unit.main_path + "'");
                return out;
            }
            input = std::move(file);
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        const char* allocationStage = "source records";
        try {
            {
                OpbParser p(*input, name, opts.strict);
                out.model = p.parse(out.diagnostics, out.report, allocationStage);
            }
            if (out.model) {
                // The model owns its immutable HIR leaves. Discard source
                // records and parser lookup tables before constructing the
                // independent semantic contract.
                allocationStage = "source semantic contract";
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "opb", out.report.fidelity()));
            }
        } catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                                  std::string("opb frontend: memory allocation failed during ")
                                      + allocationStage);
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("opb frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkOpbLanguage() { return std::make_shared<OpbLanguage>(); }

} // namespace SOMTParser::Lang
