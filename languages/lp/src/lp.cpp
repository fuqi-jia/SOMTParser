/* -*- Source -*-
 * LP (CPLEX/Gurobi) frontend.
 *
 * The format is docs/languages/lp.md; its `implicit-constraints` block is the
 * specification this file implements, and each entry has a fixture in
 * languages/lp/instances.
 *
 * The first obligation is the one that matters and it is a single line of code:
 *
 *     **A variable with no `Bounds` entry is NON-NEGATIVE.**
 *
 * That is the LP format's semantics, from linear programming's own tradition,
 * and no file says it. Omitting it yields a strictly weaker model -- more
 * feasible points, so a better "optimum" -- that parses, type-checks,
 * round-trips, exits 0 and reports `exact()`. There is no Fidelity value for
 * "I translated a different problem".
 *
 * One obligation is now MOOT and the document should be read with that in mind:
 * lp.md §4.1's scaling rescue, and its requirement that the scale factor be
 * recorded, existed because the HIR had no real literal. `ExprKind::LIT_REAL`
 * landed on 2026-08-12 and is exact -- decimals and rationals both -- so no
 * scaling happens and there is no factor to record.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/lp.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <deque>
#include <filesystem>
#include <fstream>
#include <memory>
#include <iterator>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <gmpxx.h>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

struct VarClass {
    bool integer = false;
    bool binary = false;
    bool semicontinuous = false;
};

struct Bounds {
    std::string lo;          // decimal text; empty means "not written"
    std::string hi;
    bool        free = false;
    bool        lo_unbounded = false;
    bool        lo_set = false;
    bool        hi_set = false;
    bool        impossible = false;
};

struct Term {
    std::size_t coeff = 0;   // exact text pool index
    std::size_t var = 0;     // first-seen column ordinal
    /** The second factor of a quadratic monomial, sentinel for a linear term.
     *  `x ^ 2` and `x * x` both land here with var == var2, because LP spells
     *  a square both ways and they are the same monomial. */
    static constexpr std::size_t linear = std::numeric_limits<std::size_t>::max();
    std::size_t var2 = linear;
};

struct Row {
    std::vector<Term> lhs;
    std::vector<std::string> lhs_constants;
    std::string       op;    // <=, >=, =
    std::string       rhs;
    // Range form `lo <= expr <= hi`, which is one row and two inequalities.
    bool              range = false;
    std::string       range_lo;
    int               line = 0;
};

std::string lower(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return s;
}

bool isNumber(const std::string& s) {
    if (s.empty()) { return false; }
    std::size_t i = (s[0] == '+' || s[0] == '-') ? 1 : 0;
    if (i == s.size()) { return false; }
    bool dot = false, digit = false, exponent = false, exponent_digit = false;
    for (; i < s.size(); ++i) {
        const char c = s[i];
        if (std::isdigit(static_cast<unsigned char>(c))) {
            digit = true;
            if (exponent) { exponent_digit = true; }
        } else if (c == '.' && !dot && !exponent) {
            dot = true;
        } else if ((c == 'e' || c == 'E') && digit && !exponent) {
            exponent = true;
            if (i + 1 < s.size() && (s[i + 1] == '+' || s[i + 1] == '-')) { ++i; }
        } else {
            return false;
        }
    }
    if (!digit || (exponent && !exponent_digit)) { return false; }
    const std::size_t exponent_at = s.find_first_of("eE");
    if (exponent_at != std::string::npos) {
        std::size_t at = exponent_at + 1;
        if (at < s.size() && (s[at] == '+' || s[at] == '-')) { ++at; }
        unsigned value = 0;
        for (; at < s.size(); ++at) {
            const unsigned digit_value = static_cast<unsigned>(s[at] - '0');
            if (value > (100000U - digit_value) / 10U) { return false; }
            value = value * 10U + digit_value;
        }
    }
    return true;
}

bool isInfinity(const std::string& s) {
    const std::string word = lower(s);
    return word == "inf" || word == "+inf" || word == "-inf"
        || word == "infinity" || word == "+infinity" || word == "-infinity";
}

bool isNegativeInfinity(const std::string& s) {
    const std::string word = lower(s);
    return word == "-inf" || word == "-infinity";
}

bool isPositiveInfinity(const std::string& s) {
    const std::string word = lower(s);
    return word == "inf" || word == "+inf"
        || word == "infinity" || word == "+infinity";
}

std::string plainDecimal(const std::string& source) {
    const std::size_t exponent_at = source.find_first_of("eE");
    if (exponent_at == std::string::npos) {
        std::string out = source;
        if (!out.empty() && out[0] == '+') { out.erase(0, 1); }
        const std::size_t sign = !out.empty() && (out[0] == '+' || out[0] == '-') ? 1 : 0;
        const std::size_t dot = out.find('.');
        if (dot != std::string::npos) {
            if (dot == sign) { out.insert(sign, "0"); }
            if (!out.empty() && out.back() == '.') { out += '0'; }
        }
        return out;
    }
    std::string mantissa = source.substr(0, exponent_at);
    const std::string exponent_text = source.substr(exponent_at + 1);
    char* end = nullptr;
    const long exponent = std::strtol(exponent_text.c_str(), &end, 10);
    if (end == exponent_text.c_str() || *end != '\0' || exponent < -100000
        || exponent > 100000) {
        throw std::length_error("LP exponent exceeds the 100000-digit resource limit");
    }
    std::string sign;
    if (!mantissa.empty() && (mantissa[0] == '+' || mantissa[0] == '-')) {
        if (mantissa[0] == '-') { sign = "-"; }
        mantissa.erase(0, 1);
    }
    const std::size_t dot = mantissa.find('.');
    std::string digits = mantissa;
    long fractional = 0;
    if (dot != std::string::npos) {
        fractional = static_cast<long>(mantissa.size() - dot - 1);
        digits.erase(dot, 1);
    }
    const long shift = exponent - fractional;
    if (shift >= 0) {
        digits.append(static_cast<std::size_t>(shift), '0');
    } else {
        const std::size_t places = static_cast<std::size_t>(-shift);
        if (digits.size() <= places) {
            digits.insert(0, places - digits.size() + 1, '0');
        }
        digits.insert(digits.size() - places, ".");
    }
    return sign + digits;
}

std::string canonicalDecimal(const std::string& source) {
    std::string value = plainDecimal(source);
    const bool negative = !value.empty() && value.front() == '-';
    const std::size_t first = negative ? 1 : 0;
    const auto dot = value.find('.');
    const auto integer_end = dot == std::string::npos ? value.size() : dot;
    auto nonzero = value.find_first_not_of('0', first);
    if (nonzero == std::string::npos || nonzero >= integer_end) { nonzero = integer_end - 1; }
    std::string magnitude = value.substr(nonzero);
    if (dot != std::string::npos) {
        while (magnitude.back() == '0') { magnitude.pop_back(); }
        if (magnitude.back() == '.') { magnitude.pop_back(); }
    }
    return negative && magnitude != "0" ? "-" + magnitude : magnitude;
}

// RHS adjustment for LP's mathematical LHS constants. No floating-point
// conversion: both aligned mantissas are arbitrary-precision integers.
std::string subtractDecimal(const std::string& left, const std::string& right) {
    std::string a = canonicalDecimal(left), b = canonicalDecimal(right);
    const auto scale = [](const std::string& value) {
        const auto dot = value.find('.');
        return dot == std::string::npos ? std::size_t{0} : value.size() - dot - 1;
    };
    const auto a_scale = scale(a), b_scale = scale(b), places = std::max(a_scale, b_scale);
    const auto integer = [places](std::string text, std::size_t old_scale) {
        const auto dot = text.find('.');
        if (dot != std::string::npos) { text.erase(dot, 1); }
        text.append(places - old_scale, '0');
        return mpz_class(text, 10);
    };
    const mpz_class difference = integer(a, a_scale) - integer(b, b_scale);
    std::string value = difference.get_str();
    const bool negative = value.front() == '-';
    if (negative) { value.erase(0, 1); }
    if (places != 0) {
        if (value.size() <= places) { value.insert(0, places - value.size() + 1, '0'); }
        value.insert(value.size() - places, ".");
    }
    return canonicalDecimal((negative ? "-" : "") + value);
}

class LpParser {
public:
    LpParser(std::string_view source, std::istream* input, std::string file,
             bool numeric_names = false, bool inline_bounds = false,
             const char** allocation_stage = nullptr)
        : source_(source), input_(input), file_(std::move(file)),
          allocation_stage_(allocation_stage), numeric_names_(numeric_names),
          inline_bounds_(inline_bounds) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        report_ = &report;
        stage("input rows and coefficients");
        if (!read(diags)) { return nullptr; }
        stage("HIR construction");
        return build(diags);
    }

private:
    void stage(const char* name) {
        if (allocation_stage_) { *allocation_stage_ = name; }
    }

    bool nextLine(std::string& line) {
        if (input_) { return static_cast<bool>(std::getline(*input_, line)); }
        if (source_.empty()) { return false; }
        const auto end = source_.find('\n');
        const auto size = end == std::string_view::npos ? source_.size() : end;
        line.assign(source_.data(), size);
        source_.remove_prefix(size + (end == std::string_view::npos ? 0 : 1));
        return true;
    }

    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = line;
        l.column = 1;
        return l;
    }

    /** Tokenise, dropping `\` comments and splitting the punctuation LP glues to
     *  its operands (`x<=3` is three tokens). Section keywords are recognised on
     *  the joined lowercase text because several are two words. */
    bool read(Uir::Diagnostics& diags) {
        std::string raw;
        int lineno = 0;
        std::string section = "";
        std::vector<std::string> pending;
        int pending_line = 0;
        bool pending_has_relation = false;

        // An unfinished row can span thousands of physical lines. Inspect only
        // newly appended tokens; rescanning the accumulated prefix is quadratic.
        const auto appendPending = [&](std::vector<std::string>& tokens,
                                       std::size_t count) {
            if (!pending_has_relation) {
                for (std::size_t k = 0; k < count; ++k) {
                    if (!normaliseOp(tokens[k]).empty()) {
                        pending_has_relation = true;
                        break;
                    }
                }
            }
            pending.insert(pending.end(), std::make_move_iterator(tokens.begin()),
                           std::make_move_iterator(tokens.begin() + count));
        };

        const auto flush = [&](Uir::Diagnostics& d) {
            if (pending.empty()) { return true; }
            const bool ok = item(section, std::move(pending), pending_line, d);
            pending.clear();
            pending_has_relation = false;
            return ok;
        };

        while (nextLine(raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            const std::size_t bs = raw.find('\\');
            if (bs != std::string::npos) { raw.resize(bs); }
            std::vector<std::string> tok = split(raw);
            if (tok.empty()) { continue; }

            // Keywords used as labels remain labels (e.g. `end: x >= 3`).
            const std::string head = hasLabel(tok) ? std::string{} : sectionOf(tok);
            if (!head.empty()) {
                if (!flush(diags)) { return false; }
                section = head;
                if (head == "objective") {
                    maximise_ = (lower(tok[0])[1] == 'a');   // maximi[sz]e
                    objective_line_ = lineno;
                }
                if (head == "end") { break; }
                // The keyword may be followed by content on the same line.
                // keywordWords, always: several section keywords are two words
                // ("Subject To", "Such That", "Semi Continuous"), and consuming
                // one left the second as content -- so `To` was read as a
                // constraint with no relational operator.
                tok.erase(tok.begin(),
                          tok.begin() + static_cast<long>(keywordWords(tok)));
                if (tok.empty()) { continue; }
            }
            if (section == "objective") {
                // Gurobi accepts a constraints header after the objective on
                // the same physical line. Bounds/type headers still require
                // a line boundary; splitting every keyword would misread them.
                int bracket_depth = 0;
                for (std::size_t k = hasLabel(tok) ? 2 : 0; k < tok.size(); ++k) {
                    if (tok[k] == "[") { ++bracket_depth; }
                    if (tok[k] == "]") { --bracket_depth; }
                    const std::string word = lower(tok[k]);
                    const bool pair = k + 1 < tok.size()
                        && ((word == "subject" && lower(tok[k + 1]) == "to")
                            || (word == "such" && lower(tok[k + 1]) == "that"));
                    const bool single = word == "st" || word == "s.t.";
                    if (bracket_depth != 0 || (!pair && !single)
                        || (k + 1 < tok.size() && tok[k + 1] == ":")) { continue; }
                    if (pending.empty()) { pending_line = lineno; }
                    appendPending(tok, k);
                    if (!flush(diags)) { return false; }
                    tok.erase(tok.begin(), tok.begin() + k + (pair ? 2 : 1));
                    section = "constraints";
                    report_->addChoice({file_ + ":" + std::to_string(lineno),
                        "lp-section-boundary", "gurobi-inline-constraint-header",
                        Uir::Fidelity::exact(),
                        "A constraints keyword terminates the objective on the same "
                        "line, as in Gurobi's LP reader; labels are preserved"});
                    break;
                }
                if (tok.empty()) { continue; }
            }
            if (section.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "content before the objective section", at(lineno));
                return false;
            }
            if (inline_bounds_ && section == "constraints") {
                // Explicit reader extension: a bounds keyword AFTER a complete
                // row starts the bounds section on the same physical line.
                // A keyword in the LHS or a label remains a variable/label.
                if (!pending.empty() && (hasLabel(tok) || pending_has_relation)
                    && !flush(diags)) { return false; }
                bool relation_seen = false;
                int bracket_depth = 0;
                for (std::size_t k = hasLabel(tok) ? 2 : 0; k < tok.size(); ++k) {
                    if (tok[k] == "[") { ++bracket_depth; }
                    if (tok[k] == "]") { --bracket_depth; }
                    if (!normaliseOp(tok[k]).empty()) { relation_seen = true; }
                    const auto word = lower(tok[k]);
                    if (!relation_seen || bracket_depth != 0 || (word != "bounds" && word != "bound")
                        || (k + 1 < tok.size() && tok[k + 1] == ":")) { continue; }
                    if (pending.empty()) { pending_line = lineno; }
                    appendPending(tok, k);
                    if (!flush(diags)) { return false; }
                    tok.erase(tok.begin(), tok.begin() + k + 1);
                    section = "bounds";
                    report_->addChoice({file_ + ":" + std::to_string(lineno),
                        "lp-section-boundary", "explicit-inline-bounds",
                        Uir::Fidelity::exact(),
                        "inline_bounds=true: after a complete constraint, bounds starts a new "
                        "section on the same line; EOF terminates input without requiring End"});
                    break;
                }
                if (tok.empty()) { continue; }
            }
            // `[`, `]`, `^` and `*` are the quadratic section and are read
            // (§4.5). `->` is an indicator constraint and is not.
            if ((section == "objective" || section == "constraints")
                && (raw.find("->") != std::string::npos
                    || raw.find("<->") != std::string::npos)) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "indicator and logical LP constraints are not "
                            "supported yet",
                            at(lineno));
                return false;
            }
            // A new item starts at a `name:` label or, in the bounds-like
            // sections, at every line. Continuation lines otherwise.
            if (section == "objective" || section == "constraints") {
                if (!pending.empty()
                    && (hasLabel(tok)
                        || (section == "constraints" && pending_has_relation))) {
                    if (!flush(diags)) { return false; }
                }
                if (pending.empty()) { pending_line = lineno; }
                appendPending(tok, tok.size());
            } else {
                if (!flush(diags)) { return false; }
                pending_line = lineno;
                appendPending(tok, tok.size());
                if (!flush(diags)) { return false; }
            }
        }
        if (input_ && input_->fail() && !input_->eof()) {
            diags.error(ErrorCode::E_IO, "cannot read LP input", at(lineno));
            return false;
        }
        return flush(diags);
    }

    static bool hasLabel(const std::vector<std::string>& tok) {
        return tok.size() >= 2 && tok[1] == ":";
    }

    static std::size_t keywordWords(const std::vector<std::string>& tok) {
        // `Semi-Continuous` arrives as three tokens, because the tokeniser
        // splits on `-` so that `x - y` works. The keyword is matched on all
        // three rather than the hyphen being special-cased in split().
        if (tok.size() >= 3 && lower(tok[0]) == "semi" && tok[1] == "-"
            && lower(tok[2]) == "continuous") {
            return 3;
        }
        if (tok.size() >= 2) {
            const std::string two = lower(tok[0]) + " " + lower(tok[1]);
            if (two == "subject to" || two == "such that" || two == "semi continuous") {
                return 2;
            }
        }
        return 1;
    }

    static std::string sectionOf(const std::vector<std::string>& tok) {
        if (tok.empty()) { return ""; }
        const std::string one = lower(tok[0]);
        if (one == "maximize" || one == "maximise" || one == "minimize"
            || one == "minimise" || one == "max" || one == "min") { return "objective"; }
        if (one == "st" || one == "s.t.") { return "constraints"; }
        if (tok.size() >= 2 && ((one == "subject" && lower(tok[1]) == "to")
            || (one == "such" && lower(tok[1]) == "that"))) { return "constraints"; }
        if (one == "bounds" || one == "bound") { return "bounds"; }
        if (one == "general" || one == "generals" || one == "gen"
            || one == "integer" || one == "integers") { return "general"; }
        if (one == "binary" || one == "binaries" || one == "bin") { return "binary"; }
        if (one == "semi-continuous" || one == "semi") { return "semicont"; }
        if (one == "sos") { return "sos"; }
        if (one == "end") { return "end"; }
        return "";
    }

    static std::string normaliseOp(const std::string& op);

    static std::vector<std::string> split(const std::string& line) {
        std::vector<std::string> out;
        std::string cur;
        const auto push = [&] { if (!cur.empty()) { out.push_back(cur); cur.clear(); } };
        for (std::size_t i = 0; i < line.size(); ++i) {
            const char c = line[i];
            if (std::isspace(static_cast<unsigned char>(c))) { push(); continue; }
            if (c == '+' || c == '-') {
                if (!cur.empty() && (cur.back() == 'e' || cur.back() == 'E')
                    && i + 1 < line.size()
                    && std::isdigit(static_cast<unsigned char>(line[i + 1]))) {
                    cur += c;
                    continue;
                }
                push();
                out.push_back(std::string(1, c));
                continue;
            }
            if (c == ':') { push(); out.push_back(std::string(1, c)); continue; }
            // The quadratic punctuation. Without this `x1^2` is one token,
            // `x0*x1` is one token and `]/2` is one token, so the section
            // could only be detected by scanning the raw line -- which is how
            // it was refused before it was read.
            if (c == '[' || c == ']' || c == '^' || c == '*' || c == '/') {
                push();
                out.push_back(std::string(1, c));
                continue;
            }
            if (c == '<' || c == '>' || c == '=') {
                push();
                std::string op(1, c);
                if (i + 1 < line.size() && (line[i + 1] == '=' || line[i + 1] == '<'
                                            || line[i + 1] == '>')) {
                    op += line[++i];
                }
                out.push_back(op);
                continue;
            }
            cur += c;
        }
        push();
        // A `+`/`-` that opens a term or follows an operator or a label is the
        // SIGN of the number after it, not an addition. `-5 <= x - y <= 5` has
        // one of each, and splitting on `-` unconditionally left `-` as a token
        // where a number belonged -- so the range form stopped parsing and
        // `x >= -100` lost its minus.
        std::vector<std::string> merged;
        for (std::size_t k = 0; k < out.size(); ++k) {
            const bool sign = (out[k] == "+" || out[k] == "-");
            const bool numeric_next = k + 1 < out.size()
                && (isNumber(out[k + 1]) || isInfinity(out[k + 1]));
            const bool opens = merged.empty() || merged.back() == ":"
                            || !normaliseOp(merged.back()).empty();
            if (sign && numeric_next && opens) {
                // Keep an explicit leading `+`. terms() needs to distinguish
                // a positive coefficient at the start of a continuation line
                // from an unsigned coefficient following a completed term.
                merged.push_back(out[k] + out[k + 1]);
                ++k;
                continue;
            }
            merged.push_back(out[k]);
        }
        return merged;
    }

    bool item(const std::string& section, std::vector<std::string> tok, int line,
              Uir::Diagnostics& diags) {
        if (section.empty() || tok.empty()) { return true; }
        if (section == "objective") { return objectiveItem(std::move(tok), line, diags); }
        if (section == "constraints") { return rowItem(std::move(tok), line, diags); }
        if (section == "bounds") { return boundItem(std::move(tok), line, diags); }
        if (section == "general" || section == "binary" || section == "semicont") {
            for (const auto& v : tok) {
                if (v == ":") { continue; }
                touch(v);
                VarClass& kind = klass_[v];
                if (section == "general") { kind.integer = true; }
                else if (section == "binary") {
                    kind.integer = true;
                    kind.binary = true;
                } else {
                    kind.semicontinuous = true;
                }
            }
            return true;
        }
        if (section == "sos") {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "SOS sets are not supported yet", at(line));
            return false;
        }
        return true;
    }

    bool objectiveItem(std::vector<std::string> tok, int line, Uir::Diagnostics& diags) {
        for (const std::string& token : tok) {
            // The quadratic punctuation is read (§4.5); only the logical
            // operators are still refused here.
            if (token == "->" || token == "<->") {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "logical LP objectives are not supported yet",
                            at(line));
                return false;
            }
        }
        if (hasLabel(tok)) {
            objective_name_ = tok[0];
            tok.erase(tok.begin(), tok.begin() + 2);
        }
        objective_line_ = line;
        return terms(tok, 0, tok.size(), objective_, objective_constants_, line, diags);
    }

    bool rowItem(std::vector<std::string> tok, int line, Uir::Diagnostics& diags) {
        Row r;
        r.line = line;
        std::size_t i = 0;
        if (hasLabel(tok)) { i = 2; }

        // Find operators. Two of them means the range form `lo <= expr <= hi`.
        std::vector<std::size_t> ops;
        for (std::size_t k = i; k < tok.size(); ++k) {
            if (!normaliseOp(tok[k]).empty()) { ops.push_back(k); }
        }
        if (ops.empty()) {
            diags.error(ErrorCode::E_PARSE, "a constraint needs a relational operator",
                        at(line));
            return false;
        }
        if (ops.size() >= 2) {
            r.range = true;
            if (ops[0] != i + 1 || !isNumber(tok[i])) {
                diags.error(ErrorCode::E_PARSE,
                            "a range constraint is `lo <= expr <= hi`", at(line));
                return false;
            }
            r.range_lo = tok[i];
            if (ops[1] + 2 != tok.size() || !isNumber(tok[ops[1] + 1])) {
                diags.error(ErrorCode::E_PARSE,
                            "a range constraint is `lo <= expr <= hi`", at(line));
                return false;
            }
            r.rhs = tok[ops[1] + 1];
            r.op = "range";
            if (normaliseOp(tok[ops[0]]) != "<="
                || normaliseOp(tok[ops[1]]) != "<=") {
                diags.error(ErrorCode::E_PARSE,
                            "a range constraint is ordered `lo <= expr <= hi`", at(line));
                return false;
            }
            if (!terms(tok, ops[0] + 1, ops[1], r.lhs, r.lhs_constants,
                       line, diags)) {
                return false;
            }
            interpretLhsConstants(r);
            rows_.push_back(std::move(r));
            return true;
        }
        r.op = normaliseOp(tok[ops[0]]);
        if (ops[0] + 2 != tok.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "a constraint's right-hand side is a single number", at(line));
            return false;
        }
        r.rhs = tok[ops[0] + 1];
        if (!isNumber(r.rhs)) {
            diags.error(ErrorCode::E_PARSE, "'" + r.rhs + "' is not a number", at(line));
            return false;
        }
        if (!terms(tok, i, ops[0], r.lhs, r.lhs_constants, line, diags)) {
            return false;
        }
        interpretLhsConstants(r);
        rows_.push_back(std::move(r));
        return true;
    }

    void interpretLhsConstants(Row& row) {
        if (row.lhs_constants.empty()) { return; }
        report_->addChoice({file_ + ":" + std::to_string(row.line), "lp-lhs-number",
            numeric_names_ ? "numeric-variable-names" : "mathematical-lhs-constants",
            Uir::Fidelity::exact(), numeric_names_
                ? "Standalone LHS numerals name nonnegative variables, matching the "
                  "selected Gurobi reader convention"
                : "Standalone LHS numerals are mathematical constants in the selected "
                  "LP extension; Gurobi can instead read them as variable names"});
        if (!numeric_names_) { return; }
        for (std::string name : row.lhs_constants) {
            std::string sign = "1";
            if (!name.empty() && (name[0] == '+' || name[0] == '-')) {
                if (name[0] == '-') { sign = "-1"; }
                name.erase(0, 1);
            }
            row.lhs.push_back({numberId(sign), touch(name), Term::linear});
        }
        row.lhs_constants.clear();
    }

    /** `[+|-] [coeff] var` repeated. A coefficient is optional and defaults to
     *  1, which is what makes `x + y` legal. */
    bool terms(const std::vector<std::string>& tok, std::size_t from, std::size_t to,
               std::vector<Term>& out, std::vector<std::string>& constants,
               int line, Uir::Diagnostics& diags) {
        std::string sign = "+";
        bool need_separator = false;
        const auto signedNumber = [](std::string value, const std::string& sign_token) {
            bool negative = sign_token == "-";
            if (!value.empty() && (value[0] == '+' || value[0] == '-')) {
                if (value[0] == '-') { negative = !negative; }
                value.erase(0, 1);
            }
            return negative ? "-" + value : value;
        };
        const auto attached = [](const std::string& token, std::string& coefficient,
                                 std::string& variable) {
            for (std::size_t split = token.size(); split > 0; --split) {
                if (!isNumber(token.substr(0, split))) { continue; }
                if (split == token.size()) { return false; }
                const char first = token[split];
                if (std::isdigit(static_cast<unsigned char>(first)) || first == '.') {
                    continue;
                }
                coefficient = token.substr(0, split);
                variable = token.substr(split);
                return true;
            }
            return false;
        };
        for (std::size_t k = from; k < to; ++k) {
            const std::string& s = tok[k];
            if (s == "[") {
                // A quadratic section: `[ <quadratic terms> ]` optionally
                // followed by `/ <n>`.
                //
                // The divisor is WRITTEN, not implied. CPLEX LP conventionally
                // writes the objective's form over two -- `[ 2 x^2 ] / 2` --
                // while a quadratic CONSTRAINT carries no divisor at all
                // (`qcqp.lp` has both in one file). So it is read from the
                // text rather than assumed from the position, which is the
                // difference between this and the MPS sections, where the 1/2
                // is part of the format and never appears (`mps.md` §4.7).
                if (!quadraticSection(tok, k, to, sign, out, line, diags)) {
                    return false;
                }
                sign = "+";
                need_separator = true;
                continue;
            }
            if (s == "+" || s == "-") {
                sign = (sign == s) ? "+" : "-";
                need_separator = false;
                continue;
            }
            // A physical continuation line may begin with a signed
            // coefficient. split() keeps that sign attached because it has no
            // preceding token on the line, but in the joined LP expression it
            // is the separator for the next term (for example `x` followed by
            // a line beginning `-2 y`).
            const bool signed_continuation = need_separator && isNumber(s)
                && s.size() > 1 && (s[0] == '+' || s[0] == '-');
            if (need_separator && !signed_continuation) {
                diags.error(ErrorCode::E_PARSE,
                            "linear terms must be separated by '+' or '-'", at(line));
                return false;
            }
            if (isNumber(s)) {
                if (k + 1 < to && tok[k + 1] != "+" && tok[k + 1] != "-") {
                    if (isNumber(tok[k + 1])) {
                        diags.error(ErrorCode::E_PARSE, "two coefficients in a row",
                                    at(line));
                        return false;
                    }
                    Term term;
                    term.coeff = numberId(signedNumber(s, sign));
                    term.var = touch(tok[++k]);
                    out.push_back(std::move(term));
                } else {
                    constants.push_back(signedNumber(s, sign));
                }
                sign = "+";
                need_separator = true;
                continue;
            }
            std::string coefficient, variable;
            Term t;
            if (attached(s, coefficient, variable)) {
                t.coeff = numberId(signedNumber(coefficient, sign));
                t.var = touch(variable);
            } else {
                if (!s.empty()
                    && (std::isdigit(static_cast<unsigned char>(s.front()))
                        || s.front() == '.')) {
                    diags.error(ErrorCode::E_PARSE,
                                "malformed numeric coefficient '" + s + "'", at(line));
                    return false;
                }
                t.coeff = numberId(sign == "-" ? "-1" : "1");
                t.var = touch(s);
            }
            out.push_back(std::move(t));
            sign = "+";
            need_separator = true;
        }
        return true;
    }

    static std::string negate(const std::string& v) {
        if (v.empty()) { return v; }
        if (v[0] == '-') { return v.substr(1); }
        if (v[0] == '+') { return "-" + v.substr(1); }
        return "-" + v;
    }

    /** `a / b`, exactly, as a RATIONAL.
     *
     *  `Hir::mkReal` takes decimal *or* rational text, so the quotient stays
     *  exact for any divisor rather than only for the terminating ones. A
     *  decimal result would be wrong for `/ 3`, and rounding a coefficient is
     *  the one thing this frontend must not do to a model it claims to
     *  translate exactly.
     *
     *  Both operands are scaled to integers by moving the point, which is
     *  appending zeros rather than multiplying -- no big-integer arithmetic is
     *  needed to divide two decimal literals. */
    static std::string divideDecimal(const std::string& a, const std::string& b) {
        const auto parts = [](const std::string& v, bool& neg, std::string& digits,
                              std::size_t& frac) {
            std::string t = plainDecimal(v);
            neg = false;
            if (!t.empty() && (t[0] == '+' || t[0] == '-')) {
                neg = (t[0] == '-');
                t.erase(0, 1);
            }
            const std::size_t dot = t.find('.');
            frac = dot == std::string::npos ? 0 : t.size() - dot - 1;
            digits = dot == std::string::npos ? t : t.substr(0, dot) + t.substr(dot + 1);
            const std::size_t nz = digits.find_first_not_of('0');
            digits = nz == std::string::npos ? "0" : digits.substr(nz);
        };
        bool na = false, nb = false;
        std::string da, db;
        std::size_t fa = 0, fb = 0;
        parts(a, na, da, fa);
        parts(b, nb, db, fb);
        if (da == "0") { return "0"; }
        // a/b = (da * 10^-fa) / (db * 10^-fb) = (da * 10^fb) / (db * 10^fa)
        const std::string numerator = da + std::string(fb, '0');
        const std::string denominator = db + std::string(fa, '0');
        // Reduced, because `Hir::mkReal` takes an explicit rational verbatim
        // while it canonicalises a decimal. Without this `0.2 / 2` prints as
        // `(/ 2 20)` where the same model read from MPS prints `(/ 1 10)` --
        // the same number, and a difference that would defeat the
        // cross-format comparison in test_lp_quadratic.cpp for no reason.
        mpq_class exact(numerator + "/" + denominator);
        exact.canonicalize();
        if (na != nb) { exact = -exact; }
        return exact.get_str();
    }

    /** `[ q1 + q2 ... ]` with an optional `/ n`, from the opening bracket.
     *
     *  Leaves @p k on the last token consumed. Each monomial is `[coeff] a ^ 2`
     *  or `[coeff] a * b`; a linear term inside the brackets is refused by
     *  name rather than silently accepted, because the bracket is what tells a
     *  reader the section is quadratic and a linear term there is more likely
     *  a typo than an intention. */
    bool quadraticSection(const std::vector<std::string>& tok, std::size_t& k,
                          std::size_t to, const std::string& outer_sign,
                          std::vector<Term>& out, int line,
                          Uir::Diagnostics& diags) {
        std::vector<Term> terms;
        std::string sign = outer_sign;
        ++k;                                     // past '['
        bool closed = false;
        for (; k < to; ++k) {
            const std::string& s = tok[k];
            if (s == "]") { closed = true; break; }
            if (s == "+" || s == "-") {
                sign = (sign == s) ? "+" : "-";
                continue;
            }
            std::string coefficient = "1";
            if (isNumber(s)) {
                coefficient = s;
                if (++k >= to) { break; }
            }
            const std::string first = tok[k];
            if (first == "]" || first == "+" || first == "-" || first == "*"
                || first == "^" || first == "/" || first == "[") {
                // Punctuation where a variable belongs. `/` in particular is
                // how an unterminated bracket presents -- `[ 2 x^2 / 2` runs
                // past the missing `]` into the divisor -- so this must not
                // fall through to the linear-term message below, which would
                // name a construct the author did not write.
                diags.error(ErrorCode::E_PARSE,
                            "expected a variable in the quadratic section, found '"
                                + first + "'", at(line));
                return false;
            }
            Term t;
            t.var = touch(first);
            if (k + 2 < to && tok[k + 1] == "^") {
                if (tok[k + 2] != "2") {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "only '^2' is a quadratic power; '^" + tok[k + 2]
                                    + "' is a higher degree this subset does not read",
                                at(line));
                    return false;
                }
                t.var2 = t.var;
                k += 2;
            } else if (k + 1 < to && tok[k + 1] == "*") {
                if (k + 2 >= to) {
                    diags.error(ErrorCode::E_PARSE, "'*' with no second factor",
                                at(line));
                    return false;
                }
                t.var2 = touch(tok[k + 2]);
                k += 2;
            } else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "'" + first + "' is a linear term inside a quadratic "
                            "section; the brackets are what say the section is "
                            "quadratic, so a linear term in them is refused rather "
                            "than read as one outside",
                            at(line));
                return false;
            }
            t.coeff = numberId(sign == "-" ? negate(coefficient) : coefficient);
            terms.push_back(std::move(t));
            sign = "+";
        }
        if (!closed) {
            diags.error(ErrorCode::E_PARSE, "unterminated quadratic section: no ']'",
                        at(line));
            return false;
        }
        // The divisor, when written.
        if (k + 2 < to && tok[k + 1] == "/") {
            const std::string& d = tok[k + 2];
            if (!isNumber(d)) {
                diags.error(ErrorCode::E_PARSE,
                            "a quadratic section's divisor must be a number, not '"
                                + d + "'", at(line));
                return false;
            }
            if (plainDecimal(d) == "0") {
                diags.error(ErrorCode::E_PARSE,
                            "a quadratic section divided by zero", at(line));
                return false;
            }
            for (Term& t : terms) {
                t.coeff = numberId(divideDecimal(*number_text_[t.coeff], d));
            }
            k += 2;
        }
        for (Term& t : terms) { out.push_back(std::move(t)); }
        return true;
    }

    bool boundItem(std::vector<std::string> tok, int line, Uir::Diagnostics& diags) {
        // `x free`, `l <= x <= u`, `x >= l`, `x <= u`, `x = v`.
        // A section header precedes these tokens in the original physical
        // line, so split() cannot yet recognize the first endpoint's sign.
        // Normalize only after identifying the bounds section: a variable
        // named `bounds` in an ordinary expression must remain unchanged.
        if (tok.size() >= 2 && (tok[0] == "+" || tok[0] == "-")
            && !tok[1].empty() && tok[1][0] != '+' && tok[1][0] != '-'
            && (isNumber(tok[1]) || isInfinity(tok[1]))) {
            tok[1].insert(0, tok[0]);
            tok.erase(tok.begin());
        }
        if (tok.size() == 2 && lower(tok[1]) == "free") {
            touch(tok[0]);
            Bounds& bound = bounds_[tok[0]];
            bound.free = true;
            bound.lo_unbounded = true;
            bound.lo_set = false;
            bound.hi_set = false;
            return true;
        }
        const auto setLower = [&](Bounds& bound, const std::string& value) {
            bound.free = false;
            if (isNegativeInfinity(value)) {
                bound.lo_set = false;
                bound.lo_unbounded = true;
                return true;
            }
            if (isPositiveInfinity(value)) {
                bound.impossible = true;
                return true;
            }
            if (!isNumber(value)) { return false; }
            bound.lo = value;
            bound.lo_set = true;
            bound.lo_unbounded = false;
            return true;
        };
        const auto setUpper = [&](Bounds& bound, const std::string& value) {
            bound.free = false;
            if (isPositiveInfinity(value)) {
                bound.hi_set = false;
                return true;
            }
            if (isNegativeInfinity(value)) {
                bound.impossible = true;
                return true;
            }
            if (!isNumber(value)) { return false; }
            bound.hi = value;
            bound.hi_set = true;
            return true;
        };
        std::vector<std::size_t> ops;
        for (std::size_t k = 0; k < tok.size(); ++k) {
            if (!normaliseOp(tok[k]).empty()) { ops.push_back(k); }
        }
        if (ops.size() == 2 && ops[0] == 1 && ops[1] == 3 && tok.size() == 5) {
            if (normaliseOp(tok[1]) != "<=" || normaliseOp(tok[3]) != "<=") {
                diags.error(ErrorCode::E_PARSE,
                            "a two-sided bound is ordered `lo <= x <= hi`", at(line));
                return false;
            }
            touch(tok[2]);
            Bounds& b = bounds_[tok[2]];
            if (!setLower(b, tok[0]) || !setUpper(b, tok[4])) {
                diags.error(ErrorCode::E_PARSE,
                            "a bound endpoint must be a number or signed infinity", at(line));
                return false;
            }
            return true;
        }
        if (ops.size() == 1 && ops[0] == 1 && tok.size() == 3) {
            const std::string op = normaliseOp(tok[1]);
            const bool left_value = isNumber(tok[0]) || isInfinity(tok[0]);
            const bool right_value = isNumber(tok[2]) || isInfinity(tok[2]);
            if (left_value == right_value) {
                diags.error(ErrorCode::E_PARSE,
                            "a one-sided bound needs one variable and one endpoint", at(line));
                return false;
            }
            const std::string& variable = left_value ? tok[2] : tok[0];
            const std::string& value = left_value ? tok[0] : tok[2];
            touch(variable);
            Bounds& bound = bounds_[variable];
            bool ok = false;
            if (op == "=") {
                ok = setLower(bound, value) && setUpper(bound, value);
            } else if ((!left_value && op == ">=") || (left_value && op == "<=")) {
                ok = setLower(bound, value);
            } else {
                ok = setUpper(bound, value);
            }
            if (!ok) {
                diags.error(ErrorCode::E_PARSE,
                            "a bound endpoint must be a number or signed infinity", at(line));
                return false;
            }
            return true;
        }
        // Named rather than dismissed. A BOUNDS entry is `x >= 3`, `x <= 5`,
        // `3 <= x <= 5`, `x = 4` or `x free`, and saying which of those the
        // line failed to be is the difference between a reader fixing it and a
        // reader guessing. "unrecognised bound" also fell below the corpus
        // property's minimum message length, which is what surfaced it.
        diags.error(ErrorCode::E_PARSE,
                    "unrecognised bound: a BOUNDS entry is `x >= lo`, `x <= hi`, "
                    "`lo <= x <= hi`, `x = v` or `x free`, and this line matches "
                    "none of them",
                    at(line));
        return false;
    }

    std::size_t touch(const std::string& v) {
        const auto inserted = var_index_.emplace(v, var_index_.size());
        if (inserted.second) { order_.push_back(v); }
        return inserted.first->second;
    }

    std::size_t numberId(const std::string& value) {
        const auto inserted = number_index_.emplace(value, number_index_.size());
        if (inserted.second) {
            // unordered_map rehash does not invalidate references to keys.
            number_text_.push_back(&inserted.first->first);
        }
        return inserted.first->second;
    }

    // ---- construction ----------------------------------------------------

    H::Sort sortOf(const std::string& v) const {
        const auto it = klass_.find(v);
        if (it == klass_.end()) { return H::Sort::real(); }
        return it->second.integer ? H::Sort::integer() : H::Sort::real();
    }

    H::ExprPtr num(const std::string& text, int line) const {
        // Every LP number is a decimal, hence a rational, and LIT_REAL keeps it
        // exactly. lp.md §4.1's scaling rescue existed only because there was no
        // real literal; there is one now, so nothing is scaled and there is no
        // factor to record.
        const auto inserted = numbers_.emplace(text, H::ExprPtr{});
        if (inserted.second) { inserted.first->second = H::mkReal(plainDecimal(text), at(line)); }
        return inserted.first->second;
    }

    H::ExprPtr symbol(std::size_t column, int line) const {
        auto& value = symbols_[column];
        if (!value) { value = H::mkIdent(order_[column], sortOf(order_[column]), at(line)); }
        return value;
    }

    H::ExprPtr sumOf(const std::vector<Term>& terms,
                     const std::vector<std::string>& constants, int line) const {
        std::vector<H::ExprPtr> addends;
        addends.reserve(terms.size() + constants.size());
        for (const auto& t : terms) {
            H::ExprPtr factor = symbol(t.var, line);
            if (t.var2 != Term::linear) {
                // A quadratic monomial. `x ^ 2` and `x * x` both arrive with
                // var == var2 and produce the same term, because LP spells a
                // square both ways and they mean one thing.
                factor = H::mkOp(
                    H::Op::MUL,
                    {factor, symbol(t.var2, line)},
                    at(line));
            }
            addends.push_back(H::mkOp(
                H::Op::MUL, {num(*number_text_[t.coeff], line), std::move(factor)}, at(line)));
        }
        for (const std::string& constant : constants) {
            addends.push_back(num(constant, line));
        }
        if (addends.empty()) { return num("0", line); }
        if (addends.size() == 1) { return addends.front(); }
        return H::mkOp(H::Op::ADD, std::move(addends), at(line));
    }

    static bool linear(const std::vector<Term>& terms) {
        return std::all_of(terms.begin(), terms.end(),
                           [](const Term& term) { return term.var2 == Term::linear; });
    }

    std::size_t packedNumber(const std::string& text) {
        return packed_numbers_.emplace(canonicalDecimal(text), packed_numbers_.size()).first->second;
    }

    void appendPackedRow(H::PackedLinearRows& data, const std::vector<Term>& terms,
                         const std::vector<std::string>& constants, int line,
                         H::LinearRowRelation relation, const std::string& rhs,
                         const std::string& upper = "0", std::size_t auxiliary = Term::linear) {
        constexpr std::size_t batch_rows = 4096;
        if (data.batches.empty() || data.batches.back().rows.size() == batch_rows
            || auxiliary != Term::linear) {
            data.batches.emplace_back();
            auto& batch = data.batches.back();
            batch.source_file = file_;
            batch.rows.reserve(batch_rows);
            std::size_t count = terms.size();
            if (count > batch.terms.max_size()) {
                throw std::length_error("packed LP matrix row is too large");
            }
            const auto add = [&](std::size_t size) {
                if (size > batch.terms.max_size() - count) {
                    throw std::length_error("packed LP matrix batch is too large");
                }
                count += size;
            };
            if (auxiliary != Term::linear) { add(1); }
            else {
                std::size_t remaining = batch_rows - 1;
                // The current row has been popped already. Only linear rows
                // consume batch positions; quadratic rows retain ordinary HIR.
                for (const Row& row : rows_) {
                    if (!linear(row.lhs)) { continue; }
                    add(row.lhs.size());
                    if (--remaining == 0) { break; }
                }
            }
            batch.terms.reserve(count);
        }
        auto& batch = data.batches.back();
        H::PackedLinearRow row;
        row.begin = batch.terms.size();
        for (const Term& term : terms) {
            batch.terms.push_back({term.var, packedNumber(*number_text_[term.coeff])});
        }
        if (auxiliary != Term::linear) { batch.terms.push_back({auxiliary, packedNumber("-1")}); }
        row.end = batch.terms.size();
        std::string endpoint = rhs, high = upper;
        for (const auto& constant : constants) {
            endpoint = subtractDecimal(endpoint, constant);
            if (relation == H::LinearRowRelation::RANGE) { high = subtractDecimal(high, constant); }
        }
        row.rhs = packedNumber(endpoint);
        if (relation == H::LinearRowRelation::RANGE) { row.upper = packedNumber(high); }
        row.relation = relation;
        row.source_line = static_cast<std::uint32_t>(line);
        batch.rows.push_back(row);
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags) {
        auto model = std::make_shared<H::ConstraintModel>();
        constexpr std::size_t packed_threshold = 65536;
        std::size_t linear_rows = 0, linear_terms = 0;
        for (const Row& row : rows_) {
            if (!linear(row.lhs)) { continue; }
            linear_rows += linear_rows < packed_threshold;
            linear_terms += std::min(row.lhs.size(), packed_threshold - linear_terms);
        }
        const bool packed_objective = objective_.size() >= packed_threshold && linear(objective_);
        std::shared_ptr<H::PackedLinearRows> packed;
        if (linear_rows == packed_threshold || linear_terms == packed_threshold || packed_objective) {
            packed = std::make_shared<H::PackedLinearRows>();
        }
        symbols_.resize(order_.size());
        if (packed_objective && order_.size() == model->decls.max_size()) {
            throw std::length_error("packed LP objective has no declaration slot");
        }
        model->decls.reserve(order_.size() + static_cast<std::size_t>(packed_objective));
        H::ExprPtr binary_zero, binary_one;
        stage("HIR declarations and bounds");

        for (const auto& v : order_) {
            H::VarDecl d;
            d.name = v;
            d.sort = sortOf(v);
            d.loc = at(1);
            const auto bit = bounds_.find(v);
            const auto kit = klass_.find(v);
            const bool binary = kit != klass_.end() && kit->second.binary;
            const bool semi = kit != klass_.end() && kit->second.semicontinuous;

            if (binary) {
                // Binary contributes the intrinsic {0,1} carrier. Explicit
                // Bounds remain additional restrictions and are emitted below;
                // dropping `b = 0` would incorrectly restore the value 1.
                if (!binary_zero) { binary_zero = H::mkInt(0, at(1)); }
                if (!binary_one) { binary_one = H::mkInt(1, at(1)); }
                d.lower_bound = binary_zero;
                d.upper_bound = binary_one;
            } else if (semi) {
                // §2.3, §4.4: a semi-continuous variable is `x = 0 OR l <= x <= u`
                // -- a DISJUNCTION, not the interval [0, u]. The interval reading
                // admits every value between 0 and l, which is precisely the
                // range the modeller excluded. The bounds are therefore NOT
                // written on the declaration; the disjunction is emitted below.
            } else {
                // **The obligation.** A variable with no Bounds entry is
                // non-negative: that is the format's semantics and no file says
                // it. Omitting it yields a strictly weaker model -- more
                // feasible points, so a better "optimum" -- that parses,
                // type-checks, round-trips and reports exact().
                if (bit != bounds_.end() && bit->second.lo_set) {
                    d.lower_bound = num(bit->second.lo, 1);
                } else if (bit == bounds_.end() || !bit->second.lo_unbounded) {
                    d.lower_bound = num("0", 1);
                }
                if (bit != bounds_.end() && bit->second.hi_set) {
                    d.upper_bound = num(bit->second.hi, 1);
                }
            }
            model->decls.push_back(d);
        }

        // Bounds on binary variables intersect the intrinsic {0,1} carrier.
        // CPLEX warns about alternative bounds but still enforces both pieces.
        for (const auto& v : order_) {
            const auto kind = klass_.find(v);
            const auto bound = bounds_.find(v);
            if (bound != bounds_.end() && bound->second.impossible) {
                H::Constraint contradiction;
                contradiction.loc = at(1);
                contradiction.formula = H::mkBool(false, at(1));
                model->constraints.push_back(std::move(contradiction));
            }
            if (kind == klass_.end() || !kind->second.binary
                || bound == bounds_.end()) {
                continue;
            }
            H::ExprPtr variable = H::mkIdent(v, H::Sort::integer(), at(1));
            if (bound->second.lo_set) {
                H::Constraint lower;
                lower.loc = at(1);
                lower.formula = H::mkOp(
                    H::Op::GE, {variable, num(bound->second.lo, 1)}, at(1));
                model->constraints.push_back(std::move(lower));
            }
            if (bound->second.hi_set) {
                H::Constraint upper;
                upper.loc = at(1);
                upper.formula = H::mkOp(
                    H::Op::LE, {variable, num(bound->second.hi, 1)}, at(1));
                model->constraints.push_back(std::move(upper));
            }
        }

        // Semi-continuous disjunctions.
        for (const auto& [v, k] : klass_) {
            if (!k.semicontinuous) { continue; }
            const auto bit = bounds_.find(v);
            H::ExprPtr x = H::mkIdent(v, sortOf(v), at(1));
            std::vector<H::ExprPtr> inRange;
            if (bit != bounds_.end() && bit->second.lo_set) {
                inRange.push_back(H::mkOp(
                    H::Op::LE, {num(bit->second.lo, 1), x}, at(1)));
            } else if (bit == bounds_.end() || !bit->second.lo_unbounded) {
                inRange.push_back(H::mkOp(H::Op::LE, {num("0", 1), x}, at(1)));
            }
            if (bit != bounds_.end() && bit->second.hi_set) {
                inRange.push_back(H::mkOp(H::Op::LE, {x, num(bit->second.hi, 1)}, at(1)));
            }
            H::ExprPtr band = inRange.empty()
                ? H::mkBool(true, at(1))
                : inRange.size() == 1
                    ? inRange.front()
                    : H::mkOp(H::Op::AND, std::move(inRange), at(1));
            H::Constraint c;
            c.loc = at(1);
            c.formula = H::mkOp(H::Op::OR,
                                {H::mkOp(H::Op::EQ, {x, num("0", 1)}, at(1)), band},
                                at(1));
            model->constraints.push_back(c);
        }

        stage("objectives and matrix rows");
        while (!rows_.empty()) {
            Row r = std::move(rows_.front());
            rows_.pop_front();
            if (packed && linear(r.lhs)) {
                const auto relation = r.range ? H::LinearRowRelation::RANGE
                    : r.op == "<=" ? H::LinearRowRelation::LE
                    : r.op == ">=" ? H::LinearRowRelation::GE : H::LinearRowRelation::EQ;
                appendPackedRow(*packed, r.lhs, r.lhs_constants, r.line, relation,
                                r.range ? r.range_lo : r.rhs, r.rhs);
                continue;
            }
            H::ExprPtr lhs = sumOf(r.lhs, r.lhs_constants, r.line);
            H::Constraint c;
            c.loc = at(r.line);
            if (r.range) {
                // One row, two inequalities, and both inclusive.
                c.formula = H::mkOp(
                    H::Op::AND,
                    {H::mkOp(H::Op::LE, {num(r.range_lo, r.line), lhs}, at(r.line)),
                     H::mkOp(H::Op::LE, {lhs, num(r.rhs, r.line)}, at(r.line))},
                    at(r.line));
            } else if (r.op == "<=") {
                c.formula = H::mkOp(H::Op::LE, {lhs, num(r.rhs, r.line)}, at(r.line));
            } else if (r.op == ">=") {
                c.formula = H::mkOp(H::Op::GE, {lhs, num(r.rhs, r.line)}, at(r.line));
            } else {
                c.formula = H::mkOp(H::Op::EQ, {lhs, num(r.rhs, r.line)}, at(r.line));
            }
            model->constraints.push_back(c);
        }

        // A source objective label (or the default label) can also name a
        // column. Keep every source variable intact and give the target
        // objective a fresh identifier in HIR's shared namespace.
        std::string objective_name = objective_name_.empty() ? "obj" : objective_name_;
        const std::string objective_base = objective_name + "__objective";
        std::size_t suffix = 0;
        while (var_index_.count(objective_name) != 0) {
            objective_name = objective_base
                + (suffix == 0 ? std::string() : std::to_string(suffix));
            ++suffix;
        }
        if (!objective_.empty()) {
            H::Objective o;
            o.kind = maximise_ ? H::ObjKind::MAXIMIZE : H::ObjKind::MINIMIZE;
            if (packed_objective) {
                const std::string stem = "__somt_lp_objective_value";
                std::string name = stem;
                std::size_t suffix = 0;
                while (var_index_.count(name) || var_index_.count("|" + name + "|")
                       || name == objective_name) { name = stem + std::to_string(++suffix); }
                H::VarDecl value;
                value.name = name;
                value.sort = H::Sort::real();
                value.auxiliary = true;
                value.loc = at(objective_line_);
                const auto column = model->decls.size();
                model->decls.push_back(std::move(value));
                // sum + offset = value, with no artificial domain bound on
                // the unique Real value, including when all columns are Int.
                appendPackedRow(*packed, objective_, objective_constants_, objective_line_,
                                H::LinearRowRelation::EQ, "0", "0", column);
                o.term = H::mkIdent(name, H::Sort::real(), at(objective_line_));
            } else {
                o.term = sumOf(objective_, objective_constants_, objective_line_);
            }
            o.name = objective_name;
            o.loc = at(objective_line_);
            model->objectives.push_back(o);
        } else if (!objective_constants_.empty()) {
            H::Objective o;
            o.kind = maximise_ ? H::ObjKind::MAXIMIZE : H::ObjKind::MINIMIZE;
            o.term = sumOf({}, objective_constants_, objective_line_);
            o.name = objective_name;
            o.loc = at(objective_line_);
            model->objectives.push_back(std::move(o));
        }
        if (packed) {
            packed->numbers.resize(packed_numbers_.size());
            while (!packed_numbers_.empty()) {
                auto entry = packed_numbers_.extract(packed_numbers_.begin());
                packed->numbers[entry.mapped()] = std::move(entry.key());
            }
            model->packed_linear_rows = std::move(packed);
            report_->addChoice({file_, "LP linear rows", "packed-linear-rows", Uir::Fidelity::exact(),
                "All linear terms, duplicate entries, constants, inclusive ranges and objective "
                "values are retained exactly in the typed packed matrix; quadratic rows remain HIR"});
        }
        (void)diags;
        return model;
    }

    std::string_view source_;
    std::istream* input_ = nullptr;
    std::string file_;
    const char** allocation_stage_ = nullptr;
    Uir::TranslationReport* report_ = nullptr;
    bool numeric_names_ = false;
    bool inline_bounds_ = false;

    bool        maximise_ = false;
    int         objective_line_ = 1;
    std::string objective_name_;
    std::vector<Term> objective_;
    std::vector<std::string> objective_constants_;
    std::deque<Row> rows_;
    std::vector<std::string> order_;
    std::unordered_map<std::string, std::size_t> var_index_;
    std::unordered_map<std::string, Bounds>   bounds_;
    std::unordered_map<std::string, VarClass> klass_;
    std::unordered_map<std::string, std::size_t> number_index_;
    std::vector<const std::string*> number_text_;
    mutable std::unordered_map<std::string, H::ExprPtr> numbers_;
    mutable std::vector<H::ExprPtr> symbols_;
    std::unordered_map<std::string, std::size_t> packed_numbers_;
};

/** §2.4: `<` and `<=` mean the SAME THING. Linear programming has no strict
 *  inequality, so emitting Op::LT for `<` is a different model -- one whose
 *  feasible region excludes its own boundary, which is exactly where an LP
 *  optimum usually sits. */
std::string LpParser::normaliseOp(const std::string& op) {
    if (op == "<" || op == "<=" || op == "=<") { return "<="; }
    if (op == ">" || op == ">=" || op == "=>") { return ">="; }
    if (op == "=") { return "="; }
    return "";
}

class LpLanguage : public Language {
public:
    LpLanguage() {
        // Linear objective, linear/range constraints, Bounds, General/Integer,
        // Binary, and Semi-Continuous/Semi-Integer are exact. Keep source
        // features that require a different grammar/encoding visible rather
        // than counting their enclosing section as wholly supported.
        // Quadratic objectives AND constraints landed 2026-09-20 (§4.5):
        // the bracketed form with its written divisor, `^2` and `a * b`.
        coverage_.total = 9;
        coverage_.supported = 7;
        coverage_.missing = {
            "indicator constraints",
            "SOS1/SOS2",
        };
    }

    std::string id() const override { return "lp"; }
    std::string displayName() const override { return "LP (CPLEX/Gurobi)"; }
    std::string version() const override { return "cplex-lp"; }
    std::vector<std::string> extensions() const override { return {".lp"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& options) override {
        ParseOutcome out;
        const auto mode = options.options.find("lhs_numbers");
        if (mode != options.options.end() && mode->second != "constants" && mode->second != "variables") {
            out.diagnostics.error(ErrorCode::E_PARSE, "lhs_numbers must be constants or variables");
            return out;
        }
        const bool numeric_names = mode != options.options.end() && mode->second == "variables";
        const auto layout = options.options.find("inline_bounds");
        if (layout != options.options.end() && layout->second != "true" && layout->second != "false") {
            out.diagnostics.error(ErrorCode::E_PARSE, "inline_bounds must be true or false");
            return out;
        }
        const bool inline_bounds = layout != options.options.end() && layout->second == "true";
        std::ifstream input;
        if (unit.inline_source.empty()) {
            std::error_code ec;
            if (std::filesystem::is_directory(unit.main_path, ec)) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "'" + unit.main_path + "' is a directory");
                return out;
            }
            input.open(unit.main_path, std::ios::binary);
            if (!input) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "cannot open '" + unit.main_path + "'");
                return out;
            }
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        const char* allocation_stage = "parser setup";
        try {
            {
                // Inline input is borrowed for this call; file input is read
                // line by line. Neither path needs whole-source copies.
                LpParser p(unit.inline_source, input.is_open() ? &input : nullptr,
                           name, numeric_names, inline_bounds, &allocation_stage);
                out.model = p.parse(out.diagnostics, out.report);
            }
            // Parsed matrix/token caches must be gone before the semantic
            // contract captures the completed HIR and its source signature.
            if (out.model) {
                allocation_stage = "source semantic contract";
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "lp", out.report.fidelity()));
            }
        } catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                                  std::string("lp frontend: memory allocation failed during ")
                                      + allocation_stage);
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("lp frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkLpLanguage() { return std::make_shared<LpLanguage>(); }

} // namespace SOMTParser::Lang
