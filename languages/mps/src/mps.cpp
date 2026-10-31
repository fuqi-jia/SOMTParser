/* -*- Source -*-
 * MPS frontend.
 *
 * The format is docs/languages/mps.md; its `implicit-constraints` block is the
 * specification this file implements, and each entry has a fixture in
 * languages/mps/instances.
 *
 * Three of the six obligations are about things that are MARKERS rather than
 * data -- state a reader carries between lines, invisible in any single one:
 *
 *   * `MARKER 'INTORG'` / `'INTEND'` bracket the integer columns. Ignoring them
 *     makes every variable continuous, which is the LP RELAXATION of the model:
 *     complete = true, sound = false, and a strictly easier problem.
 *   * The FIRST `N` row is the objective; later ones are free rows constraining
 *     nothing. Treating a second `N` row as a constraint invents one.
 *   * A `RANGES` entry on an `E` row stops it being an equality, and which side
 *     the interval extends to depends on the SIGN of the range value.
 *
 * And one is a genuine divergence between readers rather than a rule: `BOUNDS UP`
 * with a negative value. §4.2 verified that CPLEX resets the lower bound to
 * -infinity only when the upper bound is strictly less than 0, and deliberately
 * differs from other readers at exactly `UP 0`, where it keeps the lower bound
 * at 0 and fixes the variable. That is a third behaviour, so the rule chosen
 * here is stated and warned per instance rather than assumed.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/mps.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <deque>
#include <filesystem>
#include <fstream>
#include <memory>
#include <new>
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

struct Row {
    char        type = 'N';          // N, L, G, E
    // Only N rows need a name after input validation. Other row names are
    // already owned by row_index_ while records are read.
    std::unique_ptr<std::string> name;
    // Column names and exact coefficient spellings are interned once by the
    // parser. Native-size indices avoid narrowing a large sparse matrix.
    std::vector<std::pair<std::size_t, std::size_t>> terms;   // (column id, coefficient id)
    const std::string* rhs = nullptr;
    bool        rhs_set = false;
    bool        has_range = false;
    const std::string* range = nullptr;
    int         line = 0;

    const std::string& rhsValue() const {
        static const std::string zero = "0";
        return rhs ? *rhs : zero;
    }
};

/** One quadratic monomial's accumulated coefficient.
 *
 *  Keyed by the UNORDERED pair, because the three sections spell the same
 *  monomial differently and a model may use more than one spelling for it:
 *  `QUADOBJ` gives a triangle, `QMATRIX` gives the full symmetric matrix, and
 *  a file may repeat an entry (HiGHS's `2821-duplicate` and `2821-summation`
 *  exist precisely to pin that repeats SUM rather than overwrite). Keying by
 *  the ordered pair would make `X1 X2` and `X2 X1` two monomials, which is a
 *  quietly different objective. */
struct QuadTerm {
    std::string a;          // column, in first-seen order
    std::string b;
    std::string coeff = "0";
    int         line = 0;
};

struct Col {
    std::string name;
    bool        integer = false;
    bool        marker_integer = false;
    // Bound state. `set` distinguishes "written" from "defaulted", which is the
    // whole of the first obligation.
    bool        lo_set = false, hi_set = false, free = false, minf = false;
    bool        lo_written = false, hi_written = false;
    bool        has_bound_record = false;
    std::string lo, hi;
    bool        semicont = false;
    int         line = 0;
};

std::string upper(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(),
                   [](unsigned char c) { return static_cast<char>(std::toupper(c)); });
    return s;
}

bool isNumber(const std::string& s) {
    if (s.empty()) { return false; }
    std::size_t i = (s[0] == '+' || s[0] == '-') ? 1 : 0;
    if (i == s.size()) { return false; }
    bool dot = false, digit = false, exp = false;
    for (; i < s.size(); ++i) {
        const char c = s[i];
        if (std::isdigit(static_cast<unsigned char>(c))) { digit = true; }
        else if (c == '.' && !dot && !exp) { dot = true; }
        else if ((c == 'e' || c == 'E' || c == 'd' || c == 'D') && digit && !exp) {
            exp = true;
            if (i + 1 < s.size() && (s[i + 1] == '+' || s[i + 1] == '-')) { ++i; }
        }
        else { return false; }
    }
    if (!digit) { return false; }
    const std::size_t exponent_at = s.find_first_of("eEdD");
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

/** Strictly below zero, by VALUE and not by first character.
 *
 *  §4.2's rule is "the upper bound is strictly less than 0", and `-0.0` is zero.
 *  Testing `v[0] == '-'` calls it negative and opens the lower bound to
 *  -infinity on a file that meant to fix the variable at zero -- the same
 *  boundary CPLEX deliberately treats as its own case, reached by a different
 *  spelling. */
bool isStrictlyNegative(const std::string& s);

/** Give a decimal digits on BOTH sides of its point.
 *
 *  MPS inherits Fortran's numerals, so `30.`, `-1.` and `.301` are all ordinary
 *  and all appear in `afiro.mps`, which is about as canonical as this format
 *  gets. SMT-LIB's `⟨decimal⟩` is `⟨numeral⟩.⟨numeral⟩` and requires a digit on
 *  each side, so the typechecker refuses those three spellings -- correctly,
 *  since it is enforcing SMT-LIB's grammar rather than this format's.
 *
 *  Normalising here is the right layer: translating a format's own spelling of
 *  a value into the IR's is what a frontend is for, and passing it through
 *  unchanged made a valid MPS file read as a type error on a number that is
 *  written the way the format writes numbers. */
std::string smtDecimal(std::string d) {
    const std::size_t dot = d.find('.');
    if (dot == std::string::npos) { return d; }
    if (dot + 1 == d.size()) { d += "0"; }                 // `30.` -> `30.0`
    const std::size_t first = (!d.empty() && (d[0] == '+' || d[0] == '-')) ? 1 : 0;
    if (d.size() > first && d[first] == '.') {             // `.301` -> `0.301`
        d.insert(first, "0");
    }
    return d;
}

/** Scientific notation is legal in MPS and is not an SMT-LIB numeral, so it is
 *  expanded to a plain decimal here. Done as text to stay exact: routing it
 *  through a double is what LIT_REAL exists to avoid. Every exit goes through
 *  smtDecimal, because the expansion can itself produce a trailing point. */
std::string plainDecimal(const std::string& s) {
    const std::size_t e = s.find_first_of("eEdD");
    if (e == std::string::npos) { return smtDecimal(s); }
    std::string mant = s.substr(0, e);
    int exp = std::atoi(s.c_str() + e + 1);
    std::string sign;
    if (!mant.empty() && (mant[0] == '+' || mant[0] == '-')) {
        if (mant[0] == '-') { sign = "-"; }
        mant.erase(0, 1);
    }
    std::size_t dot = mant.find('.');
    std::string digits = mant;
    int frac = 0;
    if (dot != std::string::npos) {
        frac = static_cast<int>(mant.size() - dot - 1);
        digits.erase(dot, 1);
    }
    exp -= frac;
    if (exp >= 0) {
        return smtDecimal(sign + digits + std::string(static_cast<std::size_t>(exp), '0'));
    }
    const int need = -exp;
    if (static_cast<int>(digits.size()) <= need) {
        digits.insert(0, static_cast<std::size_t>(need - static_cast<int>(digits.size()) + 1), '0');
    }
    digits.insert(digits.size() - static_cast<std::size_t>(need), ".");
    return smtDecimal(sign + digits);
}

bool isStrictlyNegative(const std::string& s) {
    const std::string d = plainDecimal(s);
    if (d.empty() || d[0] != '-') { return false; }
    for (std::size_t i = 1; i < d.size(); ++i) {
        if (d[i] != '0' && d[i] != '.') { return true; }
    }
    return false;              // -0, -0.0, -0.000
}

class MpsParser {
public:
    MpsParser(std::istream& input, std::string file, bool highs_recovery = false,
              const char** allocation_stage = nullptr)
        : input_(input), file_(std::move(file)), highs_recovery_(highs_recovery),
          allocation_stage_(allocation_stage) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        report_ = &report;
        if (highs_recovery_) {
            Uir::EncodingChoice dialect;
            dialect.site = file_;
            dialect.unified_op = "MPS reader";
            dialect.strategy = "highs-warning-recovery";
            dialect.fidelity = Uir::Fidelity::exact();
            dialect.rationale = "Explicit HiGHS warning-recovery interpretation: ignore undefined "
                "rows, retain first nonzero linear entries and first RHS/ranges/simple bounds, allow "
                "bounds-only columns, and retain a zero default lower bound for negative UP. "
                "Finite decimal coefficients remain exact; numerical tolerances and NaN recovery "
                "are not emulated. Every recovered record is reported.";
            report_->addChoice(std::move(dialect));
        }
        stage("input row/column records");
        if (!read(diags)) { return nullptr; }
        stage("HIR construction");
        return build(diags);
    }

private:
    void stage(const char* name) {
        if (allocation_stage_) { *allocation_stage_ = name; }
    }

    void recovered(const std::string& message, int line, Uir::Diagnostics& diags) {
        diags.warn(ErrorCode::E_PARSE, "HiGHS recovery: " + message, at(line));
        report_->addWarning({Uir::Severity::WARNING, ErrorCode::E_PARSE,
                             "HiGHS recovery: " + message, at(line)});
    }
    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = line;
        l.column = 1;
        return l;
    }

    Col& column(const std::string& name, int line) {
        const auto it = col_index_.find(name);
        if (it != col_index_.end()) { return cols_[it->second]; }
        col_index_[name] = cols_.size();
        Col c;
        c.name = name;
        c.line = line;
        cols_.push_back(std::move(c));
        return cols_.back();
    }

    std::size_t coefficientId(const std::string& text) {
        const auto found = coefficient_index_.find(text);
        if (found != coefficient_index_.end()) { return found->second; }
        const std::size_t id = coefficient_text_.size();
        const auto inserted = coefficient_index_.emplace(text, id);
        // unordered_map rehash preserves references to its elements. This
        // pointer index avoids a second string copy for unique coefficients.
        coefficient_text_.push_back(&inserted.first->first);
        return id;
    }

    bool read(Uir::Diagnostics& diags) {
        std::istream& in = input_;
        std::string raw;
        int lineno = 0;
        std::string section;
        // §2.3: the marker is POSITIONAL STATE, carried between lines. That is
        // what makes ignoring it a silent relaxation rather than a parse error.
        bool integer_block = false;

        while (std::getline(in, raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            if (!raw.empty() && raw[0] == '*') { continue; }        // comment
            std::istringstream ls(raw);
            std::vector<std::string> tok;
            std::string t;
            while (ls >> t) { tok.push_back(t); }
            // A marker starts a trailing comment only after a complete data
            // record. Leading/embedded markers can be actual row/column names;
            // the former unconditional '$' truncation silently lost those.
            for (std::size_t i = 0; i < tok.size(); ++i) {
                if (tok[i].empty() || (tok[i][0] != '$' && tok[i][0] != '*')) { continue; }
                bool complete = false;
                if (section == "ROWS") { complete = i == 2; }
                if (section == "COLUMNS" || section == "RHS" || section == "RANGES") {
                    complete = (i == 3 || i == 5) && isNumber(tok[2])
                        && (i != 5 || isNumber(tok[4]));
                    // A declared row is a coefficient record, even if its name
                    // starts with a marker. An undeclared name with a numeric
                    // value is ambiguous and remains a diagnostic.
                    if (row_index_.count(tok[i])
                        || (i + 1 < tok.size() && isNumber(tok[i + 1]))) { complete = false; }
                }
                if (section == "BOUNDS" && !tok.empty()) {
                    const std::string bound = upper(tok[0]);
                    const bool no_value = bound == "FR" || bound == "MI"
                        || bound == "PL" || bound == "BV";
                    complete = no_value ? i == 3 : i == 4 && isNumber(tok[3]);
                }
                if (section == "QUADOBJ" || section == "QMATRIX" || section == "QSECTION") {
                    complete = i == 3 && isNumber(tok[2]);
                }
                if (!complete) { continue; }
                if (tok[i][0] == '*' && report_) {
                    report_->addChoice({file_ + ":" + std::to_string(lineno),
                        "mps-comment", "trailing-asterisk-comment", Uir::Fidelity::exact(),
                        "A marker after a complete record starts an inline comment; "
                        "this convention is verified on Gurobi's fixed-field reader"});
                }
                tok.erase(tok.begin() + static_cast<long>(i), tok.end());
                break;
            }
            if (tok.empty()) { continue; }

            // A section header starts in column 1; data lines are indented.
            if (!std::isspace(static_cast<unsigned char>(raw[0]))) {
                section = upper(tok[0]);
                const bool supported = section == "NAME" || section == "OBJSENSE"
                    || section == "OBJNAME" || section == "ROWS"
                    || section == "COLUMNS" || section == "RHS"
                    || section == "RANGES" || section == "BOUNDS"
                    || section == "ENDATA";
                const bool quadratic = section == "QUADOBJ" || section == "QMATRIX"
                    || section == "QSECTION";
                if (quadratic) {
                    // Which section this is decides how an OFF-DIAGONAL entry
                    // is read, so it is remembered rather than folded away
                    // here: QUADOBJ and QSECTION give one triangle and QMATRIX
                    // the whole symmetric matrix, which differ by exactly a
                    // factor of two on the off-diagonal.
                    // Two quadratic sections in one file ACCUMULATE, each
                    // entry read under its own section's convention. This was
                    // refused until 2026-09-22 on the grounds that reading
                    // both "would double every coefficient" and picking one
                    // "would be a silent choice" -- true of both, and the
                    // comment said in place that what HiGHS does with
                    // `qjh_quadobj_qmatrix.mps` "is not recorded here".
                    //
                    // It is now, and it is neither: HiGHS SUMS them. The
                    // corpus states one model four ways and the three
                    // single-section spellings (`qjh`, `qjh_quadobj`,
                    // `qjh_qmatrix`) all optimise to -5.25, while
                    // `qjh_quadobj_qmatrix` optimises to -2.75. A doubled
                    // quadratic term is exactly what separates those two
                    // numbers, so the reference reader accumulates -- which is
                    // also what this reader already does for a repeated entry
                    // WITHIN one section (`2821-duplicate.mps`), under the
                    // same argument that last-wins would read a model nobody
                    // wrote.
                    //
                    // So nothing here has to change except not refusing: the
                    // per-entry convention below already keys off the CURRENT
                    // section, and repeats already sum. There is no choice to
                    // record, because there is no longer a decision -- the
                    // format's own reader settles it, and `test_mps_quadratic`
                    // pins our optimum against its -2.75.
                    quad_section_ = section;
                    // `QSECTION <row>` names the row the quadratic belongs to.
                    // Only the objective row is implemented; a quadratic
                    // CONSTRAINT is a different construct and is refused by
                    // name rather than silently added to the objective.
                    quad_row_ = section == "QSECTION" && tok.size() >= 2 ? tok[1]
                                                                         : std::string{};
                    continue;
                }
                const bool known_unsupported = section == "SOS"
                    || section == "INDICATORS";
                if (known_unsupported) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "the " + section + " section is not supported yet",
                                at(lineno));
                    return false;
                }
                if (!supported) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "unknown MPS section '" + tok[0]
                                    + "' cannot be ignored", at(lineno));
                    return false;
                }
                if (section == "ENDATA") { saw_endata_ = true; break; }
                if (section == "OBJSENSE" && tok.size() >= 2) {
                    const std::string sense = upper(tok[1]);
                    if (sense != "MAX" && sense != "MAXIMIZE"
                        && sense != "MIN" && sense != "MINIMIZE") {
                        diags.error(ErrorCode::E_PARSE,
                                    "OBJSENSE must be MAX or MIN", at(lineno));
                        return false;
                    }
                    maximise_ = sense == "MAX" || sense == "MAXIMIZE";
                    section = "";
                }
                if (section == "OBJNAME" && tok.size() >= 2) {
                    explicit_objective_row_ = tok[1];
                    section = "";
                }
                continue;
            }
            if (section == "OBJSENSE") {
                const std::string sense = upper(tok[0]);
                if (tok.size() != 1 || (sense != "MAX" && sense != "MAXIMIZE"
                                        && sense != "MIN" && sense != "MINIMIZE")) {
                    diags.error(ErrorCode::E_PARSE,
                                "OBJSENSE must contain exactly MAX or MIN", at(lineno));
                    return false;
                }
                maximise_ = sense == "MAX" || sense == "MAXIMIZE";
                continue;
            }
            if (section == "OBJNAME") {
                if (tok.size() != 1 || !explicit_objective_row_.empty()) {
                    diags.error(ErrorCode::E_PARSE,
                                "OBJNAME must contain exactly one row name", at(lineno));
                    return false;
                }
                explicit_objective_row_ = tok[0];
                continue;
            }
            if (section == "ROWS") {
                if (tok.size() < 2) {
                    diags.error(ErrorCode::E_PARSE, "a ROWS line is `<type> <name>`",
                                at(lineno));
                    return false;
                }
                const std::string ty = upper(tok[0]);
                if (ty != "N" && ty != "L" && ty != "G" && ty != "E") {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + tok[0] + "' is not a row type (N, L, G, E)",
                                at(lineno));
                    return false;
                }
                Row r;
                r.type = ty[0];
                if (r.type == 'N') { r.name = std::make_unique<std::string>(tok[1]); }
                r.line = lineno;
                if (row_index_.find(tok[1]) != row_index_.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "duplicate MPS row name '" + tok[1] + "'", at(lineno));
                    return false;
                }
                if (r.type == 'N') { n_rows_.push_back(tok[1]); }
                row_index_[tok[1]] = rows_.size();
                rows_.push_back(std::move(r));
                continue;
            }
            if (section == "QUADOBJ" || section == "QMATRIX"
                || section == "QSECTION") {
                if (tok.size() != 3) {
                    diags.error(ErrorCode::E_PARSE,
                                "a " + section + " line is `<col> <col> <value>`",
                                at(lineno));
                    return false;
                }
                for (int k = 0; k < 2; ++k) {
                    if (col_index_.find(tok[static_cast<std::size_t>(k)])
                        == col_index_.end()) {
                        diags.error(ErrorCode::E_PARSE,
                                    section + " names undeclared column '"
                                        + tok[static_cast<std::size_t>(k)] + "'",
                                    at(lineno));
                        return false;
                    }
                }
                if (!isNumber(tok[2])) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + tok[2] + "' is not a number", at(lineno));
                    return false;
                }
                // The coefficient of the MONOMIAL, so the three spellings meet
                // here rather than in the objective builder.
                //
                //   x_i x_i v   ->  (v/2) x_i^2          every section
                //   x_i x_j v   ->   v    x_i x_j        QUADOBJ / QSECTION
                //   x_i x_j v   ->  (v/2) x_i x_j        QMATRIX
                //
                // The `v/2` is the 1/2 of `c'x + 1/2 x'Qx`, which these
                // sections carry as a notation. QUADOBJ and QSECTION give ONE
                // triangle, so an off-diagonal entry stands for its mirror too
                // and the halves add back to v; QMATRIX gives both triangles
                // and each entry is halved. Verified against HiGHS's own
                // regression set, where `2821{,-duplicate,-summation}.mps`
                // (QUADOBJ) and `2821-qmatrix.mps` state one model four ways --
                // see test_mps_quadratic.cpp.
                const bool diagonal = tok[0] == tok[1];
                const std::string contribution =
                    (diagonal || section == "QMATRIX") ? halveDecimal(tok[2]) : tok[2];
                const std::string key = tok[0] < tok[1] ? tok[0] + '\0' + tok[1]
                                                        : tok[1] + '\0' + tok[0];
                const auto found = quad_index_.find(key);
                if (found == quad_index_.end()) {
                    QuadTerm q;
                    q.a = tok[0];
                    q.b = tok[1];
                    q.coeff = contribution;
                    q.line = lineno;
                    quad_index_.emplace(key, quads_.size());
                    quads_.push_back(std::move(q));
                } else {
                    // Repeats SUM. `2821-duplicate.mps` is HiGHS's regression
                    // for exactly this, and last-wins would read 1.5 where the
                    // model says 2.0.
                    QuadTerm& q = quads_[found->second];
                    q.coeff = addDecimals(q.coeff, contribution);
                }
                continue;
            }
            if (section == "COLUMNS") {
                if (tok.size() >= 3 && upper(tok[1]).find("MARKER") != std::string::npos) {
                    const std::string last = upper(tok.back());
                    if (last.find("INTORG") != std::string::npos) { integer_block = true; }
                    else if (last.find("INTEND") != std::string::npos) { integer_block = false; }
                    continue;
                }
                if (tok.size() < 3 || (tok.size() % 2) == 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "a COLUMNS line is `<col> <row> <value> [<row> <value>]`",
                                at(lineno));
                    return false;
                }
                Col& c = column(tok[0], lineno);
                const std::size_t column_id = col_index_.at(tok[0]);
                if (integer_block) {
                    c.integer = true;
                    c.marker_integer = true;
                }
                for (std::size_t k = 1; k + 1 < tok.size(); k += 2) {
                    if (highs_recovery_ && !isNumber(tok[k + 1])) {
                        diags.error(ErrorCode::E_PARSE, "recovery requires finite numeric coefficients", at(lineno));
                        return false;
                    }
                    const auto it = row_index_.find(tok[k]);
                    if (it == row_index_.end()) {
                        if (highs_recovery_) {
                            recovered("ignored undefined COLUMNS row '" + tok[k] + "'", lineno, diags);
                            continue;
                        }
                        diags.error(ErrorCode::E_PARSE,
                                    "column '" + tok[0] + "' names undeclared row '"
                                        + tok[k] + "'", at(lineno));
                        return false;
                    }
                    if (!isNumber(tok[k + 1])) {
                        diags.error(ErrorCode::E_PARSE,
                                    "'" + tok[k + 1] + "' is not a number", at(lineno));
                        return false;
                    }
                    auto& terms = rows_[it->second].terms;
                    if (highs_recovery_) {
                        const auto value = plainDecimal(tok[k + 1]);
                        if (value.find_first_not_of("+-0.") == std::string::npos) { continue; }
                    }
                    if (highs_recovery_ && std::any_of(terms.begin(), terms.end(),
                        [&](const auto& term) { return term.first == column_id; })) {
                        recovered("ignored duplicate COLUMNS value for '" + tok[0] + "' / '" + tok[k] + "'",
                                  lineno, diags);
                        continue;
                    }
                    // Large sparse rows must not retain up to a whole row of
                    // unused capacity. Keep the small-row layout allocation-free
                    // until insertion and grow larger buffers by about one eighth.
                    if (terms.size() >= 128 && terms.size() == terms.capacity()) {
                        const std::size_t growth = std::min(
                            terms.max_size() - terms.size(),
                            std::max(terms.size() / 8, std::size_t{64}));
                        if (growth != 0) { terms.reserve(terms.size() + growth); }
                    }
                    terms.emplace_back(column_id, coefficientId(tok[k + 1]));
                }
                continue;
            }
            if (section == "RHS" || section == "RANGES") {
                if (tok.size() < 3 || (tok.size() % 2) == 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "an " + section + " line is `<name> <row> <value> ...`",
                                at(lineno));
                    return false;
                }
                std::string& selected = section == "RHS" ? rhs_vector_ : range_vector_;
                if (selected.empty()) { selected = tok[0]; }
                if (tok[0] != selected) {
                    std::unordered_set<std::string>& reported =
                        section == "RHS" ? ignored_rhs_vectors_ : ignored_range_vectors_;
                    if (reported.insert(tok[0]).second) {
                        Uir::EncodingChoice choice;
                        choice.site = file_ + ":" + std::to_string(lineno);
                        choice.unified_op = section + " vector";
                        choice.strategy = "first-vector-selected";
                        choice.fidelity = Uir::Fidelity::exact();
                        choice.rationale = "MPS selects vector '" + selected
                            + "' and discards later vector '" + tok[0] + "'";
                        report_->addChoice(std::move(choice));
                    }
                    continue;
                }
                for (std::size_t k = 1; k + 1 < tok.size(); k += 2) {
                    if (highs_recovery_ && !isNumber(tok[k + 1])) {
                        diags.error(ErrorCode::E_PARSE, "recovery requires finite numeric values", at(lineno));
                        return false;
                    }
                    const auto it = row_index_.find(tok[k]);
                    if (it == row_index_.end()) {
                        if (highs_recovery_) {
                            recovered("ignored undefined " + section + " row '" + tok[k] + "'", lineno, diags);
                            continue;
                        }
                        diags.error(ErrorCode::E_PARSE,
                                    "undeclared row '" + tok[k] + "'", at(lineno));
                        return false;
                    }
                    if (!isNumber(tok[k + 1])) {
                        diags.error(ErrorCode::E_PARSE,
                                    "'" + tok[k + 1] + "' is not a number", at(lineno));
                        return false;
                    }
                    Row& row = rows_[it->second];
                    if (section == "RHS") {
                        if (row.rhs_set) {
                            if (highs_recovery_) {
                                recovered("ignored duplicate RHS for '" + tok[k] + "'", lineno, diags);
                                continue;
                            }
                            diags.error(ErrorCode::E_PARSE,
                                        "duplicate RHS value for row '" + tok[k] + "'",
                                        at(lineno));
                            return false;
                        }
                        row.rhs = coefficient_text_[coefficientId(tok[k + 1])];
                        row.rhs_set = true;
                    } else {
                        if (row.type == 'N') {
                            if (highs_recovery_) {
                                recovered("ignored RANGES on free row '" + tok[k] + "'", lineno, diags);
                                continue;
                            }
                            diags.error(ErrorCode::E_PARSE,
                                        "RANGES cannot be applied to free N row '"
                                            + tok[k] + "'", at(lineno));
                            return false;
                        }
                        if (row.has_range) {
                            if (highs_recovery_) {
                                recovered("ignored duplicate RANGES for '" + tok[k] + "'", lineno, diags);
                                continue;
                            }
                            diags.error(ErrorCode::E_PARSE,
                                        "duplicate RANGES value for row '" + tok[k] + "'",
                                        at(lineno));
                            return false;
                        }
                        row.has_range = true;
                        row.range = coefficient_text_[coefficientId(tok[k + 1])];
                    }
                }
                continue;
            }
            if (section == "BOUNDS") {
                if (tok.size() < 3) {
                    diags.error(ErrorCode::E_PARSE,
                                "a BOUNDS line is `<type> <set> <col> [<value>]`",
                                at(lineno));
                    return false;
                }
                const std::string ty = upper(tok[0]);
                if (bound_vector_.empty()) { bound_vector_ = tok[1]; }
                if (tok[1] != bound_vector_) {
                    if (ignored_bound_vectors_.insert(tok[1]).second) {
                        Uir::EncodingChoice choice;
                        choice.site = file_ + ":" + std::to_string(lineno);
                        choice.unified_op = "BOUNDS vector";
                        choice.strategy = "first-vector-selected";
                        choice.fidelity = Uir::Fidelity::exact();
                        choice.rationale = "MPS selects bound vector '" + bound_vector_
                            + "' and discards later vector '" + tok[1] + "'";
                        report_->addChoice(std::move(choice));
                    }
                    continue;
                }
                if (highs_recovery_ && !col_index_.count(tok[2])) {
                    column(tok[2], lineno);
                    recovered("declared bounds-only column '" + tok[2] + "'", lineno, diags);
                }
                const auto declared_column = col_index_.find(tok[2]);
                if (declared_column == col_index_.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "BOUNDS names undeclared column '" + tok[2] + "'",
                                at(lineno));
                    return false;
                }
                Col& c = cols_[declared_column->second];
                const bool has_value = tok.size() >= 4 && isNumber(tok[3]);
                const std::string v = has_value ? tok[3] : "";
                if (highs_recovery_ && !has_value && (ty == "LO" || ty == "UP" || ty == "FX"
                    || ty == "LI" || ty == "UI" || ty == "SC" || ty == "SI")) {
                    return badBound(diags, ty, lineno);
                }
                const bool writes_lower = ty == "LO" || ty == "LI" || ty == "FX"
                    || ty == "FR" || ty == "MI" || ty == "BV";
                const bool writes_upper = ty == "UP" || ty == "UI" || ty == "FX"
                    || ty == "FR" || ty == "PL" || ty == "BV" || ty == "SC"
                    || ty == "SI";
                if ((writes_lower && c.lo_written) || (writes_upper && c.hi_written)) {
                    if (highs_recovery_ && !(writes_lower && writes_upper)) {
                        recovered("ignored duplicate bound for '" + c.name + "'", lineno, diags);
                        continue;
                    }
                    diags.error(ErrorCode::E_PARSE,
                                "duplicate "
                                    + std::string(writes_lower && c.lo_written
                                                      ? "lower" : "upper")
                                    + " bound for column '" + c.name + "'", at(lineno));
                    return false;
                }
                c.has_bound_record = true;
                c.lo_written = c.lo_written || writes_lower;
                c.hi_written = c.hi_written || writes_upper;
                if (ty == "UP") {
                    if (!has_value) { return badBound(diags, ty, lineno); }
                    c.hi = v; c.hi_set = true;
                    // §4.2, and the rule is stated rather than assumed. CPLEX
                    // opens the lower bound to -infinity only when the upper is
                    // STRICTLY less than zero, and at exactly `UP 0` keeps it at
                    // 0 -- fixing the variable. Other readers differ, so the
                    // choice is warned per instance.
                    if (isStrictlyNegative(v) && !highs_recovery_) {
                        c.minf = true;
                        // Exact, and recorded rather than downgraded: reading
                        // the bound CPLEX's way does not approximate anything,
                        // it picks one of three admissible readings. What a
                        // later result row needs is which one ran -- a row
                        // produced under this rule is not comparable with one
                        // produced by a reader that keeps the lower bound at 0.
                        Uir::EncodingChoice ch;
                        ch.site       = file_ + ":" + std::to_string(lineno);
                        ch.unified_op = "BOUNDS UP";
                        ch.strategy   = "cplex-negative-up-opens-lower";
                        ch.fidelity   = Uir::Fidelity::exact();
                        ch.rationale =
                            "BOUNDS UP with a negative value on '" + c.name
                            + "': lower bound opened to -infinity per CPLEX; other "
                              "readers keep it at 0, and `UP 0` is a third behaviour";
                        report_->addChoice(std::move(ch));
                        diags.warn(ErrorCode::E_PARSE,
                                   "BOUNDS UP with a negative value on '" + c.name
                                       + "': its lower bound is opened to -infinity, "
                                         "which is CPLEX's rule; readers differ, and "
                                         "`UP 0` is a third behaviour that keeps the "
                                         "lower bound at 0",
                                   at(lineno));
                    }
                } else if (ty == "LO") {
                    if (!has_value) { return badBound(diags, ty, lineno); }
                    c.lo = v; c.lo_set = true; c.minf = false; c.free = false;
                } else if (ty == "FX") {
                    if (!has_value) { return badBound(diags, ty, lineno); }
                    c.lo = c.hi = v; c.lo_set = c.hi_set = true;
                    c.minf = false; c.free = false;
                } else if (ty == "FR") {
                    c.free = true;
                } else if (ty == "MI") {
                    c.minf = true; c.lo_set = false;
                } else if (ty == "PL") {
                    c.hi_set = false;
                } else if (ty == "BV") {
                    // Integer and {0,1}, overriding anything else.
                    c.integer = true;
                    c.lo = "0"; c.hi = "1"; c.lo_set = c.hi_set = true;
                    c.free = c.minf = false;
                } else if (ty == "LI" || ty == "UI") {
                    if (!has_value) { return badBound(diags, ty, lineno); }
                    c.integer = true;
                    if (ty == "LI") {
                        c.lo = v; c.lo_set = true; c.minf = false; c.free = false;
                    }
                    else { c.hi = v; c.hi_set = true; }
                } else if (ty == "SC" || ty == "SI") {
                    if (!has_value) { return badBound(diags, ty, lineno); }
                    c.semicont = true;
                    if (ty == "SI") { c.integer = true; }
                    c.hi = v; c.hi_set = true;
                } else {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + tok[0] + "' is not a bound type", at(lineno));
                    return false;
                }
                continue;
            }
            if (section == "NAME" || section.empty()) { continue; }
        }
        // ENDATA terminates the model, but consume the remaining bytes so a
        // pipe producer can finish and report decompression/transport errors.
        if (saw_endata_) {
            char remainder[8192];
            while (in.read(remainder, sizeof(remainder)) || in.gcount() != 0) {}
        }
        if (in.bad()) {
            diags.error(ErrorCode::E_IO, "failed while reading MPS source", at(lineno));
            return false;
        }
        if (integer_block) {
            diags.error(ErrorCode::E_PARSE,
                        "an INTORG marker has no matching INTEND", at(lineno));
            return false;
        }
        if (!saw_endata_) {
            diags.error(ErrorCode::E_PARSE,
                        "an MPS file must end with ENDATA", at(lineno));
            return false;
        }
        if (rows_.empty()) {
            diags.error(ErrorCode::E_PARSE, "the file has no ROWS section", at(1));
            return false;
        }
        if (!explicit_objective_row_.empty()) {
            const auto selected = row_index_.find(explicit_objective_row_);
            if (selected == row_index_.end()
                || rows_[selected->second].type != 'N') {
                diags.error(ErrorCode::E_PARSE,
                            "OBJNAME '" + explicit_objective_row_
                                + "' does not name an N row", at(1));
                return false;
            }
            objective_row_ = explicit_objective_row_;
        } else if (!n_rows_.empty()) {
            objective_row_ = n_rows_.front();
        }
        for (const std::string& free_row : n_rows_) {
            if (free_row == objective_row_) { continue; }
            const Row& row = rows_[row_index_.at(free_row)];
            Uir::EncodingChoice choice;
            choice.site = file_ + ":" + std::to_string(row.line);
            choice.unified_op = "N row";
            choice.strategy = explicit_objective_row_.empty()
                ? "first-n-row-is-objective" : "objname-selects-objective";
            choice.fidelity = Uir::Fidelity::exact();
            const std::string role = explicit_objective_row_.empty()
                ? "a second N row" : "a non-objective N row selected by OBJNAME";
            choice.rationale = "row '" + free_row + "' is " + role + " and "
                "therefore constrains nothing; selected objective row is '"
                + objective_row_ + "'";
            report_->addChoice(std::move(choice));
            diags.warn(ErrorCode::E_PARSE,
                       "row '" + free_row + "' is " + role + "; objective row is '"
                           + objective_row_ + "' and this row constrains nothing",
                       at(row.line));
        }
        return true;
    }

    bool badBound(Uir::Diagnostics& diags, const std::string& ty, int line) {
        diags.error(ErrorCode::E_PARSE, "bound type " + ty + " needs a value", at(line));
        return false;
    }

    // ---- construction ----------------------------------------------------

    H::Sort sortOf(const Col& c) const {
        return c.integer ? H::Sort::integer() : H::Sort::real();
    }

    H::ExprPtr num(const std::string& text, int line) const {
        const auto found = numbers_.find(text);
        if (found != numbers_.end()) { return found->second; }
        return numbers_.emplace(text, H::mkReal(addDecimals(plainDecimal(text), "0"), at(line))).first->second;
    }

    H::ExprPtr symbol(const std::string& name, int line) const {
        const auto found = symbols_.find(name);
        if (found != symbols_.end()) { return found->second; }
        const Col& col = cols_[col_index_.at(name)];
        return symbols_.emplace(name, H::mkIdent(name, sortOf(col), at(line))).first->second;
    }

    H::ExprPtr symbol(const H::VarDecl& declaration, int line) const {
        const auto found = symbols_.find(declaration.name);
        if (found != symbols_.end()) { return found->second; }
        return symbols_.emplace(declaration.name,
            H::mkIdent(declaration.name, declaration.sort, at(line))).first->second;
    }

    std::string freshObjectiveName(const std::string& row_name) const {
        std::string name = row_name;
        const std::string base = row_name + "__objective";
        std::size_t suffix = 0;
        while (col_index_.count(name) != 0) {
            name = base + (suffix == 0 ? std::string() : std::to_string(suffix));
            ++suffix;
        }
        return name;
    }

    H::ExprPtr coefficient(std::size_t id, int line) const {
        H::ExprPtr& value = coefficient_nodes_[id];
        if (!value) {
            value = H::mkReal(addDecimals(plainDecimal(*coefficient_text_[id]), "0"), at(line));
        }
        return value;
    }

    /** `rhs + delta`, exactly, without going through a double. */
    static std::string addDecimals(const std::string& a, const std::string& b);

    /** `v / 2`, exactly.
     *
     *  Halving always terminates in base ten, so this is a digit operation and
     *  not an approximation -- which matters because the quadratic sections
     *  carry the `1/2` of `c'x + ½ x'Qx` as a *notation*. `lp.md` §4.5 states
     *  the consequence of getting it wrong: every quadratic coefficient comes
     *  out scaled by two, in a model that still type-checks and still solves. */
    static std::string halveDecimal(const std::string& v);

    H::ExprPtr sumOf(const Row& r,
                     const std::vector<H::VarDecl>* declarations = nullptr) const {
        std::vector<H::ExprPtr> addends;
        addends.reserve(r.terms.size());
        for (const auto& [column_id, coefficient_id] : r.terms) {
            const H::VarDecl* declaration = declarations ? &declarations->at(column_id) : nullptr;
            const std::string& col = declaration ? declaration->name : cols_[column_id].name;
            const H::ExprPtr value = coefficient(coefficient_id, r.line);
            if (value->name == "0") { continue; }
            const H::ExprPtr variable = declaration
                ? symbol(*declaration, r.line) : symbol(col, r.line);
            if (value->name == "1") {
                addends.push_back(variable);
            } else if (value->name == "-1") {
                auto inserted = negatives_.emplace(col, H::ExprPtr{});
                if (inserted.second) {
                    inserted.first->second = H::mkOp(
                        H::Op::MUL, {value, variable}, at(r.line));
                }
                addends.push_back(inserted.first->second);
            } else {
                addends.push_back(H::mkOp(
                    H::Op::MUL, {value, variable}, at(r.line)));
            }
        }
        if (addends.empty()) { return num("0", r.line); }
        if (addends.size() == 1) { return addends.front(); }
        return H::mkOp(H::Op::ADD, std::move(addends), at(r.line));
    }

    void appendPackedRow(H::PackedLinearRows& data, const Row& source,
                         H::LinearRowRelation relation, const std::string& rhs,
                         const std::string& upper = "0",
                         const H::PackedLinearTerm* defining_term = nullptr) {
        constexpr std::size_t batch_rows = 4096;
        if (defining_term || after_packed_objective_
            || data.batches.empty() || data.batches.back().rows.size() == batch_rows) {
            data.batches.emplace_back();
            auto& batch = data.batches.back();
            batch.source_file = file_;
            batch.rows.reserve(batch_rows);
            // The current row has been popped from rows_; all remaining row
            // lengths are already known. Reserve precisely this batch's terms
            // so building compact output cannot double a wide matrix buffer.
            std::size_t terms = source.terms.size();
            if (defining_term) {
                if (terms == batch.terms.max_size()) {
                    throw std::length_error("packed MPS objective row is too large");
                }
                ++terms;
            }
            if (terms > batch.terms.max_size()) {
                throw std::length_error("packed MPS matrix row is too large");
            }
            std::size_t remaining = batch_rows - 1;
            for (const auto& pending : rows_) {
                // A wide objective owns a single-row batch. The following
                // matrix batch must never append to its exactly-sized buffer.
                if (defining_term) { break; }
                if (pending.type == 'N') {
                    if (has_packed_objective_ && *pending.name == objective_row_) { break; }
                    continue;
                }
                if (pending.terms.size() > batch.terms.max_size() - terms) {
                    throw std::length_error("packed MPS matrix batch is too large");
                }
                terms += pending.terms.size();
                if (--remaining == 0) { break; }
            }
            batch.terms.reserve(terms);
        }
        auto& batch = data.batches.back();
        H::PackedLinearRow row;
        row.begin = batch.terms.size();
        for (const auto& term : source.terms) {
            batch.terms.push_back({term.first, term.second});
        }
        if (defining_term) { batch.terms.push_back(*defining_term); }
        row.end = batch.terms.size();
        row.rhs = coefficientId(rhs);
        if (relation == H::LinearRowRelation::RANGE) { row.upper = coefficientId(upper); }
        row.source_line = static_cast<std::uint32_t>(source.line);
        row.relation = relation;
        batch.rows.push_back(row);
        after_packed_objective_ = defining_term != nullptr;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags) {
        auto model = std::make_shared<H::ConstraintModel>();
        // Each ordinary row needs a Constraint, comparison and sum, while
        // every non-unit matrix entry can also need a multiplication Expr.
        // Wide matrices therefore need packing even with few rows. Count
        // entries as well as rows before expanding any of them into HIR.
        constexpr std::size_t packed_row_threshold = 65536;
        constexpr std::size_t packed_term_threshold = 65536;
        std::shared_ptr<H::PackedLinearRows> packed;
        // A wide objective otherwise expands into IDENT/MUL expression nodes
        // even when every matrix row is packed. Its exact defining equality
        // can use the same storage. Keep small and quadratic objectives on
        // the ordinary path; a pure wide objective also enables packing.
        bool packed_objective = false;
        if (quads_.empty() && !objective_row_.empty()) {
            for (const Row& row : rows_) {
                if (row.type == 'N' && *row.name == objective_row_) {
                    packed_objective = row.terms.size() >= packed_term_threshold;
                    break;
                }
            }
        }
        has_packed_objective_ = packed_objective;
        std::size_t linear_terms = 0;
        for (const Row& row : rows_) {
            if (row.type == 'N') { continue; }
            // Saturation avoids overflow and stops counting as soon as the
            // storage decision is known; free rows and objectives do not use
            // the packed constraint representation.
            const std::size_t remaining = packed_term_threshold - linear_terms;
            linear_terms += std::min(row.terms.size(), remaining);
            if (linear_terms == packed_term_threshold) { break; }
        }
        if (rows_.size() - n_rows_.size() >= packed_row_threshold
            || linear_terms == packed_term_threshold || packed_objective) {
            packed = std::make_shared<H::PackedLinearRows>();
        }
        // `QSECTION <row>` names the row its entries belong to. Only the
        // objective row is implemented: a quadratic CONSTRAINT is a different
        // construct, and adding its terms to the objective would move them
        // from a bound the model states to a quantity it minimises.
        //
        // Checked here rather than at the header, because which row IS the
        // objective is not settled until OBJNAME and the first-N-row rule have
        // both run.
        if (!quad_row_.empty() && quad_row_ != objective_row_) {
            const auto named = row_index_.find(quad_row_);
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        named == row_index_.end()
                            ? "QSECTION names undeclared row '" + quad_row_ + "'"
                            : "QSECTION names row '" + quad_row_
                                  + "', which is not the objective row '"
                                  + objective_row_
                                  + "'; a quadratic constraint is not supported",
                        at(quads_.empty() ? 0 : quads_.front().line));
            return nullptr;
        }

        // Row lookup is complete. Drop the name index before constructing HIR,
        // and consume each parsed row so its metadata does not coexist with
        // the whole output model. Columns are retained only until their
        // declarations and semicontinuous domains have been constructed.
        decltype(row_index_){}.swap(row_index_);
        coefficient_nodes_.resize(coefficient_text_.size());
        stage("HIR declarations and bounds");
        if (packed_objective && cols_.size() == model->decls.max_size()) {
            throw std::length_error("packed objective has no declaration slot");
        }
        // Reserve the one auxiliary now, before the source declarations are
        // resident; appending it later must not double a large declaration buffer.
        model->decls.reserve(cols_.size() + static_cast<std::size_t>(packed_objective));
        // Bounds are immutable values. Share the implicit zero/one leaves
        // across columns, as num() already does for explicit bound values;
        // each declaration retains its own source location and domain.
        H::ExprPtr default_lower_bound;
        H::ExprPtr marker_upper_bound;

        for (const Col& c : cols_) {
            H::VarDecl d;
            d.name = c.name;
            d.sort = sortOf(c);
            d.loc = at(c.line);
            if (c.free) {
                // FR: neither bound.
            } else if (c.semicont) {
                // The disjunction is emitted below; no interval on the
                // declaration, for lp.md §4.4's reason.
            } else {
                if (c.lo_set) { d.lower_bound = num(c.lo, c.line); }
                else if (!c.minf) {
                    // As LP: a column with no BOUNDS entry is non-negative, and
                    // no line says so.
                    if (!default_lower_bound) {
                        default_lower_bound = H::mkInt(0, at(c.line));
                    }
                    d.lower_bound = default_lower_bound;
                }
                if (c.hi_set) { d.upper_bound = num(c.hi, c.line); }
                else if (c.marker_integer && !c.has_bound_record) {
                    // CPLEX's INTORG/INTEND convention makes an unbounded-by-
                    // record marker column binary by default. Any selected
                    // BOUNDS record switches back to the ordinary unspecified
                    // upper bound of +infinity.
                    if (!marker_upper_bound) {
                        marker_upper_bound = H::mkInt(1, at(c.line));
                    }
                    d.upper_bound = marker_upper_bound;
                }
            }
            model->decls.push_back(d);
        }

        for (const Col& c : cols_) {
            if (!c.semicont) { continue; }
            H::ExprPtr x = H::mkIdent(c.name, sortOf(c), at(c.line));
            std::vector<H::ExprPtr> band{
                H::mkOp(H::Op::LE, {num(c.lo_set ? c.lo : "1", c.line), x}, at(c.line))};
            if (c.hi_set) {
                band.push_back(H::mkOp(H::Op::LE, {x, num(c.hi, c.line)}, at(c.line)));
            }
            H::Constraint cc;
            cc.loc = at(c.line);
            cc.formula = H::mkOp(
                H::Op::OR,
                {H::mkOp(H::Op::EQ, {x, H::mkInt(0, at(c.line))}, at(c.line)),
                 band.size() == 1 ? band.front()
                                  : H::mkOp(H::Op::AND, std::move(band), at(c.line))},
                at(c.line));
            model->constraints.push_back(cc);
        }

        // Packed matrix terms refer to stable declaration ordinals. Linear
        // objectives can use those declarations too, so release the duplicate
        // column records and name index before materializing rows. Quadratic
        // terms still resolve names through the original column metadata.
        const bool released_columns = packed && quads_.empty();
        std::string packed_objective_name;
        std::string packed_objective_value_name;
        if (released_columns) {
            // Determine the sole selected objective's name while O(1) column
            // lookup is available. Retain one string, not the whole index.
            if (!objective_row_.empty()) {
                packed_objective_name = freshObjectiveName(objective_row_);
            }
            if (packed_objective) {
                const std::string stem = "__somt_mps_objective_value";
                packed_objective_value_name = stem;
                std::size_t suffix = 0;
                while (col_index_.count(packed_objective_value_name) != 0
                    || col_index_.count("|" + packed_objective_value_name + "|") != 0
                    || packed_objective_value_name == packed_objective_name) {
                    packed_objective_value_name = stem + std::to_string(++suffix);
                }
            }
            decltype(col_index_){}.swap(col_index_);
            decltype(cols_){}.swap(cols_);
        }

        // Every non-N row contributes exactly one constraint, including a
        // ranged row whose two endpoints are joined under one AND. Reserve
        // after releasing the lookup index so geometric vector growth does
        // not keep old and new HIR buffers alive together on large models.
        if (!packed) {
            model->constraints.reserve(model->constraints.size() + rows_.size() - n_rows_.size());
        }
        stage("objectives and matrix rows");
        while (!rows_.empty()) {
            Row r = std::move(rows_.front());
            rows_.pop_front();
            if (r.type == 'N') {
                if (*r.name != objective_row_) {
                    continue; // a free row
                }
                H::Objective o;
                o.kind = maximise_ ? H::ObjKind::MAXIMIZE : H::ObjKind::MINIMIZE;
                if (packed_objective) {
                    H::VarDecl value;
                    value.name = packed_objective_value_name;
                    value.sort = H::Sort::real();
                    value.auxiliary = true;
                    value.loc = at(r.line);
                    const std::size_t value_column = model->decls.size();
                    model->decls.push_back(std::move(value));
                    // MPS objective RHS is the negative constant offset:
                    // value = sum(a_i*x_i) - rhs, hence sum - value = rhs.
                    // The free Real auxiliary is uniquely defined for every
                    // source assignment, including integer-only source columns.
                    const H::PackedLinearTerm defining_term{value_column, coefficientId("-1")};
                    appendPackedRow(*packed, r, H::LinearRowRelation::EQ,
                                    r.rhsValue(), "0", &defining_term);
                    o.term = H::mkIdent(packed_objective_value_name, H::Sort::real(), at(r.line));
                    o.name = packed_objective_name;
                    o.loc = at(r.line);
                    model->objectives.push_back(std::move(o));
                    continue;
                }
                o.term = sumOf(r, released_columns ? &model->decls : nullptr);
                if (!quads_.empty()) {
                    // `c'x` is already in o.term; this is the `1/2 x'Qx` half,
                    // with the 1/2 already folded into each coefficient above.
                    std::vector<H::ExprPtr> addends;
                    // sumOf() gives a literal 0 for a row with no COLUMNS
                    // entries -- `qjh_uncon.mps` is purely quadratic -- and
                    // adding that 0 would print in the objective.
                    //
                    // The linear part is SPLICED rather than nested, so the
                    // objective is one flat sum. `c'x + 1/2 x'Qx` is a single
                    // sum of monomials and nesting the linear half would make
                    // the emitted text depend on which format the model was
                    // read from -- the same model from `qjh.lp` is flat, and
                    // test_lp_quadratic.cpp compares the two.
                    if (!r.terms.empty()) {
                        if (o.term->kind == H::ExprKind::OP
                            && o.term->op == H::Op::ADD) {
                            for (const H::ExprPtr& a : o.term->args) {
                                addends.push_back(a);
                            }
                        } else {
                            addends.push_back(o.term);
                        }
                    }
                    for (const QuadTerm& q : quads_) {
                        if (plainDecimal(q.coeff) == "0") { continue; }
                        H::ExprPtr product = H::mkOp(
                            H::Op::MUL,
                            {symbol(q.a, q.line), symbol(q.b, q.line)},
                            at(q.line));
                        addends.push_back(H::mkOp(
                            H::Op::MUL, {num(q.coeff, q.line), std::move(product)},
                            at(q.line)));
                    }
                    if (addends.empty()) { addends.push_back(num("0", r.line)); }
                    o.term = addends.size() == 1
                                 ? addends.front()
                                 : H::mkOp(H::Op::ADD, std::move(addends), at(r.line));
                }
                if (r.rhs_set && plainDecimal(r.rhsValue()) != "0"
                    && plainDecimal(r.rhsValue()) != "0.0") {
                    // MPS stores the negative of the objective offset in the
                    // RHS vector: RHS(obj)=-3.5 denotes objective +3.5.
                    o.term = H::mkOp(
                        H::Op::SUB, {o.term, num(r.rhsValue(), r.line)}, at(r.line));
                }
                // Rows and columns have separate source namespaces. Freshen
                // only the objective identifier, preserving every source column.
                o.name = released_columns ? packed_objective_name : freshObjectiveName(*r.name);
                o.loc = at(r.line);
                model->objectives.push_back(o);
                continue;
            }
            H::ExprPtr lhs;
            if (!packed) { lhs = sumOf(r); }
            H::Constraint c;
            c.loc = at(r.line);
            if (!r.has_range) {
                if (packed) {
                    const auto relation = r.type == 'L' ? H::LinearRowRelation::LE
                        : r.type == 'G' ? H::LinearRowRelation::GE : H::LinearRowRelation::EQ;
                    appendPackedRow(*packed, r, relation, r.rhsValue());
                    continue;
                }
                if (r.type == 'L') {
                    c.formula = H::mkOp(H::Op::LE, {lhs, num(r.rhsValue(), r.line)}, at(r.line));
                } else if (r.type == 'G') {
                    c.formula = H::mkOp(H::Op::GE, {lhs, num(r.rhsValue(), r.line)}, at(r.line));
                } else {
                    c.formula = H::mkOp(H::Op::EQ, {lhs, num(r.rhsValue(), r.line)}, at(r.line));
                }
                model->constraints.push_back(c);
                continue;
            }
            // §2.4. The interval a RANGES entry denotes depends on the row type,
            // and for E rows on the SIGN of the range value -- an equality row
            // with a range is no longer an equality, and which side it opens to
            // is decided by a sign the reader must inspect.
            std::string lo, hi;
            const std::string R = plainDecimal(*r.range);
            const bool negative = !R.empty() && R[0] == '-';
            const std::string absR = negative ? R.substr(1) : R;
            if (r.type == 'L') {
                lo = addDecimals(plainDecimal(r.rhsValue()), "-" + absR);
                hi = plainDecimal(r.rhsValue());
            } else if (r.type == 'G') {
                lo = plainDecimal(r.rhsValue());
                hi = addDecimals(plainDecimal(r.rhsValue()), absR);
            } else if (!negative) {
                lo = plainDecimal(r.rhsValue());
                hi = addDecimals(plainDecimal(r.rhsValue()), absR);
            } else {
                lo = addDecimals(plainDecimal(r.rhsValue()), "-" + absR);
                hi = plainDecimal(r.rhsValue());
            }
            if (packed) {
                appendPackedRow(*packed, r, H::LinearRowRelation::RANGE, lo, hi);
                continue;
            }
            c.formula = H::mkOp(
                H::Op::AND,
                {H::mkOp(H::Op::LE, {num(lo, r.line), lhs}, at(r.line)),
                 H::mkOp(H::Op::LE, {lhs, num(hi, r.line)}, at(r.line))},
                at(r.line));
            model->constraints.push_back(c);
        }
        if (packed) {
            // All IDs are final now, including bounds introduced while packing
            // RHS/range rows. Extract keys without copying the complete pool.
            coefficient_text_.clear();
            packed->numbers.resize(coefficient_index_.size());
            while (!coefficient_index_.empty()) {
                auto entry = coefficient_index_.extract(coefficient_index_.begin());
                packed->numbers[entry.mapped()] = addDecimals(plainDecimal(entry.key()), "0");
            }
            model->packed_linear_rows = std::move(packed);
            report_->addChoice({file_, "MPS linear rows", "packed-linear-rows",
                Uir::Fidelity::exact(),
                "Every numeric row retains its exact coefficients, relation, bounds and source line; "
                "typed validation precedes streaming SMT assertions without expression-tree expansion"});
        }
        (void)diags;
        return model;
    }

    bool has_packed_objective_ = false;
    bool after_packed_objective_ = false;
    std::istream& input_;
    std::string file_;
    bool highs_recovery_ = false;
    const char** allocation_stage_ = nullptr;
    Uir::TranslationReport* report_ = nullptr;   // set by parse(), never null after

    bool        maximise_ = false;
    std::string objective_row_;
    std::string explicit_objective_row_;
    /** Which quadratic section this file used, and for QSECTION the row it
     *  named. Empty when the file has no quadratic part. */
    std::string quad_section_;
    std::string quad_row_;
    std::vector<QuadTerm> quads_;
    std::unordered_map<std::string, std::size_t> quad_index_;
    std::vector<std::string> n_rows_;
    std::string rhs_vector_;
    std::string range_vector_;
    std::string bound_vector_;
    std::unordered_set<std::string> ignored_rhs_vectors_;
    std::unordered_set<std::string> ignored_range_vectors_;
    std::unordered_set<std::string> ignored_bound_vectors_;
    bool saw_endata_ = false;
    // A segmented container avoids the old+new contiguous buffers of vector
    // growth on multi-million-row instances, while preserving indexed lookup.
    std::deque<Row> rows_;
    std::unordered_map<std::string, std::size_t> row_index_;
    // Column IDs are stable indices, so segmented storage also avoids the
    // transient old+new buffers of vector growth on wide matrices.
    std::deque<Col> cols_;
    std::unordered_map<std::string, std::size_t> col_index_;
    std::unordered_map<std::string, std::size_t> coefficient_index_;
    std::vector<const std::string*> coefficient_text_;
    mutable std::vector<H::ExprPtr> coefficient_nodes_;
    // Leaves are immutable and scoped to this model. Constraint roots retain
    // their own row locations even when coefficients and symbols are shared.
    mutable std::unordered_map<std::string, H::ExprPtr> numbers_;
    mutable std::unordered_map<std::string, H::ExprPtr> symbols_;
    mutable std::unordered_map<std::string, H::ExprPtr> negatives_;
};

/** Exact decimal addition, so a RANGES interval is not perturbed by a double.
 *  Both operands come from the file; the second may carry a leading `-`. */
std::string MpsParser::halveDecimal(const std::string& v) {
    std::string t = plainDecimal(v);
    std::string sign;
    if (!t.empty() && (t[0] == '+' || t[0] == '-')) {
        if (t[0] == '-') { sign = "-"; }
        t.erase(0, 1);
    }
    const std::size_t dot = t.find('.');
    std::string digits = dot == std::string::npos ? t : t.substr(0, dot) + t.substr(dot + 1);
    std::size_t frac = dot == std::string::npos ? 0 : t.size() - dot - 1;

    // Long division by two over the digit string. A trailing remainder adds
    // one fractional digit -- 1 becomes 0.5 -- and never more, so this
    // terminates after a single extra place.
    std::string out;
    int rem = 0;
    for (char c : digits) {
        const int cur = rem * 10 + (c - '0');
        out.push_back(static_cast<char>('0' + cur / 2));
        rem = cur % 2;
    }
    if (rem != 0) { out.push_back('5'); ++frac; }

    std::string ip = frac >= out.size() ? "0" : out.substr(0, out.size() - frac);
    std::string fp = frac == 0 ? "" : out.substr(out.size() - frac);
    if (frac > out.size()) { fp.insert(0, frac - out.size(), '0'); }
    const std::size_t nz = ip.find_first_not_of('0');
    ip = nz == std::string::npos ? "0" : ip.substr(nz);
    while (!fp.empty() && fp.back() == '0') { fp.pop_back(); }
    if (ip == "0" && fp.empty()) { return "0"; }
    return sign + ip + (fp.empty() ? "" : "." + fp);
}

std::string MpsParser::addDecimals(const std::string& a, const std::string& b) {
    const auto split = [](const std::string& s, bool& neg, std::string& ip,
                          std::string& fp) {
        std::string t = s;
        neg = false;
        if (!t.empty() && (t[0] == '+' || t[0] == '-')) { neg = (t[0] == '-'); t.erase(0, 1); }
        const std::size_t dot = t.find('.');
        ip = dot == std::string::npos ? t : t.substr(0, dot);
        fp = dot == std::string::npos ? "" : t.substr(dot + 1);
        if (ip.empty()) { ip = "0"; }
    };
    bool na = false, nb = false;
    std::string ia, fa, ib, fb;
    split(a, na, ia, fa);
    split(b, nb, ib, fb);
    const std::size_t scale = std::max(fa.size(), fb.size());
    fa.append(scale - fa.size(), '0');
    fb.append(scale - fb.size(), '0');
    // Compare and add/subtract as digit strings.
    const auto cmp = [](const std::string& x, const std::string& y) {
        const std::string xs = x.substr(std::min(x.find_first_not_of('0'), x.size() - 1));
        const std::string ys = y.substr(std::min(y.find_first_not_of('0'), y.size() - 1));
        if (xs.size() != ys.size()) { return xs.size() < ys.size() ? -1 : 1; }
        return xs < ys ? -1 : (xs == ys ? 0 : 1);
    };
    const auto add = [](std::string x, std::string y) {
        std::string out;
        int carry = 0;
        int i = static_cast<int>(x.size()) - 1, j = static_cast<int>(y.size()) - 1;
        while (i >= 0 || j >= 0 || carry) {
            int d = carry;
            if (i >= 0) { d += x[static_cast<std::size_t>(i--)] - '0'; }
            if (j >= 0) { d += y[static_cast<std::size_t>(j--)] - '0'; }
            out.push_back(static_cast<char>('0' + d % 10));
            carry = d / 10;
        }
        std::reverse(out.begin(), out.end());
        return out;
    };
    const auto sub = [](std::string x, std::string y) {
        std::string out;
        int borrow = 0;
        int i = static_cast<int>(x.size()) - 1, j = static_cast<int>(y.size()) - 1;
        while (i >= 0) {
            int d = (x[static_cast<std::size_t>(i--)] - '0') - borrow;
            if (j >= 0) { d -= y[static_cast<std::size_t>(j--)] - '0'; }
            borrow = d < 0 ? 1 : 0;
            if (d < 0) { d += 10; }
            out.push_back(static_cast<char>('0' + d));
        }
        std::reverse(out.begin(), out.end());
        return out;
    };
    const std::string x = ia + fa, y = ib + fb;
    std::string digits;
    bool neg = false;
    if (na == nb) { digits = add(x, y); neg = na; }
    else if (cmp(x, y) >= 0) { digits = sub(x, y); neg = na; }
    else { digits = sub(y, x); neg = nb; }
    if (scale > 0) {
        if (digits.size() <= scale) { digits.insert(0, scale - digits.size() + 1, '0'); }
        digits.insert(digits.size() - scale, ".");
    }
    const std::size_t nz = digits.find_first_not_of('0');
    if (nz != std::string::npos && digits[nz] == '.') {
        digits = "0" + digits.substr(nz);
    } else if (nz != std::string::npos) {
        digits = digits.substr(nz);
    } else {
        digits = "0";
    }
    if (digits.find('.') != std::string::npos) {
        while (!digits.empty() && digits.back() == '0') { digits.pop_back(); }
        if (!digits.empty() && digits.back() == '.') { digits.pop_back(); }
    }
    if (digits.empty()) { digits = "0"; }
    return (neg && digits != "0") ? "-" + digits : digits;
}

class MpsLanguage : public Language {
public:
    MpsLanguage() {
        // NAME, OBJSENSE, ROWS, COLUMNS with markers, RHS, RANGES, BOUNDS,
        // and the quadratic objective sections. SOS and INDICATORS are
        // refused.
        // `total` grew with `supported`: implementing quadratic OBJECTIVES is
        // what revealed quadratic CONSTRAINTS as a construct of its own
        // (`QSECTION` names its row, and it need not be the objective). A
        // table that had only moved the gap into the supported column would
        // report the ratio improving by forgetting something.
        coverage_.total = 11;
        coverage_.supported = 8;
        coverage_.missing = {
            "SOS",
            // Quadratic OBJECTIVES landed 2026-09-20 (QUADOBJ, QMATRIX and
            // QSECTION naming the objective row). What is left is a quadratic
            // CONSTRAINT -- `QSECTION <row>` naming anything else -- which is
            // a different construct and refused by name, not by silence.
            "quadratic CONSTRAINTS (`QSECTION` naming a row other than the "
            "objective); quadratic objectives are supported",
            "INDICATORS",
        };
    }

    std::string id() const override { return "mps"; }
    std::string displayName() const override { return "MPS"; }
    std::string version() const override { return "free-form"; }
    std::vector<std::string> extensions() const override { return {".mps"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& options) override {
        ParseOutcome out;
        const auto recovery = options.options.find("highs_warning_recovery");
        if (recovery != options.options.end() && recovery->second != "0" && recovery->second != "1") {
            out.diagnostics.error(ErrorCode::E_PARSE, "highs_warning_recovery must be 0 or 1");
            return out;
        }
        const bool highs_recovery = recovery != options.options.end() && recovery->second == "1";
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
        const char* allocation_stage = "parser setup";
        try {
            {
                MpsParser p(*input, name, highs_recovery, &allocation_stage);
                out.model = p.parse(out.diagnostics, out.report);
            }
            if (out.model) {
                allocation_stage = "source semantic contract";
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "mps", out.report.fidelity()));
            }
        } catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                                  std::string("mps frontend: memory allocation failed during ")
                                      + allocation_stage);
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("mps frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkMpsLanguage() { return std::make_shared<MpsLanguage>(); }

} // namespace SOMTParser::Lang
