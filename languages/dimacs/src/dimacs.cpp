/* -*- Source -*-
 * DIMACS CNF frontend.
 *
 * The format is docs/languages/dimacs-cnf.md; its `implicit-constraints` block
 * is the specification this file implements, and each entry has a fixture in
 * languages/dimacs/instances.
 *
 * Read the first obligation beside the other two QBF-adjacent frontends,
 * because the three formats define "the file's vocabulary" three different ways
 * and a shared code path would take one of them:
 *
 *     DIMACS    the HEADER. `p cnf V C` declares variables 1..V, whether or not
 *               a clause mentions them.
 *     QDIMACS   the PREFIX. A matrix variable not quantified there is a
 *               malformed instance.
 *     QCIR      the GATES. A variable nothing quantifies is free by default.
 *
 * test/languages/test_sat_cross_format.cpp asserts the three apart.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/dimacs.h"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <cstdlib>
#include <cstdint>
#include <istream>
#include <filesystem>
#include <fstream>
#include <new>
#include <limits>
#include <memory>
#include <sstream>
#include <string>
#include <system_error>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

std::string varName(long long v) { return "x" + std::to_string(v); }

/** A non-negative decimal weight, as written. Kept as TEXT because a weight is
 *  exact data and a double would round it.
 *
 *  Non-negative is enforced, not merely documented: a model count is a sum of
 *  weights over satisfying assignments, and a negative weight makes that sum
 *  something other than a count. A leading `+` is allowed because it is a
 *  spelling of the same number. */
bool isDecimal(const std::string& s) {
    if (s.empty()) { return false; }
    std::size_t i = (s[0] == '+') ? 1 : 0;
    bool digits = false, dot = false;
    for (; i < s.size(); ++i) {
        if (std::isdigit(static_cast<unsigned char>(s[i])) != 0) { digits = true; }
        else if (s[i] == '.' && !dot) { dot = true; }
        else { return false; }
    }
    return digits;
}

class DimacsParser {
public:
    DimacsParser(std::istream& source, std::string file, bool strict, bool packed)
        : source_(source), file_(std::move(file)), strict_(strict), packed_(packed) {
        batch_.source_file = file_;
    }

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        report_ = &report;
        if (!read(diags)) { return nullptr; }
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

    /** from_chars rather than stoll: an oversized literal in a benchmark is an
     *  input problem with a line number, not an exception escaping into the
     *  frontend's blanket handler where it would be filed as E_INTERNAL -- the
     *  bucket translation/diagnostic.h reserves for broken invariants. */
    static bool toInt(const std::string& tok, long long& out) {
        if (tok.empty()) { return false; }
        const char* first = tok.data();
        const char* last = first + tok.size();
        const auto conv = std::from_chars(first, last, out);
        return conv.ec == std::errc() && conv.ptr == last;
    }

    bool read(Uir::Diagnostics& diags) {
        std::istream& in = source_;
        std::string raw;
        int lineno = 0;
        bool seen_p = false;
        std::vector<long long> clause;
        int clause_line = 0;
        const auto clause_empty = [&]() {
            return packed_ ? batch_.literals.size() == batch_.clause_offsets.back()
                           : clause.empty();
        };

        while (std::getline(in, raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            std::istringstream head(raw);
            std::string first;
            if (!(head >> first)) { continue; }        // blank
            // A comment is a line whose FIRST CHARACTER is `c`. The space
            // after it is conventional, not required: the MaxSAT Evaluation's
            // own standardised instances open with `c{` and continue
            // `c "sha1sum": ...`, a JSON block written one line at a time with
            // no separator. Splitting on whitespace and comparing the first
            // TOKEN to "c" refuses every one of them -- 10 of the 25 files in
            // the vendored corpus, each reported as malformed input when the
            // file is well formed and the reader is not.
            // Only the exact token `c` can introduce a `c p`/`c t` directive,
            // because those are defined with the separator; `c{` is prose.
            if (first.size() > 1 && first[0] == 'c') { continue; }
            if (first == "c") {
                // A comment -- except that the Model Counting Competition puts
                // its weights and projection scope in `c p …` and its track in
                // `c t …`. Dropping those made a weighted instance translate
                // as an unweighted one, in silence.
                std::string second;
                if (!(head >> second)) { continue; }     // bare `c`
                if (second == "t") {
                    std::string track;
                    if (head >> track) {
                        counting_track_ = track;
                        track_line_ = lineno;
                    }
                    continue;
                }
                if (second != "p") { continue; }         // ordinary prose
                std::string directive;
                if (!(head >> directive)) { continue; }
                if (directive == "weight") {
                    long long lit = 0;
                    std::string w;
                    if (!(head >> lit) || !(head >> w)) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a `c p weight` line is `c p weight <lit> <w> 0`",
                                    at(lineno));
                        return false;
                    }
                    if (!isDecimal(w)) {
                        diags.error(ErrorCode::E_PARSE,
                                    "'" + w + "' is not a weight", at(lineno));
                        return false;
                    }
                    // The terminating 0 is part of the line's grammar, and
                    // anything after it is a token this reader does not
                    // understand. Checking it is the difference between
                    // reading the line and reading the first three fields of
                    // it -- which is the same shortcut that lost the weights.
                    long long terminator = 0;
                    std::string extra;
                    if (!(head >> terminator) || terminator != 0) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a `c p weight` line must end with 0",
                                    at(lineno));
                        return false;
                    }
                    if (head >> extra) {
                        diags.error(ErrorCode::E_PARSE,
                                    "unexpected '" + extra
                                        + "' after the end of a `c p weight` line",
                                    at(lineno));
                        return false;
                    }
                    counting_weights_.emplace_back(lit, w);
                    continue;
                }
                if (directive == "show") {
                    // `>>` into a long long fails on a non-numeric token and
                    // leaves the stream bad, so the loop below would simply
                    // END on `c p show 1 2 x 0` -- silently keeping {1, 2} and
                    // dropping both the bad token and the missing terminator.
                    std::string token;
                    bool terminated = false;
                    while (head >> token) {
                        if (terminated) {
                            // E_PARSE, not E_UNSUPPORTED_CONSTRUCT: text
                            // after a line's terminating 0 is malformed
                            // input, not a construct this reader has yet to
                            // learn. The two feed different statistics.
                            diags.error(
                                ErrorCode::E_PARSE,
                                "unexpected '" + token
                                    + "' after the end of a `c p show` line",
                                at(lineno));
                            return false;
                        }
                        char* stop = nullptr;
                        const long long v = std::strtoll(token.c_str(), &stop, 10);
                        if (stop == token.c_str() || *stop != '\0') {
                            diags.error(ErrorCode::E_PARSE,
                                        "'" + token
                                            + "' is not a variable in a `c p show` line",
                                        at(lineno));
                            return false;
                        }
                        if (v == 0) { terminated = true; continue; }
                        counting_scope_.push_back(v);
                    }
                    if (!terminated) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a `c p show` line must end with 0", at(lineno));
                        return false;
                    }
                    continue;
                }
                // Unrecognised. Refused by name rather than ignored: a
                // directive this reader does not know may change what is being
                // asked, and ignoring it is exactly how the weights were lost.
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "unknown counting directive `c p " + directive
                                + "`; this reader knows `weight` and `show`",
                            at(lineno));
                return false;
            }
            if (first == "p") {
                if (seen_p) {
                    diags.error(ErrorCode::E_PARSE, "more than one problem line",
                                at(lineno));
                    return false;
                }
                std::string fmt, vs, cs;
                long long v = 0, c = 0;
                if (!(head >> fmt) || fmt != "cnf") {
                    diags.error(ErrorCode::E_PARSE,
                                "the problem line must read `p cnf V C`", at(lineno));
                    return false;
                }
                if (!(head >> vs) || !(head >> cs) || !toInt(vs, v) || !toInt(cs, c)
                    || v < 0 || c < 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "the problem line's counts are not numbers", at(lineno));
                    return false;
                }
                declared_vars_ = v;
                declared_clauses_ = c;
                seen_p = true;
                p_line_ = lineno;
                continue;
            }
            if (!seen_p) {
                diags.error(ErrorCode::E_PARSE, "content before the problem line",
                            at(lineno));
                return false;
            }
            // A clause. Literals may span lines up to the terminating 0.
            if (clause_empty()) { clause_line = lineno; }
            std::istringstream ls(raw);
            std::string tok;
            while (ls >> tok) {
                long long v = 0;
                if (!toInt(tok, v)) {
                    diags.error(ErrorCode::E_PARSE, "'" + tok + "' is not a literal",
                                at(lineno));
                    return false;
                }
                if (v == 0) {
                    if (packed_) {
                        batch_.clause_offsets.push_back(batch_.literals.size());
                        batch_.weight_offsets.push_back(0); // all DIMACS clauses are hard
                        batch_.source_lines.push_back(static_cast<std::uint32_t>(clause_line));
                    } else {
                        clauses_.emplace_back(std::move(clause), clause_line);
                        clause = std::vector<long long>{};
                    }
                    clause_line = lineno;
                    continue;
                }
                if (v == std::numeric_limits<long long>::min()) {
                    diags.error(ErrorCode::E_PARSE,
                                "the magnitude of this literal cannot be represented",
                                at(lineno));
                    return false;
                }
                largest_ = std::max(largest_, std::llabs(v));
                if (packed_) { batch_.literals.push_back(v); }
                else { clause.push_back(v); }
            }
        }
        if (source_.bad()) {
            diags.error(ErrorCode::E_IO, "failed reading DIMACS source", at(std::max(1, lineno)));
            return false;
        }
        if (!seen_p) {
            diags.error(ErrorCode::E_PARSE, "the file has no problem line", at(1));
            return false;
        }
        if (!clause_empty()) {
            diags.error(ErrorCode::E_PARSE, "the last clause is not terminated by 0",
                        at(clause_line));
            return false;
        }
        return true;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags) {
        auto model = std::make_shared<H::ConstraintModel>();

        const long long largest = largest_;
        const std::size_t clause_count = packed_ ? batch_.source_lines.size() : clauses_.size();

        // §4.2's mismatch policy: trust the CONTENT and warn.
        //
        // Trusting the header and stopping after C clauses would silently drop
        // constraints, making the translated problem *weaker* -- sound = false,
        // a wrong answer reported as success. The asymmetry the document draws
        // matters: an over-large VARIABLES is harmless (extra free variables,
        // and see below), an over-small CLAUSES is not.
        if (static_cast<long long>(clause_count) != declared_clauses_) {
            const std::string msg =
                "the problem line declares " + std::to_string(declared_clauses_)
                + " clauses but the file has " + std::to_string(clause_count);
            if (strict_) {
                diags.error(ErrorCode::E_PARSE, msg, at(p_line_));
                return nullptr;
            }
            diags.warn(ErrorCode::E_PARSE, msg, at(p_line_));
        }
        if (largest > declared_vars_) {
            const std::string msg =
                "the problem line declares " + std::to_string(declared_vars_)
                + " variables but index " + std::to_string(largest) + " is used";
            if (strict_) {
                diags.error(ErrorCode::E_PARSE, msg, at(p_line_));
                return nullptr;
            }
            diags.warn(ErrorCode::E_PARSE, msg, at(p_line_));
        }

        // `c t <track>` is the Model Counting Competition's own label for which
        // track an instance was submitted to, and each track implies which
        // `c p …` directives should accompany it. This is a WARNING, not a
        // refusal: the track is advisory metadata about the question being
        // asked of the instance, and the formula built below is well defined
        // regardless of whether the label and the directives agree -- refusing
        // the file would reject a valid instance over a mislabelled header,
        // the same asymmetry as the declared/actual checks just above. Uses
        // E_PARSE, the same code those checks use, because this is the same
        // kind of defect: declared metadata that disagrees with the content
        // actually read.
        if (!counting_track_.empty()) {
            const bool has_weight = !counting_weights_.empty();
            const bool has_scope = !counting_scope_.empty();
            bool expect_weight = false;
            bool expect_scope = false;
            bool known_track = true;
            if (counting_track_ == "mc") {
                expect_weight = false;
                expect_scope = false;
            } else if (counting_track_ == "wmc") {
                expect_weight = true;
                expect_scope = false;
            } else if (counting_track_ == "pmc") {
                expect_weight = false;
                expect_scope = true;
            } else if (counting_track_ == "pwmc") {
                expect_weight = true;
                expect_scope = true;
            } else {
                known_track = false;
            }
            if (!known_track) {
                diags.warn(ErrorCode::E_PARSE,
                           "'c t " + counting_track_
                               + "' is not a track this reader knows (mc, wmc, "
                                 "pmc, pwmc)",
                           at(track_line_));
            } else {
                if (expect_weight && !has_weight) {
                    diags.warn(ErrorCode::E_PARSE,
                               "'c t " + counting_track_
                                   + "' declares a weighted track but the file "
                                     "has no 'c p weight' line",
                               at(track_line_));
                } else if (!expect_weight && has_weight) {
                    diags.warn(ErrorCode::E_PARSE,
                               "'c t " + counting_track_
                                   + "' does not declare a weighted track but "
                                     "the file has a 'c p weight' line",
                               at(track_line_));
                }
                if (expect_scope && !has_scope) {
                    diags.warn(ErrorCode::E_PARSE,
                               "'c t " + counting_track_
                                   + "' declares a projected track but the file "
                                     "has no 'c p show' line",
                               at(track_line_));
                } else if (!expect_scope && has_scope) {
                    diags.warn(ErrorCode::E_PARSE,
                               "'c t " + counting_track_
                                   + "' does not declare a projected track but "
                                     "the file has a 'c p show' line",
                               at(track_line_));
                }
            }
        }

        // The first obligation: **the file's vocabulary is the HEADER's, not the
        // clauses'.** A variable in 1..V occurring in no clause is still a
        // VarDecl -- it is a variable of the problem that happens to be
        // unconstrained, and dropping it would report a smaller instance than
        // the file describes.
        //
        // QDIMACS calls the same situation legal for the opposite reason (the
        // prefix binds it) and calls the *converse* -- a clause variable the
        // header does not cover -- malformed. Here the converse is only a
        // warning, because an under-counting VARIABLES loses nothing: the
        // variable is declared anyway, from the content.
        const long long n = std::max(declared_vars_, largest);
        if (packed_) {
            // The header still declares every variable, including unused ones.
            // Preserve signed literals and clause boundaries without allocating
            // a separate expression or declaration object for each occurrence.
            model->bool_var_ranges.push_back({"x", 1, static_cast<std::uint64_t>(n),
                                               H::Sort::boolean(), at(p_line_)});
            model->packed_bool_clauses.push_back(std::move(batch_));
        } else {
            model->decls.reserve(static_cast<std::size_t>(n));
            model->constraints.reserve(clauses_.size());
            // DIMACS literals are immutable and only depend on variable index and
            // sign. Cache literal nodes lazily so unused header variables allocate
            // declarations but no expression nodes. Clause and constraint nodes
            // below retain their own source locations.
            // A literal node's location is the header line, where its variable
            // vocabulary was declared. Literal sorts are always Bool, so this does
            // not weaken any source type diagnostic.
            std::vector<H::ExprPtr> positive(static_cast<std::size_t>(n) + 1);
            std::vector<H::ExprPtr> negative(static_cast<std::size_t>(n) + 1);
            for (long long v = 1; v <= n; ++v) {
                H::VarDecl d;
                d.name = varName(v);
                d.sort = H::Sort::boolean();
                d.loc = at(p_line_);
                model->decls.push_back(d);
            }

            // §3: one Constraint per clause. The implicit conjunction over
            // ConstraintModel::constraints is exactly right here -- unlike QDIMACS,
            // where a prefix has to scope over the whole matrix and the model
            // therefore holds one constraint (qdimacs.md §4.2).
            for (const auto& [lits, line] : clauses_) {
                std::vector<H::ExprPtr> disjuncts;
                disjuncts.reserve(lits.size());
                for (long long l : lits) {
                    const std::size_t variable =
                        static_cast<std::size_t>(std::llabs(l));
                    if (!positive[variable]) {
                        positive[variable] = H::mkIdent(
                            varName(static_cast<long long>(variable)),
                            H::Sort::boolean(), at(p_line_));
                    }
                    if (l < 0 && !negative[variable]) {
                        negative[variable] = H::mkOp(
                            H::Op::NOT, {positive[variable]}, at(p_line_));
                    }
                    disjuncts.push_back(l < 0 ? negative[variable] : positive[variable]);
                }
                H::Constraint c;
                c.loc = at(line);
                if (disjuncts.empty()) {
                    // §4.1: the empty clause is FALSE, and mkOp(OR, {}) THROWS
                    // rather than producing it -- condAssert survives -DNDEBUG, so
                    // this is not a debug-only trap. An uncaught one on a legal
                    // input would be filed as E_INTERNAL, i.e. under the wrong
                    // bucket of the failure-cause breakdown.
                    c.formula = H::mkBool(false, at(line));
                } else if (disjuncts.size() == 1) {
                    c.formula = disjuncts.front();
                } else {
                    c.formula = H::mkOp(H::Op::OR, std::move(disjuncts), at(line));
                }
                model->constraints.push_back(c);
            }
        }
        // No objectives: `preserves_optimum` is vacuously true and not
        // "verified preserved", which is the third obligation and a statement
        // about how the fidelity should be read rather than about the code.

        // Counting data is recorded, not encoded: the SMT body above is the
        // plain unweighted/unprojected formula regardless, because a weighted
        // or projected count is a question the counter answers, not a change
        // to the constraint model itself.
        if (!counting_weights_.empty()) {
            Uir::EncodingChoice ch;
            ch.site = file_;
            ch.unified_op = "model-counting";
            ch.strategy = "counting-weights";
            ch.fidelity = Uir::Fidelity::exact();
            std::string listed;
            for (const auto& [lit, w] : counting_weights_) {
                if (!listed.empty()) { listed += " "; }
                listed += std::to_string(lit) + "=" + w;
            }
            ch.rationale =
                "the instance declares literal weights (" + listed
                + "); they are recorded rather than dropped, but the emitted "
                  "SMT body is the unweighted formula -- a weighted count is a "
                  "question for the counter, not a change to the model";
            report_->addChoice(std::move(ch));
        }
        if (!counting_scope_.empty()) {
            Uir::EncodingChoice ch;
            ch.site = file_;
            ch.unified_op = "model-counting";
            ch.strategy = "counting-projection";
            ch.fidelity = Uir::Fidelity::exact();
            ch.rationale =
                "the instance projects its count onto "
                + std::to_string(counting_scope_.size())
                + " variable(s); the scope is the question's, not an artefact "
                  "of translation, and is passed to the counter unchanged";
            report_->addChoice(std::move(ch));
        }
        return model;
    }

    std::istream& source_;
    std::string file_;
    bool        strict_ = false;
    bool        packed_ = false;
    long long   largest_ = 0;
    H::PackedBoolClauseBatch batch_{0, {}, {0}, {}, {0}, {}, {}};

    long long declared_vars_ = 0;
    long long declared_clauses_ = 0;
    int       p_line_ = 1;
    std::vector<std::pair<std::vector<long long>, int>> clauses_;

    /** Model Counting Competition data, read from `c t` / `c p …` lines.
     *  Empty for an ordinary SAT instance, which is what an MC-track file
     *  also is -- the track is a statement about the question, not the file. */
    std::string counting_track_;
    int         track_line_ = 1;
    std::vector<std::pair<long long, std::string>> counting_weights_;
    std::vector<long long> counting_scope_;

    Uir::TranslationReport* report_ = nullptr;   // set by parse(), never null after
};

class DimacsLanguage : public Language {
public:
    DimacsLanguage() {
        // The problem line, clauses, comments, the empty clause, and now the
        // Model Counting Competition's `c t` / `c p weight|show` headers.
        // Both counters rise together: the headers are read and recorded
        // (EncodingChoice), not merely tolerated, so this is a supported
        // construct rather than a gap `missing` should list.
        coverage_.total = 5;
        coverage_.supported = 5;
    }

    std::string id() const override { return "dimacs"; }
    std::string displayName() const override { return "DIMACS CNF"; }
    std::string version() const override { return "cnf"; }
    std::vector<std::string> extensions() const override { return {".cnf", ".dimacs"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) override {
        ParseOutcome out;
        bool packed = false;
        if (const auto option = opts.options.find("packed"); option != opts.options.end()) {
            if (option->second != "0" && option->second != "1") {
                out.diagnostics.error(ErrorCode::E_PARSE,
                                      "DIMACS option 'packed' must be '0' or '1'");
                return out;
            }
            packed = option->second == "1";
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            const auto read = [&](std::istream& source) {
                DimacsParser parser(source, name, opts.strict, packed);
                out.model = parser.parse(out.diagnostics, out.report);
            };
            if (!unit.inline_source.empty()) {
                std::istringstream source(unit.inline_source);
                read(source);
            } else {
                std::error_code ec;
                if (std::filesystem::is_directory(unit.main_path, ec)) {
                    out.diagnostics.error(ErrorCode::E_IO,
                                          "'" + unit.main_path + "' is a directory");
                    return out;
                }
                std::ifstream source(unit.main_path, std::ios::binary);
                if (!source) {
                    out.diagnostics.error(ErrorCode::E_IO,
                                          "cannot open '" + unit.main_path + "'");
                    return out;
                }
                read(source);
            }
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "dimacs", out.report.fidelity()));
            }
        } catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                                  "dimacs frontend: memory allocation failed");
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("dimacs frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkDimacsLanguage() { return std::make_shared<DimacsLanguage>(); }

} // namespace SOMTParser::Lang
