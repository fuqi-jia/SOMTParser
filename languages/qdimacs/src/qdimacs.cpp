/* -*- Source -*-
 * QDIMACS 1.1 frontend.
 *
 * The format is docs/languages/qdimacs.md, written from the standard before any
 * of this existed; its `implicit-constraints` block is the specification this
 * file implements, and each entry has a fixture in
 * languages/qdimacs/instances.
 *
 * QDIMACS 1.1 Input format, third additional constraint, gives matrix variables
 * absent from the prefix an implicit OUTERMOST existential quantifier. This
 * preserves DIMACS compatibility. Placing them inside a universal block would
 * instead give them additional dependencies and can change the truth value.
 * QCIR leaves its unquantified non-gate variables free; the cross-format test
 * distinguishes the resulting HIR binding structure.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/qdimacs.h"

#include <cctype>
#include <charconv>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <limits>
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

/** One prefix block, in file order. */
struct Block {
    bool                  forall = false;
    std::vector<long long> vars;
    int                   line = 0;
};

std::string varName(long long v) { return "x" + std::to_string(v); }

class QdimacsParser {
public:
    QdimacsParser(std::string src, std::string file, bool strict)
        : src_(std::move(src)), file_(std::move(file)), strict_(strict) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags) {
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

    /** Read a whitespace-separated integer, refusing one that does not fit.
     *
     *  from_chars rather than stoll: an out-of-range literal in a benchmark is
     *  an input problem with a line number, not an exception escaping into the
     *  frontend's blanket handler where it would be filed as E_INTERNAL. */
    static bool toInt(const std::string& tok, long long& out) {
        if (tok.empty()) { return false; }
        const char* first = tok.data();
        const char* last = first + tok.size();
        const auto conv = std::from_chars(first, last, out);
        return conv.ec == std::errc() && conv.ptr == last;
    }

    bool read(Uir::Diagnostics& diags) {
        std::istringstream in(src_);
        std::string raw;
        int lineno = 0;
        bool seen_p = false;
        bool in_matrix = false;
        std::vector<long long> clause;
        int clause_line = 0;

        while (std::getline(in, raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            std::istringstream ls(raw);
            std::string first;
            if (!(ls >> first)) { continue; }         // blank
            if (first == "c") { continue; }           // comment
            if (first == "p") {
                if (seen_p) {
                    diags.error(ErrorCode::E_PARSE, "more than one problem line",
                                at(lineno));
                    return false;
                }
                std::string fmt;
                long long v = 0, c = 0;
                if (!(ls >> fmt) || fmt != "cnf") {
                    diags.error(ErrorCode::E_PARSE,
                                "the problem line must read `p cnf V C`", at(lineno));
                    return false;
                }
                std::string vs, cs;
                if (!(ls >> vs) || !(ls >> cs) || !toInt(vs, v) || !toInt(cs, c)
                    || v < 0 || c < 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "the problem line's counts are not numbers", at(lineno));
                    return false;
                }
                std::string extra;
                if (ls >> extra) {
                    diags.error(ErrorCode::E_PARSE,
                                "unexpected token after problem-line counts: '" + extra + "'",
                                at(lineno));
                    return false;
                }
                declared_vars_ = v;
                declared_clauses_ = c;
                seen_p = true;
                p_line_ = lineno;
                continue;
            }
            if (!seen_p) {
                diags.error(ErrorCode::E_PARSE,
                            "content before the problem line", at(lineno));
                return false;
            }
            if ((first == "a" || first == "e") && !in_matrix) {
                // §2.3: the prefix precedes the matrix. A quantifier line after
                // a clause is not a late block, it is a malformed file -- and
                // accepting it would silently change the nesting.
                Block b;
                b.forall = (first == "a");
                b.line = lineno;
                std::string tok;
                bool terminated = false;
                while (ls >> tok) {
                    long long v = 0;
                    if (!toInt(tok, v)) {
                        diags.error(ErrorCode::E_PARSE,
                                    "'" + tok + "' is not a variable index", at(lineno));
                        return false;
                    }
                    if (v == 0) { terminated = true; break; }
                    if (v < 0) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a quantifier block lists variables, not literals; "
                                    "'" + tok + "' is negated",
                                    at(lineno));
                        return false;
                    }
                    b.vars.push_back(v);
                }
                if (!terminated) {
                    diags.error(ErrorCode::E_PARSE,
                                "a quantifier block must end with 0", at(lineno));
                    return false;
                }
                if (ls >> tok) {
                    diags.error(ErrorCode::E_PARSE,
                                "unexpected token after quantifier-block terminator: '" + tok + "'",
                                at(lineno));
                    return false;
                }
                if (b.vars.empty()) {
                    // An empty block binds nothing but still separates the
                    // blocks around it, which would change the alternation
                    // count if it were kept. It is not legal QDIMACS.
                    diags.error(ErrorCode::E_PARSE,
                                "a quantifier block is empty", at(lineno));
                    return false;
                }
                blocks_.push_back(std::move(b));
                continue;
            }
            // A clause. Literals may span lines up to the terminating 0.
            in_matrix = true;
            if (clause.empty()) { clause_line = lineno; }
            std::string tok;
            ls.clear();
            ls.str(raw);
            while (ls >> tok) {
                long long v = 0;
                // Every literal's absolute value must fit the variable-index
                // type. Negating LLONG_MIN (including via llabs) is undefined.
                if (!toInt(tok, v) || v == std::numeric_limits<long long>::min()) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + tok + "' is not a literal", at(lineno));
                    return false;
                }
                if (v == 0) {
                    clauses_.push_back({clause, clause_line});
                    clause.clear();
                    clause_line = lineno;
                    continue;
                }
                clause.push_back(v);
            }
        }
        if (!seen_p) {
            diags.error(ErrorCode::E_PARSE, "the file has no problem line", at(1));
            return false;
        }
        if (!clause.empty()) {
            diags.error(ErrorCode::E_PARSE, "the last clause is not terminated by 0",
                        at(clause_line));
            return false;
        }
        return true;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags) {
        auto model = std::make_shared<H::ConstraintModel>();

        // §2.3: a variable may not be quantified twice.
        std::unordered_map<long long, int> owner;
        for (const auto& b : blocks_) {
            for (long long v : b.vars) {
                const auto it = owner.find(v);
                if (it != owner.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "variable " + std::to_string(v)
                                    + " is quantified twice (also on line "
                                    + std::to_string(it->second) + ")",
                                at(b.line));
                    return nullptr;
                }
                owner[v] = b.line;
            }
        }

        // QDIMACS 1.1 explicitly permits matrix variables absent from the
        // prefix. Collect them once, in first-occurrence order, and bind them
        // outside every universal. Never append them to an inner existential
        // block: that would introduce dependencies not present in the source.
        std::vector<long long> implicit_exists;
        for (const auto& [lits, line] : clauses_) {
            for (long long l : lits) {
                const long long v = std::llabs(l);
                if (owner.emplace(v, line).second) {
                    implicit_exists.push_back(v);
                }
            }
        }
        if (!implicit_exists.empty()) {
            if (!blocks_.empty() && !blocks_.front().forall) {
                auto& outer = blocks_.front().vars;
                outer.insert(outer.end(), implicit_exists.begin(), implicit_exists.end());
            } else {
                blocks_.insert(blocks_.begin(), Block{false, std::move(implicit_exists), p_line_});
            }
        }

        // §4.2's mismatch policy, inherited from dimacs-cnf.md §4.2: trust the
        // content and warn. Trusting the header would silently drop clauses,
        // which makes the translated problem *weaker* -- a wrong answer reported
        // as success. Under ParseOptions::strict it is a refusal instead.
        if (static_cast<long long>(clauses_.size()) != declared_clauses_) {
            const std::string msg =
                "the problem line declares " + std::to_string(declared_clauses_)
                + " clauses but the file has " + std::to_string(clauses_.size());
            if (strict_) {
                diags.error(ErrorCode::E_PARSE, msg, at(p_line_));
                return nullptr;
            }
            diags.warn(ErrorCode::E_PARSE, msg, at(p_line_));
        }
        long long largest = 0;
        for (const auto& [v, line] : owner) { largest = std::max(largest, v); }
        for (const auto& [lits, line] : clauses_) {
            for (long long l : lits) { largest = std::max(largest, std::llabs(l)); }
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

        // §4.2: the matrix is ONE constraint. The prefix scopes over the whole
        // conjunction, so a model with one Constraint per clause would wrap each
        // clause in its own prefix -- a formula that is not merely different but
        // usually much easier.
        std::vector<H::ExprPtr> conjuncts;
        conjuncts.reserve(clauses_.size());
        for (const auto& [lits, line] : clauses_) {
            std::vector<H::ExprPtr> disjuncts;
            disjuncts.reserve(lits.size());
            for (long long l : lits) {
                H::ExprPtr v = H::mkBoundVar(varName(std::llabs(l)),
                                             H::Sort::boolean(), at(line));
                disjuncts.push_back(l < 0 ? H::mkOp(H::Op::NOT, {v}, at(line)) : v);
            }
            if (disjuncts.empty()) {
                // The empty clause is FALSE, and it is the trap
                // dimacs-cnf.md §4.1 records: mkOp throws on an empty argument
                // list rather than inventing an identity, so this must be a
                // branch. An instance containing one is unsatisfiable, which is
                // an answer and a legal file.
                conjuncts.push_back(H::mkBool(false, at(line)));
            } else if (disjuncts.size() == 1) {
                conjuncts.push_back(disjuncts.front());
            } else {
                conjuncts.push_back(H::mkOp(H::Op::OR, std::move(disjuncts), at(line)));
            }
        }
        H::ExprPtr matrix;
        if (conjuncts.empty()) {
            // No clauses: the empty conjunction is TRUE. The opposite polarity
            // from the empty clause, and the pair is easy to get backwards.
            matrix = H::mkBool(true, at(p_line_));
        } else if (conjuncts.size() == 1) {
            matrix = conjuncts.front();
        } else {
            matrix = H::mkOp(H::Op::AND, std::move(conjuncts), at(p_line_));
        }

        // §2.2: the prefix's ORDER is the semantics, applied outermost-first.
        // Building it inside-out means walking the blocks in reverse.
        //
        // §2.3 row 2: a prefix variable occurring in no clause still binds, and
        // still fixes the alternation depth a QBF solver's difficulty is
        // measured by. So every block is emitted, whether or not the matrix
        // mentions it -- dropping the unused ones would report a shallower
        // instance than the file describes.
        for (auto it = blocks_.rbegin(); it != blocks_.rend(); ++it) {
            std::vector<H::Binder> binders;
            binders.reserve(it->vars.size());
            for (long long v : it->vars) {
                binders.push_back(H::Binder{varName(v), H::Sort::boolean()});
            }
            matrix = it->forall ? H::mkForall(binders, matrix, at(it->line))
                                : H::mkExists(binders, matrix, at(it->line));
        }

        H::Constraint c;
        c.loc = at(p_line_);
        c.formula = matrix;
        model->constraints.push_back(c);
        return model;
    }

    std::string src_;
    std::string file_;
    bool        strict_ = false;

    long long declared_vars_ = 0;
    long long declared_clauses_ = 0;
    int       p_line_ = 1;
    std::vector<Block> blocks_;
    std::vector<std::pair<std::vector<long long>, int>> clauses_;
};

class QdimacsLanguage : public Language {
public:
    QdimacsLanguage() {
        // The problem line, `a` and `e` blocks, clauses, comments -- QDIMACS is
        // a small format and this reads all of it.
        coverage_.total = 4;
        coverage_.supported = 4;
    }

    std::string id() const override { return "qdimacs"; }
    std::string displayName() const override { return "QDIMACS 1.1"; }
    std::string version() const override { return "1.1"; }
    std::vector<std::string> extensions() const override { return {".qdimacs"}; }
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
            QdimacsParser p(src, name, opts.strict);
            out.model = p.parse(out.diagnostics);
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "qdimacs", out.report.fidelity()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("qdimacs frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkQdimacsLanguage() { return std::make_shared<QdimacsLanguage>(); }

} // namespace SOMTParser::Lang
