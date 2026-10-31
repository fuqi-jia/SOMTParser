/* -*- Source -*-
 * WCNF (MaxSAT) frontend, old and new formats.
 *
 * The format is docs/languages/wcnf.md; its `implicit-constraints` block is the
 * specification this file implements, and each entry has a fixture in
 * languages/wcnf/instances.
 *
 * All three obligations are about the same question -- **which clauses are
 * hard** -- and each format answers it a different way:
 *
 *     new format   a clause beginning `h` is hard. A clause with no leading
 *                  weight would be malformed; the ABSENCE of a weight is not a
 *                  default, it is the `h` marker's job.
 *     old format   every clause carries a weight, and one whose weight is >=
 *                  `top` is HARD -- not a soft clause at a large cost.
 *
 * The third obligation is about the objective: soft clauses are jointly
 * optimised, and the thing being minimised is the sum of the violated weights.
 * No single clause states that, so it has to be constructed -- and getting it
 * wrong is silent, because the constraints are all still there.
 *
 * `top` is a MARKER, not a threshold. wcnf.md §2.2 draws the line against WBO,
 * whose `soft: T ;` is a hard admissibility bound -- an assignment whose cost
 * reaches T is not a solution at all. Translating either with the other's
 * meaning changes the answer.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/wcnf.h"
#include "wcnf_decimal.h"

#include <algorithm>
#include <charconv>
#include <cstdlib>
#include <cstdint>
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
using WcnfInternal::decimalAtLeast;
using WcnfInternal::decimalNatural;

std::string varName(long long v) { return "x" + std::to_string(v); }

struct Clause {
    std::vector<long long> lits;
    bool      hard = false;
    std::string weight = "1";
    int       line = 0;
    bool      encoded_as_binary_edge = false;
};

struct BinaryEdge {
    std::size_t u = 0; // falsifying assignment literal for the first source literal
    std::size_t v = 0;
    int line = 0;
};

struct BinaryClique {
    std::vector<std::size_t> vertices;
    int line = 0;
};

struct BinaryCliquePlan {
    bool bitmap = false; // optional dense-enough graph representation was built
    std::vector<BinaryEdge> edges; // unique graph edges, sorted by (u,v)
    std::vector<BinaryClique> cliques; // edge-disjoint, each size >= 4
    std::vector<std::uint64_t> remaining_adjacency; // symmetric bit matrix
    std::size_t words_per_row = 0;
};

std::size_t firstSetBit(std::uint64_t word) {
    // Caller guarantees word != 0. This portable scan avoids compiler-specific
    // intrinsics while retaining the same least-significant-bit order.
    std::size_t bit = 0;
    while ((word & std::uint64_t(1)) == 0) {
        word >>= 1;
        ++bit;
    }
    return bit;
}

bool bitAt(const std::vector<std::uint64_t>& bits, std::size_t words,
           std::size_t u, std::size_t v) {
    return (bits[u * words + v / 64] & (std::uint64_t(1) << (v % 64))) != 0;
}

void clearBit(std::vector<std::uint64_t>& bits, std::size_t words,
              std::size_t u, std::size_t v) {
    bits[u * words + v / 64] &= ~(std::uint64_t(1) << (v % 64));
}

BinaryCliquePlan makeBinaryCliquePlan(std::vector<Clause>& clauses, std::size_t variables) {
    BinaryCliquePlan plan;
    std::size_t raw_edges = 0;
    for (const Clause& clause : clauses) {
        if (clause.hard && clause.lits.size() == 2 && clause.lits[0] != clause.lits[1]) {
            ++raw_edges;
        }
    }
    if (raw_edges == 0 || variables > std::numeric_limits<std::size_t>::max() / 2) {
        return plan;
    }
    const std::size_t vertices = variables * 2;
    if (vertices > std::numeric_limits<std::size_t>::max() - 63) { return plan; }
    const std::size_t words = (vertices + 63) / 64;
    if (words != 0 && vertices > std::numeric_limits<std::size_t>::max() / words) { return plan; }
    const std::size_t matrix_words = vertices * words;
    if (matrix_words > std::numeric_limits<std::size_t>::max() / sizeof(std::uint64_t)
        || raw_edges > std::numeric_limits<std::size_t>::max() / sizeof(BinaryEdge)) {
        return plan;
    }

    // Consume the parser's per-clause two-literal vectors into an O(E) edge
    // list before selecting a graph representation. Hard duplicates are
    // redundant; sort/unique also makes the later edge accounting exact.
    plan.edges.reserve(raw_edges);
    for (Clause& clause : clauses) {
        if (!clause.hard || clause.lits.size() != 2 || clause.lits[0] == clause.lits[1]) {
            continue;
        }
        const auto vertex = [](long long literal) {
            const std::size_t variable = static_cast<std::size_t>(std::llabs(literal) - 1);
            return variable * 2 + (literal > 0 ? 0 : 1);
        };
        std::size_t u = vertex(clause.lits[0]);
        std::size_t v = vertex(clause.lits[1]);
        if (u > v) { std::swap(u, v); }
        plan.edges.push_back({u, v, clause.line});
        clause.encoded_as_binary_edge = true;
        std::vector<long long>().swap(clause.lits);
    }
    std::sort(plan.edges.begin(), plan.edges.end(), [](const BinaryEdge& a, const BinaryEdge& b) {
        if (a.u != b.u) { return a.u < b.u; }
        if (a.v != b.v) { return a.v < b.v; }
        return a.line < b.line;
    });
    plan.edges.erase(std::unique(plan.edges.begin(), plan.edges.end(),
        [](const BinaryEdge& a, const BinaryEdge& b) { return a.u == b.u && a.v == b.v; }),
        plan.edges.end());

    // Use a bitmap only when its O(V^2/64) footprint is no larger than the
    // deduplicated O(E) edge list. Sparse/large graphs stay edge-list based,
    // are not rejected, and are emitted as their original binary clauses.
    if (matrix_words * sizeof(std::uint64_t) > plan.edges.size() * sizeof(BinaryEdge)) {
        return plan;
    }
    plan.bitmap = true;
    plan.words_per_row = words;
    std::vector<std::uint64_t> graph(matrix_words, 0);
    for (const BinaryEdge& edge : plan.edges) {
        graph[edge.u * words + edge.v / 64] |= std::uint64_t(1) << (edge.v % 64);
        graph[edge.v * words + edge.u / 64] |= std::uint64_t(1) << (edge.u % 64);
    }
    plan.remaining_adjacency = std::move(graph);
    std::vector<std::uint64_t> tried(words, 0), common(words, 0);
    for (std::size_t u = 0; u < vertices; ++u) {
        std::fill(tried.begin(), tried.end(), 0);
        for (;;) {
            std::size_t v = vertices;
            for (std::size_t word = 0; word < words; ++word) {
                const std::uint64_t candidates = plan.remaining_adjacency[u * words + word]
                    & ~tried[word];
                if (candidates != 0) {
                    v = word * 64 + firstSetBit(candidates);
                    break;
                }
            }
            if (v >= vertices) { break; }
            tried[v / 64] |= std::uint64_t(1) << (v % 64);
            std::vector<std::size_t> clique{u, v};
            for (std::size_t word = 0; word < words; ++word) {
                common[word] = plan.remaining_adjacency[u * words + word]
                    & plan.remaining_adjacency[v * words + word];
            }
            common[u / 64] &= ~(std::uint64_t(1) << (u % 64));
            common[v / 64] &= ~(std::uint64_t(1) << (v % 64));
            for (;;) {
                std::size_t w = vertices;
                for (std::size_t word = 0; word < words; ++word) {
                    if (common[word] != 0) {
                        w = word * 64 + firstSetBit(common[word]);
                        break;
                    }
                }
                if (w >= vertices) { break; }
                clique.push_back(w);
                for (std::size_t word = 0; word < words; ++word) {
                    common[word] &= plan.remaining_adjacency[w * words + word];
                }
            }
            if (clique.size() < 4) { continue; }
            int source_line = std::numeric_limits<int>::max();
            for (std::size_t i = 0; i < clique.size(); ++i) {
                for (std::size_t j = i + 1; j < clique.size(); ++j) {
                    const auto a = std::min(clique[i], clique[j]);
                    const auto b = std::max(clique[i], clique[j]);
                    const auto found = std::lower_bound(plan.edges.begin(), plan.edges.end(),
                        std::pair<std::size_t, std::size_t>{a, b},
                        [](const BinaryEdge& edge, const auto& key) {
                            return edge.u < key.first || (edge.u == key.first && edge.v < key.second);
                        });
                    if (found != plan.edges.end() && found->u == a && found->v == b) {
                        source_line = std::min(source_line, found->line);
                    }
                    clearBit(plan.remaining_adjacency, words, a, b);
                    clearBit(plan.remaining_adjacency, words, b, a);
                }
            }
            plan.cliques.push_back({std::move(clique), source_line});
        }
    }
    return plan;
}

class WcnfParser {
public:
    WcnfParser(std::istream& src, std::string file, bool strict)
        : source_(src), file_(std::move(file)), strict_(strict) {
        batch_.source_file = file_;
    }

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags) {
        if (!read(source_, diags)) { return nullptr; }
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

    static bool toInt(const std::string& tok, long long& out) {
        if (tok.empty()) { return false; }
        const char* first = tok.data();
        const char* last = first + tok.size();
        const auto conv = std::from_chars(first, last, out);
        return conv.ec == std::errc() && conv.ptr == last;
    }

    bool read(std::istream& in, Uir::Diagnostics& diags) {
        std::string raw;
        int lineno = 0;

        while (std::getline(in, raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            std::istringstream ls(raw);
            std::string first;
            if (!(ls >> first)) { continue; }
            // A comment is a line whose FIRST CHARACTER is `c`. The space
            // after it is conventional, not required: the MaxSAT Evaluation's
            // own standardised instances open with `c{` and continue
            // `c "sha1sum": ...`, a JSON block written one line at a time with
            // no separator. Splitting on whitespace and comparing the first
            // TOKEN to "c" refuses every one of them -- 10 of the 25 files in
            // the vendored corpus, each reported as malformed input when the
            // file is well formed and the reader is not.
            if (!first.empty() && first[0] == 'c') { continue; }
            if (first == "p") {
                // §2.2: the old format. `p wcnf V C [top]`, and `p cnf V C` is
                // unweighted MaxSAT -- every clause soft at weight 1.
                if (old_format_) {
                    diags.error(ErrorCode::E_PARSE, "more than one problem line",
                                at(lineno));
                    return false;
                }
                std::string fmt, vs, cs, ts;
                if (!(ls >> fmt) || (fmt != "wcnf" && fmt != "cnf")) {
                    diags.error(ErrorCode::E_PARSE,
                                "the problem line must read `p wcnf V C [top]` or "
                                "`p cnf V C`",
                                at(lineno));
                    return false;
                }
                long long v = 0, c = 0;
                if (!(ls >> vs) || !(ls >> cs) || !toInt(vs, v) || !toInt(cs, c)
                    || v < 0 || c < 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "the problem line's counts are not numbers", at(lineno));
                    return false;
                }
                declared_vars_ = v;
                declared_clauses_ = c;
                unweighted_ = (fmt == "cnf");
                if (ls >> ts) {
                    std::string top;
                    if (!decimalNatural(ts, top)) {
                        diags.error(ErrorCode::E_PARSE,
                                    "the problem line's `top` is not a positive number",
                                    at(lineno));
                        return false;
                    }
                    top_ = std::move(top);
                    has_top_ = true;
                }
                old_format_ = true;
                p_line_ = lineno;
                continue;
            }
            if (clause_count_ != 0 && old_format_ == false && first == "p") { continue; }

            // A clause line. It may be `h <lits> 0` (new format), `<w> <lits> 0`
            // (old format or new soft), or `<lits> 0` (unweighted `p cnf`).
            Clause cl;
            cl.line = lineno;
            std::istringstream body(raw);
            std::string tok;
            bool first_token = true;
            bool terminated = false;
            while (body >> tok) {
                if (first_token) {
                    first_token = false;
                    if (tok == "h") {
                        // §2.1: hard clauses are declared by `h` instead of a
                        // weight. The marker IS the declaration.
                        cl.hard = true;
                        new_format_ = true;
                        continue;
                    }
                    if (old_format_ && unweighted_) {
                        // `p cnf`: unweighted MaxSAT, every clause soft at 1.
                        cl.weight = "1";
                        // fall through: this token is a literal
                    } else {
                        std::string w;
                        if (!decimalNatural(tok, w)) {
                            diags.error(ErrorCode::E_PARSE,
                                        "'" + tok + "' is neither `h` nor a weight",
                                            at(lineno));
                            return false;
                        }
                        cl.weight = std::move(w);
                        if (!old_format_) { new_format_ = true; }
                        continue;
                    }
                }
                long long l = 0;
                if (!toInt(tok, l)) {
                    diags.error(ErrorCode::E_PARSE, "'" + tok + "' is not a literal",
                                at(lineno));
                    return false;
                }
                if (l == 0) { terminated = true; break; }
                if (l == std::numeric_limits<long long>::min()) {
                    diags.error(ErrorCode::E_PARSE,
                                "literal magnitude does not fit in a signed 64-bit integer",
                                at(lineno));
                    return false;
                }
                cl.lits.push_back(l);
            }
            if (!terminated) {
                diags.error(ErrorCode::E_PARSE, "the clause is not terminated by 0",
                            at(lineno));
                return false;
            }
            for (long long literal : cl.lits) {
                const long long variable = std::llabs(literal);
                largest_ = std::max(largest_, variable);
                batch_.literals.push_back(static_cast<std::int64_t>(literal));
            }
            batch_.clause_offsets.push_back(batch_.literals.size());
            const bool hard = cl.hard || (old_format_ && has_top_
                && decimalAtLeast(cl.weight, top_));
            if (!hard) { batch_.weight_bytes += cl.weight; }
            batch_.weight_offsets.push_back(batch_.weight_bytes.size());
            batch_.source_lines.push_back(static_cast<std::uint32_t>(lineno));
            ++clause_count_;
        }
        if (!old_format_ && !new_format_ && clause_count_ == 0) {
            diags.error(ErrorCode::E_PARSE, "the file has no clauses", at(1));
            return false;
        }
        return true;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags) {
        auto model = std::make_shared<H::ConstraintModel>();
        if (old_format_) {
            if (static_cast<long long>(clause_count_) != declared_clauses_) {
                const std::string msg = "the problem line declares "
                    + std::to_string(declared_clauses_) + " clauses but the file has "
                    + std::to_string(clause_count_);
                if (strict_) { diags.error(ErrorCode::E_PARSE, msg, at(p_line_)); return nullptr; }
                diags.warn(ErrorCode::E_PARSE, msg, at(p_line_));
            }
            if (largest_ > declared_vars_) {
                const std::string msg = "the problem line declares "
                    + std::to_string(declared_vars_) + " variables but index "
                    + std::to_string(largest_) + " is used";
                if (strict_) { diags.error(ErrorCode::E_PARSE, msg, at(p_line_)); return nullptr; }
                diags.warn(ErrorCode::E_PARSE, msg, at(p_line_));
            }
        }
        // Old-format header variables that never occur remain declared, exactly
        // as the ordinary frontend did. New-format variables are inferred from
        // the greatest absolute literal index. No source-side arbitrary bound.
        const std::uint64_t variable_count = static_cast<std::uint64_t>(
            old_format_ ? std::max(declared_vars_, largest_) : largest_);
        model->bool_var_ranges.push_back(
            H::BoolVarRange{"x", 1, variable_count, H::Sort::boolean(), at(p_line_)});
        batch_.variable_range = 0;
        model->packed_bool_clauses.push_back(std::move(batch_));
        return model;
    }

    std::istream& source_;
    std::string file_;
    bool        strict_ = false;

    bool      old_format_ = false;
    bool      new_format_ = false;
    bool      unweighted_ = false;
    bool      has_top_ = false;
    std::string top_;
    long long declared_vars_ = 0;
    long long declared_clauses_ = 0;
    int       p_line_ = 1;
    long long largest_ = 0;
    std::uint64_t clause_count_ = 0;
    H::PackedBoolClauseBatch batch_{0, {}, {0}, {}, {0}, {}, {}};

};

} // namespace

ParseOutcome parsePackedWcnf(const SourceUnit& unit, const ParseOptions& opts) {
    ParseOutcome out;
    const std::string name = unit.main_path.empty() ? unit.display_name : unit.main_path;
    if (!unit.inline_source.empty()) {
        std::istringstream input(unit.inline_source);
        try { WcnfParser p(input, name, opts.strict); out.model = p.parse(out.diagnostics); }
        catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                                  "wcnf packed frontend: memory allocation failed");
            return out;
        }
        catch (const std::exception& e) {
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("wcnf packed frontend: ") + e.what());
            return out;
        }
    } else {
        std::error_code ec;
        if (std::filesystem::is_directory(unit.main_path, ec)) {
            out.diagnostics.error(ErrorCode::E_IO, "'" + unit.main_path + "' is a directory");
            return out;
        }
        std::ifstream input(unit.main_path, std::ios::binary);
        if (!input) {
            out.diagnostics.error(ErrorCode::E_IO, "cannot open '" + unit.main_path + "'");
            return out;
        }
        try { WcnfParser p(input, name, opts.strict); out.model = p.parse(out.diagnostics); }
        catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                                  "wcnf packed frontend: memory allocation failed");
            return out;
        }
        catch (const std::exception& e) {
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("wcnf packed frontend: ") + e.what());
            return out;
        }
    }
    if (out.model) {
        out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
            *out.model, "wcnf", out.report.fidelity()));
    }
    return out;
}

} // namespace SOMTParser::Lang
