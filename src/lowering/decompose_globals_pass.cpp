/* -*- Source -*-
 * DecomposeGlobalsPass. See the header for why both encodings exist.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/lowering/decompose_globals_pass.h"

#include "somtparser/lowering/bound_ints_pass.h"
#include "somtparser/translation/profile.h"

#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lower {

namespace {

namespace H = Uir::Hir;
using Uir::EncodingStyle;
using Uir::ErrorCode;

/** A fresh binder name that cannot collide with a model variable or with an
 *  outer binder. Uir::Hir::typeCheck rejects shadowing, so a collision is a
 *  hard error rather than a subtle one -- but it would be an error in *our*
 *  output, blamed on the input, so it is avoided by construction. */
std::string freshBinder(const H::ConstraintModel& model, const std::string& stem,
                        int nth) {
    for (int suffix = 0;; ++suffix) {
        std::string candidate = "!" + stem + std::to_string(nth)
                              + (suffix == 0 ? "" : "_" + std::to_string(suffix));
        bool taken = false;
        for (const auto& d : model.decls) {
            if (d.name == candidate) { taken = true; break; }
        }
        if (!taken) { return candidate; }
    }
}

/** lo <= x < hi, as one expression. */
H::ExprPtr inRange(const H::ExprPtr& x, const H::ExprPtr& lo, const H::ExprPtr& hi) {
    return H::mkOp(H::Op::AND, {H::mkOp(H::Op::LE, {lo, x}),
                                H::mkOp(H::Op::LT, {x, hi})});
}

/** The ground encoding: enumerate the terms once. Needs constant bounds. */
bool groundAllDifferent(const H::ExprPtr& g, const H::ExprPtr& array,
                        long long lo, long long hi, H::ExprPtr& out,
                        Uir::Diagnostics& diags) {
    std::vector<H::ExprPtr> terms;
    for (long long i = lo; i < hi; ++i) {
        terms.push_back(H::mkOp(H::Op::SELECT, {array, H::mkInt(i)}, g->loc));
    }
    (void)diags;
    out = terms.size() < 2 ? H::mkBool(true, g->loc)
                          : H::mkOp(H::Op::DISTINCT, std::move(terms), g->loc);
    return true;
}

/** Native distinctness over an explicit list of terms.
 *
 *  The list shape has no array and no index range, so there is nothing to
 *  quantify over: this is the encoding under BOTH styles, and the choice is
 *  recorded as distinct in both so the report does not claim a quantified
 *  encoding that was never built. */
bool groundAllDifferentList(const H::ExprPtr& g, H::ExprPtr& out) {
    // SMT distinct has exactly the conjunction-of-pairs relation, including
    // under negation. Keeping one native node avoids quadratic HIR expansion.
    out = g->args.size() < 2 ? H::mkBool(true, g->loc)
                           : H::mkOp(H::Op::DISTINCT, g->args, g->loc);
    return true;
}

/** Map one Int value into a position-specific domain where distinctness means
 *  "all nonzero values are distinct". Zero gets a unique negative tag; the
 *  nonzero Int domain maps injectively into positive integers. */
H::ExprPtr mapExceptZero(const H::ExprPtr& value, std::size_t position,
                         const Uir::SourceLoc& loc) {
    const H::ExprPtr zero = H::mkInt(0, loc);
    const H::ExprPtr one = H::mkInt(1, loc);
    const H::ExprPtr two = H::mkInt(2, loc);
    const H::ExprPtr twice = H::mkOp(H::Op::MUL, {two, value}, loc);
    const H::ExprPtr negative_tag =
        H::mkInt("-" + std::to_string(position + 1), loc);
    const H::ExprPtr nonzero_image = H::mkOp(
        H::Op::ITE,
        {H::mkOp(H::Op::GT, {value, zero}, loc),
         twice,
         H::mkOp(H::Op::SUB, {one, twice}, loc)},
        loc);
    return H::mkOp(
        H::Op::ITE,
        {H::mkOp(H::Op::EQ, {value, zero}, loc), negative_tag, nonzero_image},
        loc);
}

std::string freshReservedName(std::unordered_set<std::string>& reserved,
                              const std::string& stem, int nth) {
    for (int suffix = 0;; ++suffix) {
        std::string candidate = "!" + stem + std::to_string(nth)
                              + (suffix == 0 ? "" : "_" + std::to_string(suffix));
        if (reserved.insert(candidate).second) { return candidate; }
    }
}

H::ExprPtr distinctExceptZero(const H::ExprPtr& g,
                              const std::vector<H::ExprPtr>& terms) {
    if (terms.size() < 2) { return H::mkBool(true, g->loc); }
    std::vector<H::ExprPtr> images;
    images.reserve(terms.size());
    for (std::size_t i = 0; i < terms.size(); ++i) {
        images.push_back(mapExceptZero(terms[i], i, g->loc));
    }
    return H::mkOp(H::Op::DISTINCT, std::move(images), g->loc);
}

H::ExprPtr quantifiedAllDifferentExcept0(
    const H::ExprPtr& g, const H::ExprPtr& array,
    const H::ExprPtr& lo, const H::ExprPtr& hi,
    int nth, std::unordered_set<std::string>& reserved) {
    const H::Sort index = *array->sort.index;
    H::Binder bi{freshReservedName(reserved, "except0_i", nth), index};
    H::Binder bj{freshReservedName(reserved, "except0_j", nth), index};
    const H::ExprPtr i = H::mkBoundVar(bi.name, index, g->loc);
    const H::ExprPtr j = H::mkBoundVar(bj.name, index, g->loc);
    const H::ExprPtr x = H::mkOp(H::Op::SELECT, {array, i}, g->loc);
    const H::ExprPtr y = H::mkOp(H::Op::SELECT, {array, j}, g->loc);
    const H::ExprPtr zero = H::mkInt(0, g->loc);
    const H::ExprPtr both_nonzero = H::mkOp(H::Op::AND, {
        H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {x, zero}, g->loc)}, g->loc),
        H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {y, zero}, g->loc)}, g->loc)},
        g->loc);
    const H::ExprPtr guard = H::mkOp(H::Op::AND, {
        inRange(i, lo, hi), inRange(j, lo, hi),
        H::mkOp(H::Op::LT, {i, j}, g->loc), both_nonzero}, g->loc);
    const H::ExprPtr distinct =
        H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {x, y}, g->loc)}, g->loc);
    return H::mkForall({bi, bj},
        H::mkOp(H::Op::OR, {H::mkOp(H::Op::NOT, {guard}, g->loc), distinct},
                g->loc),
        g->loc);
}

/** Exact connectivity through an in-relation root/rank witness. Each selected
 *  non-root node needs a selected incoming parent of smaller rank. In a finite
 *  graph, strict decrease rules out a disconnected parent cycle; consequently
 *  the selected root reaches every selected node. The witness stays under the
 *  global's Boolean polarity, so negating the global negates the whole relation.
 */
H::ExprPtr connectivityWitness(const H::ExprPtr& g, bool undirected,
                               std::unordered_set<std::string>& reserved,
                               int fresh_id) {
    const std::size_t n = static_cast<std::size_t>(g->args[0]->int_value);
    const std::size_t e = static_cast<std::size_t>(g->args[1]->int_value);
    const std::size_t from_begin = 2;
    const std::size_t to_begin = from_begin + e;
    const std::size_t nodes_begin = to_begin + e;
    const std::size_t edges_begin = nodes_begin + n;
    if (n == 0) { return H::mkBool(false, g->loc); }

    const H::Sort int_sort = H::Sort::integer();
    const H::ExprPtr root = H::mkBoundVar(
        freshReservedName(reserved, undirected ? "conn_root" : "dconn_root",
                          fresh_id++), int_sort, g->loc);
    std::vector<H::Binder> binders{{root->name, int_sort}};
    std::vector<H::ExprPtr> ranks;
    ranks.reserve(n);
    for (std::size_t i = 0; i < n; ++i) {
        const std::string name = freshReservedName(
            reserved, undirected ? "conn_rank" : "dconn_rank", fresh_id++);
        binders.push_back({name, int_sort});
        ranks.push_back(H::mkBoundVar(name, int_sort, g->loc));
    }

    std::vector<H::ExprPtr> clauses;
    std::vector<H::ExprPtr> root_choices;
    root_choices.reserve(n);
    for (std::size_t i = 0; i < n; ++i) {
        const H::ExprPtr index = H::mkInt(std::to_string(i), g->loc);
        const H::ExprPtr is_root = H::mkOp(H::Op::EQ, {root, index}, g->loc);
        root_choices.push_back(H::mkOp(H::Op::AND,
            {is_root, g->args[nodes_begin + i]}, g->loc));
        clauses.push_back(H::mkOp(H::Op::AND, {
            H::mkOp(H::Op::LE, {H::mkInt(0, g->loc), ranks[i]}, g->loc),
            H::mkOp(H::Op::LT, {ranks[i], H::mkInt(std::to_string(n), g->loc)},
                    g->loc)}, g->loc));
    }
    clauses.push_back(H::mkOp(H::Op::OR, std::move(root_choices), g->loc));

    std::vector<std::vector<std::pair<std::size_t, std::size_t>>> incoming(n);
    for (std::size_t k = 0; k < e; ++k) {
        const auto from = static_cast<std::size_t>(g->args[from_begin + k]->int_value);
        const auto to = static_cast<std::size_t>(g->args[to_begin + k]->int_value);
        const H::ExprPtr& selected_edge = g->args[edges_begin + k];
        const H::ExprPtr& selected_from = g->args[nodes_begin + from];
        const H::ExprPtr& selected_to = g->args[nodes_begin + to];
        clauses.push_back(H::mkOp(H::Op::OR, {
            H::mkOp(H::Op::NOT, {selected_edge}, g->loc), selected_from}, g->loc));
        clauses.push_back(H::mkOp(H::Op::OR, {
            H::mkOp(H::Op::NOT, {selected_edge}, g->loc), selected_to}, g->loc));
        incoming[to].push_back({k, from});
        if (undirected) { incoming[from].push_back({k, to}); }
    }

    for (std::size_t target = 0; target < n; ++target) {
        std::vector<H::ExprPtr> has_parent;
        has_parent.reserve(incoming[target].size());
        for (const auto& [k, source] : incoming[target]) {
            const H::ExprPtr& selected_edge = g->args[edges_begin + k];
            has_parent.push_back(H::mkOp(H::Op::AND, {
                selected_edge,
                H::mkOp(H::Op::LT, {ranks[source], ranks[target]}, g->loc)}, g->loc));
        }
        std::vector<H::ExprPtr> reached{H::mkOp(H::Op::EQ, {
            root, H::mkInt(std::to_string(target), g->loc)}, g->loc)};
        reached.insert(reached.end(), has_parent.begin(), has_parent.end());
        clauses.push_back(H::mkOp(H::Op::OR, {
            H::mkOp(H::Op::NOT, {g->args[nodes_begin + target]}, g->loc),
            H::mkOp(H::Op::OR, std::move(reached), g->loc)}, g->loc));
    }
    const H::ExprPtr body = clauses.size() == 1 ? clauses.front()
        : H::mkOp(H::Op::AND, std::move(clauses), g->loc);
    return H::mkExists(std::move(binders), body, g->loc);
}

/** `c = count of terms equal to y`, as a sum of one-or-zero indicators.
 *
 *  There is only one encoding here and it is exact, so unlike alldifferent
 *  there is no ground/quantified pair to choose between: a quantified form
 *  would need a cardinality operator the HIR does not have, and building one
 *  out of a quantifier would need an uninterpreted counting function -- which
 *  is not the same constraint, because an uninterpreted function is free to
 *  denote anything the axioms do not pin down.
 *
 *  `ITE(t = y, 1, 0)` rather than a Boolean-to-Int coercion because the HIR
 *  has no such coercion and `Op::ITE` is total: every term contributes exactly
 *  one summand whatever it evaluates to.
 *
 *  A count over NO terms is `c = 0`, not an error. `count([e | i in S], y, c)`
 *  with an empty S is a legal MiniZinc model, and `mkOp(ADD, {})` would throw
 *  -- the same empty-argument trap groundAllDifferent avoids. */
H::ExprPtr countAsSum(const H::ExprPtr& g, const std::vector<H::ExprPtr>& terms,
                      const H::ExprPtr& sought, const H::ExprPtr& howmany) {
    if (terms.empty()) {
        return H::mkOp(H::Op::EQ, {howmany, H::mkInt(0, g->loc)}, g->loc);
    }
    const H::Sort count_sort = howmany->sort;
    const bool real = count_sort.kind == H::SortKind::REAL;
    const H::ExprPtr one = real ? H::mkReal("1", g->loc) : H::mkInt(1, g->loc);
    const H::ExprPtr zero = real ? H::mkReal("0", g->loc) : H::mkInt(0, g->loc);
    std::vector<H::ExprPtr> indicators;
    indicators.reserve(terms.size());
    for (const H::ExprPtr& t : terms) {
        indicators.push_back(H::mkOp(
            H::Op::ITE, {H::mkOp(H::Op::EQ, {t, sought}, g->loc), one, zero},
            g->loc));
    }
    H::ExprPtr total = indicators.size() == 1
                           ? indicators.front()
                           : H::mkOp(H::Op::ADD, std::move(indicators), g->loc);
    return H::mkOp(H::Op::EQ, {howmany, std::move(total)}, g->loc);
}

/** The quantified encoding: one assertion whatever the range. */
H::ExprPtr quantifiedAllDifferent(const H::ConstraintModel& model,
                                  const H::ExprPtr& g, const H::ExprPtr& array,
                                  const H::ExprPtr& lo, const H::ExprPtr& hi,
                                  int nth) {
    const H::Sort index = array->sort.index ? *array->sort.index
                                            : H::Sort::integer();
    H::Binder bi{freshBinder(model, "i", nth), index};
    H::Binder bj{freshBinder(model, "j", nth), index};
    const H::ExprPtr i = H::mkBoundVar(bi.name, index, g->loc);
    const H::ExprPtr j = H::mkBoundVar(bj.name, index, g->loc);

    // i < j rather than i != j: half the instantiations for the same meaning,
    // and it matches the ground form's pair enumeration exactly.
    const H::ExprPtr guard = H::mkOp(
        H::Op::AND, {inRange(i, lo, hi), inRange(j, lo, hi),
                     H::mkOp(H::Op::LT, {i, j})});
    const H::ExprPtr distinct = H::mkOp(
        H::Op::NOT, {H::mkOp(H::Op::EQ, {H::mkOp(H::Op::SELECT, {array, i}),
                                         H::mkOp(H::Op::SELECT, {array, j})})});
    // guard -> distinct, as OR(NOT guard, distinct): the HIR has no IMPLIES.
    const H::ExprPtr body =
        H::mkOp(H::Op::OR, {H::mkOp(H::Op::NOT, {guard}), distinct});

    return H::mkForall({bi, bj}, body, g->loc);
}

/** Rewrite one expression tree, replacing every GLOBAL it contains. */
class Decomposer {
public:
    Decomposer(const H::ConstraintModel& model, EncodingStyle style,
               Uir::TranslationReport& report, Uir::Diagnostics& diags)
        : model_(model), style_(style), report_(report), diags_(diags) {
        for (const auto& d : model.decls) { reserved_.insert(d.name); }
        for (const auto& f : model.funs) {
            reserved_.insert(f.name);
            reserveNames(f.body);
        }
        for (const auto& c : model.constraints) { reserveNames(c.formula); }
        for (const auto& o : model.objectives) { reserveNames(o.term); }
        // Name collection is finished. Its traversal cache must not coexist
        // with the rewrite cache on large, mostly ordinary HIR models.
        decltype(visited_){}.swap(visited_);
    }

    H::ExprPtr rewrite(const H::ExprPtr& e) {
        if (!e || !ok_) { return e; }
        // SMT sources can contain very deep ordinary expressions even when no
        // global needs rewriting. Keep both traversal and return propagation
        // on the heap. References into the immutable source preserve the old
        // shared-node test without adding artificial shared_ptr owners.
        struct Frame {
            const H::ExprPtr* source;
            std::size_t next = 0;
            std::vector<H::ExprPtr> args;
            bool changed = false;
            bool shared;
            explicit Frame(const H::ExprPtr& node)
                : source(&node), shared(node && node.use_count() > 1) {}
        };
        std::vector<Frame> pending;
        pending.emplace_back(e);
        H::ExprPtr result;
        while (!pending.empty()) {
            auto& frame = pending.back();
            const auto& node = *frame.source;
            bool complete = false;
            if (!node || !ok_) {
                result = node;
                complete = true;
            } else if (frame.next == 0) {
                if (node->args.empty()) {
                    result = node->kind == H::ExprKind::GLOBAL ? decompose(node) : node;
                    complete = true;
                } else if (frame.shared) {
                    const auto cached = rewritten_.find(node);
                    if (cached != rewritten_.end()) {
                        result = cached->second;
                        complete = true;
                    }
                }
                if (!complete) { frame.args.reserve(node->args.size()); }
            }
            if (!complete && frame.next < node->args.size()) {
                const auto& child = node->args[frame.next++];
                pending.emplace_back(child);
                continue;
            }
            if (!complete) {
                if (!frame.changed) {
                    result = decomposeNode(node);
                } else {
                    // Rebuild immutable nodes; other models retain the source.
                    auto copy = std::make_shared<H::Expr>(*node);
                    copy->args = std::move(frame.args);
                    result = decomposeNode(copy);
                }
                if (frame.shared) { rewritten_.emplace(node, result); }
            }
            pending.pop_back();
            if (!pending.empty()) {
                auto& parent = pending.back();
                parent.changed = parent.changed
                    || result != (*parent.source)->args[parent.next - 1];
                parent.args.push_back(result);
            }
        }
        return result;
    }

    bool ok() const { return ok_; }

    void appendAuxiliaryFunctions(H::ConstraintModel& model) {
        for (auto& function : auxiliary_functions_) {
            model.funs.push_back(std::move(function));
        }
        auxiliary_functions_.clear();
    }

private:
    /** Extensional membership over explicitly constructed finite sets needs
     *  only equality and Boolean operations. Unknown set values retain their
     *  native theory; in particular, no finite universe is guessed. */
    H::ExprPtr finiteMembership(const H::ExprPtr& element, const H::ExprPtr& set,
                                std::unordered_map<const H::Expr*, H::ExprPtr>& memo) {
        const auto found = memo.find(set.get());
        if (found != memo.end()) { return found->second; }
        H::ExprPtr result;
        if (set->kind == H::ExprKind::LIT_SET && set->name == "set.empty") {
            result = H::mkBool(false, set->loc);
        } else if (set->kind == H::ExprKind::OP) {
            const auto member = [&](const H::ExprPtr& child) {
                return finiteMembership(element, child, memo);
            };
            if (set->op == H::Op::SET_SINGLETON) {
                result = H::mkOp(H::Op::EQ, {element, set->args.front()}, set->loc);
            } else if (set->op == H::Op::SET_INSERT) {
                auto tail = member(set->args.back());
                if (tail) {
                    std::vector<H::ExprPtr> alternatives{tail};
                    for (std::size_t i = 0; i + 1 < set->args.size(); ++i) {
                        alternatives.push_back(H::mkOp(H::Op::EQ,
                            {element, set->args[i]}, set->loc));
                    }
                    result = H::mkOp(H::Op::OR, std::move(alternatives), set->loc);
                }
            } else if (set->op == H::Op::SET_UNION || set->op == H::Op::SET_INTER) {
                std::vector<H::ExprPtr> terms;
                for (const auto& child : set->args) {
                    auto term = member(child);
                    if (!term) { terms.clear(); break; }
                    terms.push_back(term);
                }
                if (!terms.empty()) {
                    result = terms.size() == 1 ? terms.front() :
                        H::mkOp(set->op == H::Op::SET_UNION ? H::Op::OR : H::Op::AND,
                                std::move(terms), set->loc);
                }
            } else if (set->op == H::Op::SET_MINUS) {
                auto a = member(set->args[0]), b = member(set->args[1]);
                if (a && b) {
                    result = H::mkOp(H::Op::AND,
                        {a, H::mkOp(H::Op::NOT, {b}, set->loc)}, set->loc);
                }
            } else if (set->op == H::Op::ITE) {
                auto a = member(set->args[1]), b = member(set->args[2]);
                if (a && b) { result = H::mkOp(H::Op::ITE, {set->args[0], a, b}, set->loc); }
            }
        }
        memo.emplace(set.get(), result);
        return result;
    }

    H::ExprPtr decomposeNode(const H::ExprPtr& e) {
        if (e->kind == H::ExprKind::GLOBAL) { return decompose(e); }
        if (e->kind == H::ExprKind::OP && e->op == H::Op::SET_MEMBER) {
            std::unordered_map<const H::Expr*, H::ExprPtr> memo;
            auto result = finiteMembership(e->args[0], e->args[1], memo);
            if (result) {
                Uir::EncodingChoice choice;
                choice.site = choice.unified_op = "set.member";
                choice.strategy = "finite-set-membership";
                choice.fidelity = Uir::Fidelity::exact();
                report_.addChoice(choice);
                return result;
            }
        }
        return e;
    }

    void reserveNames(const H::ExprPtr& e) {
        std::vector<const H::ExprPtr*> pending{&e};
        while (!pending.empty()) {
            const auto& node = *pending.back();
            pending.pop_back();
            if (!node) { continue; }
            if (!node->args.empty() && node.use_count() > 1
                && !visited_.insert(node.get()).second) { continue; }
            reserved_.insert(node->name);
            for (const auto& b : node->binders) { reserved_.insert(b.name); }
            for (const auto& a : node->args) { pending.push_back(&a); }
        }
    }

    /** A successor permutation with one locally existential rank array.
     *  Every edge except the edge back to start increases rank by one. A
     *  disconnected cycle would require a strict increase around that cycle.
     *  The witness stays inside this Boolean expression, including under NOT;
     *  adding free auxiliary declarations would change negative polarity.
     */
    H::ExprPtr decomposeCircuit(const H::ExprPtr& g) {
        Uir::EncodingChoice choice;
        choice.site = choice.unified_op = "circuit";
        choice.strategy = "circuit-local-ranks";
        choice.fidelity = Uir::Fidelity::exact();
        report_.addChoice(choice);
        const std::size_t n = g->args.size() - 1;
        if (n < 2) { return H::mkBool(n == 0, g->loc); }
        std::string name;
        do { name = "!circuit_rank" + std::to_string(nth_++); }
        while (!reserved_.insert(name).second);
        const H::Sort array_sort = H::Sort::array(H::Sort::integer(), H::Sort::integer());
        const H::ExprPtr rank = H::mkBoundVar(name, array_sort, g->loc);
        const H::ExprPtr start = g->args.front();
        const auto num = [&](std::size_t i) { return H::mkInt(std::to_string(i), g->loc); };
        const auto index = [&](std::size_t i) {
            return H::mkOp(H::Op::ADD, {start, num(i)}, g->loc);
        };
        const auto at = [&](const H::ExprPtr& i) {
            return H::mkOp(H::Op::SELECT, {rank, i}, g->loc);
        };
        const H::ExprPtr end = index(n);
        std::vector<H::ExprPtr> successors(g->args.begin() + 1, g->args.end());
        std::vector<H::ExprPtr> clauses{
            H::mkOp(H::Op::DISTINCT, successors, g->loc),
            H::mkOp(H::Op::EQ, {at(start), num(0)}, g->loc)};
        for (std::size_t i = 0; i < n; ++i) {
            const auto& successor = successors[i];
            const H::ExprPtr current = index(i);
            clauses.push_back(inRange(successor, start, end));
            clauses.push_back(inRange(at(current), num(0), num(n)));
            clauses.push_back(H::mkOp(H::Op::NOT,
                {H::mkOp(H::Op::EQ, {successor, current}, g->loc)}, g->loc));
            clauses.push_back(H::mkOp(H::Op::OR, {
                H::mkOp(H::Op::EQ, {successor, start}, g->loc),
                H::mkOp(H::Op::EQ, {at(successor),
                    H::mkOp(H::Op::ADD, {at(current), num(1)}, g->loc)}, g->loc)}, g->loc));
        }
        return H::mkExists({H::Binder{name, array_sort}},
                           H::mkOp(H::Op::AND, std::move(clauses), g->loc), g->loc);
    }

    H::ExprPtr decomposeTable(const H::ExprPtr& g) {
        Uir::EncodingChoice choice;
        choice.site = choice.unified_op = "table";
        choice.strategy = "table-row-disjunction";
        choice.fidelity = Uir::Fidelity::exact();
        report_.addChoice(choice);
        const std::size_t n = static_cast<std::size_t>(g->args[0]->int_value);
        const auto rows = g->args[1]->int_value;
        if (rows == 0 || n == 0) { return H::mkBool(rows != 0, g->loc); }
        std::vector<H::ExprPtr> alternatives;
        for (std::size_t offset = 2 + n; offset < g->args.size(); offset += n) {
            std::vector<H::ExprPtr> equalities;
            for (std::size_t j = 0; j < n; ++j) {
                equalities.push_back(H::mkOp(H::Op::EQ,
                    {g->args[2 + j], g->args[offset + j]}, g->loc));
            }
            alternatives.push_back(n == 1 ? equalities.front() :
                H::mkOp(H::Op::AND, std::move(equalities), g->loc));
        }
        return alternatives.size() == 1 ? alternatives.front() :
            H::mkOp(H::Op::OR, std::move(alternatives), g->loc);
    }

    H::ExprPtr decomposeInverse(const H::ExprPtr& g) {
        Uir::EncodingChoice choice;
        choice.site = choice.unified_op = "inverse";
        choice.strategy = "inverse-bidirectional-matching";
        choice.fidelity = Uir::Fidelity::exact();
        report_.addChoice(choice);
        const std::size_t n = static_cast<std::size_t>(g->args[2]->int_value);
        const std::size_t m = g->args.size() - 3 - n;
        // Total inverses are bijections, including the unique empty bijection.
        if (n != m || n == 0) { return H::mkBool(n == m, g->loc); }
        const auto index = [&](std::size_t side, std::size_t i) {
            return H::mkOp(H::Op::ADD, {g->args[side],
                H::mkInt(std::to_string(i), g->loc)}, g->loc);
        };
        std::vector<H::ExprPtr> clauses;
        for (std::size_t i = 0; i < n; ++i) {
            clauses.push_back(inRange(g->args[3 + i], g->args[1], index(1, m)));
            clauses.push_back(inRange(g->args[3 + n + i], g->args[0], index(0, n)));
            for (std::size_t j = 0; j < m; ++j) {
                clauses.push_back(H::mkOp(H::Op::EQ, {
                    H::mkOp(H::Op::EQ, {g->args[3 + i], index(1, j)}, g->loc),
                    H::mkOp(H::Op::EQ, {g->args[3 + n + j], index(0, i)}, g->loc)}, g->loc));
            }
        }
        return H::mkOp(H::Op::AND, std::move(clauses), g->loc);
    }

    // A top-level exact definition can refer to free model symbols. Never
    // lift an expression containing lexical binders into that scope: the
    // ordinary event expansion remains valid inside quantifiers and lets.
    bool canShareCumulativeLoad(const H::ExprPtr& g) const {
        if ((g->args.size() - 1) / 3 < 64) { return false; }
        std::unordered_set<const H::Expr*> visited;
        std::vector<H::ExprPtr> pending(g->args.begin(), g->args.end());
        while (!pending.empty()) {
            auto expression = std::move(pending.back());
            pending.pop_back();
            if (!expression || !visited.insert(expression.get()).second) { continue; }
            if (expression->kind == H::ExprKind::BOUND_VAR
                || !expression->binders.empty()) { return false; }
            pending.insert(pending.end(), expression->args.begin(), expression->args.end());
        }
        return true;
    }

    H::ExprPtr decomposeCumulative(const H::ExprPtr& g) {
        Uir::EncodingChoice choice;
        choice.site = choice.unified_op = "cumulative";
        const bool quantified = style_ == EncodingStyle::QUANTIFIED;
        const bool shared_load = !quantified && canShareCumulativeLoad(g);
        choice.strategy = quantified ? "cumulative-integer-time-quantified"
            : shared_load ? "cumulative-start-events-shared-load"
                          : "cumulative-start-events";
        choice.fidelity = Uir::Fidelity::exact();
        choice.rationale = quantified
            ? "nonnegative durations and demands; exact half-open load at every integer time, without a finite scheduling horizon"
            : "nonnegative durations and demands; exact half-open integer-time load at every task start, without a finite scheduling horizon";
        report_.addChoice(choice);
        const auto zero = H::mkInt(0, g->loc);
        const auto& capacity = g->args.front();
        std::vector<H::ExprPtr> clauses{H::mkOp(H::Op::GE, {capacity, zero}, g->loc)};
        std::vector<H::ExprPtr> ends;
        for (std::size_t i = 1; i < g->args.size(); i += 3) {
            clauses.push_back(H::mkOp(H::Op::GE, {g->args[i + 1], zero}, g->loc));
            clauses.push_back(H::mkOp(H::Op::GE, {g->args[i + 2], zero}, g->loc));
            ends.push_back(H::mkOp(H::Op::ADD, {g->args[i], g->args[i + 1]}, g->loc));
        }
        const auto loadAt = [&](const H::ExprPtr& time) {
            std::vector<H::ExprPtr> loads;
            loads.reserve(ends.size());
            for (std::size_t i = 1; i < g->args.size(); i += 3) {
                auto active = H::mkOp(H::Op::AND, {
                    H::mkOp(H::Op::LE, {g->args[i], time}, g->loc),
                    H::mkOp(H::Op::LT, {time, ends[(i - 1) / 3]}, g->loc)}, g->loc);
                loads.push_back(H::mkOp(H::Op::ITE, {active, g->args[i + 2], zero}, g->loc));
            }
            if (loads.empty()) { return zero; }
            return loads.size() == 1 ? loads.front()
                : H::mkOp(H::Op::ADD, std::move(loads), g->loc);
        };
        if (quantified && !ends.empty()) {
            // The global's source relation bounds the load at every integer
            // time. Retain that quantifier instead of N macro applications of
            // an N-term load, which a target parser can expand quadratically.
            // All guards remain inside the relation (also under negation).
            const H::Sort integer = H::Sort::integer();
            const std::string time_name = freshReservedName(reserved_, "cumulative_time", nth_++);
            const auto time = H::mkBoundVar(time_name, integer, g->loc);
            clauses.push_back(H::mkForall({{time_name, integer}},
                H::mkOp(H::Op::LE, {loadAt(time), capacity}, g->loc), g->loc));
            return H::mkOp(H::Op::AND, std::move(clauses), g->loc);
        }
        std::string load_name;
        if (shared_load) {
            load_name = freshReservedName(reserved_, "cumulative_load", nth_++);
            const auto time_name = freshReservedName(reserved_, "cumulative_time", nth_++);
            H::FunDecl function;
            function.name = load_name;
            function.params = {H::Sort::integer()};
            function.result = H::Sort::integer();
            function.loc = g->loc;
            function.binders = {{time_name, H::Sort::integer()}};
            function.body = loadAt(H::mkBoundVar(time_name, H::Sort::integer(), g->loc));
            function.auxiliary = true;
            auxiliary_functions_.push_back(std::move(function));
        }
        // With nonnegative demands, load can increase only at a start event.
        // The shared function has an exact body, not an uninterpreted witness.
        // It changes neither polarity nor the source variable projection.
        for (std::size_t event = 1; event < g->args.size(); event += 3) {
            auto total = shared_load
                ? H::mkApply(load_name, H::Sort::integer(), {g->args[event]}, g->loc)
                : loadAt(g->args[event]);
            clauses.push_back(H::mkOp(H::Op::LE, {total, capacity}, g->loc));
        }
        return clauses.size() == 1 ? clauses.front()
            : H::mkOp(H::Op::AND, std::move(clauses), g->loc);
    }

    H::ExprPtr decomposeDiffn(const H::ExprPtr& g) {
        const bool nonstrict = g->name == "diffn_nonstrict";
        report_.addChoice({g->name, g->name, "diffn-separating-axis",
            Uir::Fidelity::exact(),
            "each box pair separates in at least one axis; only nonstrict ignores zero-size boxes"});
        const std::size_t width = 2 * static_cast<std::size_t>(g->args[0]->int_value);
        const auto zero = H::mkInt(0, g->loc);
        std::vector<H::ExprPtr> clauses;
        for (std::size_t i = 1; i < g->args.size(); i += width) {
            for (std::size_t j = 1; j < i; j += width) {
                std::vector<H::ExprPtr> axes;
                for (std::size_t d = 0; d < width; d += 2) {
                    const auto& pi = g->args[i + d];
                    const auto& si = g->args[i + d + 1];
                    const auto& pj = g->args[j + d];
                    const auto& sj = g->args[j + d + 1];
                    axes.push_back(H::mkOp(H::Op::LE,
                        {H::mkOp(H::Op::ADD, {pi, si}, g->loc), pj}, g->loc));
                    axes.push_back(H::mkOp(H::Op::LE,
                        {H::mkOp(H::Op::ADD, {pj, sj}, g->loc), pi}, g->loc));
                    if (nonstrict) {
                        axes.push_back(H::mkOp(H::Op::EQ, {si, zero}, g->loc));
                        axes.push_back(H::mkOp(H::Op::EQ, {sj, zero}, g->loc));
                    }
                }
                clauses.push_back(H::mkOp(H::Op::OR, std::move(axes), g->loc));
            }
        }
        // Match MiniZinc's decomposition without adding size restrictions or
        // free facts outside the Boolean relation, including under negation.
        return clauses.empty() ? H::mkBool(true, g->loc) : clauses.size() == 1
            ? clauses.front() : H::mkOp(H::Op::AND, std::move(clauses), g->loc);
    }

    H::ExprPtr decompose(const H::ExprPtr& g) {
        if (g->name == "diffn" || g->name == "diffn_nonstrict") { return decomposeDiffn(g); }
        if (g->name == "connected" || g->name == "dconnected") {
            const bool undirected = g->name == "connected";
            Uir::EncodingChoice choice;
            choice.site = choice.unified_op = g->name;
            choice.strategy = undirected ? "connected-rank-witness"
                                         : "dconnected-rank-witness";
            choice.fidelity = Uir::Fidelity::exact();
            report_.addChoice(choice);
            return connectivityWitness(g, undirected, reserved_, nth_++);
        }
        if (g->name == "alldifferent_except_0") {
            if (g->args.empty()) {
                report_.addChoice({"alldifferent_except_0",
                                   "alldifferent_except_0",
                                   "alldifferent-except-0-distinct-map",
                                   Uir::Fidelity::exact(),
                                   "empty vector is vacuously true"});
                return H::mkBool(true, g->loc);
            }
            const bool indexed = g->args[0]->sort.kind == H::SortKind::ARRAY;
            Uir::EncodingChoice choice;
            choice.site = choice.unified_op = "alldifferent_except_0";
            choice.fidelity = Uir::Fidelity::exact();

            if (!indexed) {
                choice.strategy = "alldifferent-except-0-distinct-map";
                report_.addChoice(choice);
                return distinctExceptZero(g, g->args);
            }

            const H::ExprPtr& array = g->args[0];
            const H::ExprPtr& lo = g->args[1];
            const H::ExprPtr& hi = g->args[2];
            choice.site = array->kind == H::ExprKind::IDENT
                              ? array->name : "alldifferent_except_0";
            if (style_ == EncodingStyle::QUANTIFIED) {
                choice.strategy = "alldifferent-except-0-quantified";
                report_.addChoice(choice);
                return quantifiedAllDifferentExcept0(g, array, lo, hi,
                                                       nth_++, reserved_);
            }
            if (lo->kind != H::ExprKind::LIT_INT || hi->kind != H::ExprKind::LIT_INT
                || !H::fitsInt64(*lo) || !H::fitsInt64(*hi)) {
                diags_.error(
                    ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "alldifferent_except_0 needs constant index bounds under the "
                        "'ground' encoding style, because expansion enumerates them",
                    g->loc);
                ok_ = false;
                return g;
            }
            choice.strategy = "alldifferent-except-0-distinct-map";
            report_.addChoice(choice);
            std::vector<H::ExprPtr> terms;
            for (long long i = lo->int_value; i < hi->int_value; ++i) {
                terms.push_back(H::mkOp(
                    H::Op::SELECT, {array, H::mkInt(i, g->loc)}, g->loc));
            }
            return distinctExceptZero(g, terms);
        }
        if (g->name == "count_value") {
            report_.addChoice({"count_value", "count_value", "count-value-indicators",
                               Uir::Fidelity::exact(), "sum of equality indicators, with no auxiliary variable"});
            const auto zero = H::mkInt(0, g->loc), one = H::mkInt(1, g->loc);
            std::vector<H::ExprPtr> terms;
            for (std::size_t i = 2; i < g->args.size(); ++i) {
                terms.push_back(H::mkOp(H::Op::ITE, {
                    H::mkOp(H::Op::EQ, {g->args[i], g->args[1]}, g->loc), one, zero}, g->loc));
            }
            return terms.empty() ? zero : terms.size() == 1 ? terms.front()
                : H::mkOp(H::Op::ADD, std::move(terms), g->loc);
        }
        if (g->name == "cumulative") { return decomposeCumulative(g); }
        if (g->name == "table") { return decomposeTable(g); }
        if (g->name == "inverse") { return decomposeInverse(g); }
        if (g->name == "circuit") { return decomposeCircuit(g); }
        if (g->name == "count") { return decomposeCount(g); }
        if (g->name != "alldifferent") {
            // typeCheck already refuses an unknown global, so reaching here
            // means a global was added to the checker's table and not to this
            // pass. Failing loudly beats emitting the constraint unchanged,
            // which would leave a GLOBAL node for HirToParser to meet.
            diags_.error(ErrorCode::E_INTERNAL,
                         "decompose-globals: no decomposition for '" + g->name
                             + "', which typeCheck accepted",
                         g->loc);
            ok_ = false;
            return g;
        }
        return decomposeAllDifferent(g);
    }

    /** `count(array, lo, hi, y, c)` or `count(t1, …, tn, y, c)`.
     *
     *  Both shapes reduce to the same sum of indicators, so the shape only
     *  decides where the terms come from. The indexed one enumerates, which
     *  needs constant bounds for the same reason alldifferent's ground
     *  encoding does -- and says so by name rather than approximating. */
    H::ExprPtr decomposeCount(const H::ExprPtr& g) {
        const std::size_t n = g->args.size();
        const H::ExprPtr& sought = g->args[n - 2];
        const H::ExprPtr& howmany = g->args[n - 1];

        Uir::EncodingChoice choice;
        choice.unified_op = "count";
        choice.fidelity = Uir::Fidelity::exact();
        // One encoding under both styles, and said so: a quantified form would
        // need a cardinality operator the HIR does not have, and claiming
        // "quantified" would describe an encoding nobody built.
        choice.strategy = "count-indicator-sum";

        std::vector<H::ExprPtr> terms;
        if (g->args[0]->sort.kind == H::SortKind::ARRAY) {
            const H::ExprPtr& array = g->args[0];
            const H::ExprPtr& lo = g->args[1];
            const H::ExprPtr& hi = g->args[2];
            if (lo->kind != H::ExprKind::LIT_INT || hi->kind != H::ExprKind::LIT_INT
                || !H::fitsInt64(*lo) || !H::fitsInt64(*hi)) {
                diags_.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                             "count needs constant index bounds, because the "
                             "decomposition enumerates the elements it counts",
                             g->loc);
                ok_ = false;
                return g;
            }
            for (long long i = lo->int_value; i < hi->int_value; ++i) {
                terms.push_back(H::mkOp(H::Op::SELECT, {array, H::mkInt(i)}, g->loc));
            }
            choice.site = array->kind == H::ExprKind::IDENT ? array->name : "count";
        } else {
            terms.assign(g->args.begin(), g->args.end() - 2);
            choice.site = "count";
        }
        report_.addChoice(choice);
        return countAsSum(g, terms, sought, howmany);
    }

    H::ExprPtr decomposeAllDifferent(const H::ExprPtr& g) {
        // Which shape, by the first argument's SORT -- the same test typeCheck
        // makes, and for the same reason: a three-term list form must not be
        // read as an indexed one.
        if (g->args[0]->sort.kind != H::SortKind::ARRAY) {
            Uir::EncodingChoice list_choice;
            list_choice.site = "alldifferent";
            list_choice.unified_op = "alldifferent";
            list_choice.fidelity = Uir::Fidelity::exact();
            // Native distinct under both styles: there is no index set to
            // quantify over when the terms are given explicitly, so reporting
            // "quantified" here would describe an encoding nobody built.
            list_choice.strategy = "alldifferent-distinct";
            report_.addChoice(list_choice);
            H::ExprPtr list_out;
            if (!groundAllDifferentList(g, list_out)) {
                ok_ = false;
                return g;
            }
            return list_out;
        }

        const H::ExprPtr& array = g->args[0];
        const H::ExprPtr& lo = g->args[1];
        const H::ExprPtr& hi = g->args[2];

        Uir::EncodingChoice choice;
        choice.site = array->kind == H::ExprKind::IDENT ? array->name : "alldifferent";
        choice.unified_op = "alldifferent";
        choice.fidelity = Uir::Fidelity::exact();

        if (style_ == EncodingStyle::QUANTIFIED) {
            choice.strategy = "alldifferent-quantified";
            report_.addChoice(choice);
            return quantifiedAllDifferent(model_, g, array, lo, hi, nth_++);
        }

        // GROUND (and UNSPECIFIED, whose only sensible reading is the encoding
        // every other toolchain produces).
        // fitsInt64, not merely LIT_INT: an integer literal is text-backed and
        // may exceed what int_value holds, and reading it anyway would enumerate
        // a range built from a wrong number rather than refusing.
        if (lo->kind != H::ExprKind::LIT_INT || hi->kind != H::ExprKind::LIT_INT
            || !H::fitsInt64(*lo) || !H::fitsInt64(*hi)) {
            // Not an approximation to record -- the encoding cannot be built at
            // all, because expansion has to enumerate the range. The quantified
            // profile translates this instance; ground does not, and saying so
            // by name is the difference between a coverage figure that means
            // something and one that does not.
            diags_.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                         "alldifferent needs constant index bounds under the "
                         "'ground' encoding style, because expansion enumerates "
                         "them; use the 'quantified' profile for this model",
                         g->loc);
            ok_ = false;
            return g;
        }
        choice.strategy = "alldifferent-distinct";
        report_.addChoice(choice);

        H::ExprPtr out;
        if (!groundAllDifferent(g, array, lo->int_value, hi->int_value, out, diags_)) {
            ok_ = false;
            return g;
        }
        return out;
    }

    const H::ConstraintModel& model_;
    EncodingStyle             style_;
    Uir::TranslationReport&   report_;
    Uir::Diagnostics&         diags_;
    int                       nth_ = 0;
    bool                      ok_ = true;
    std::unordered_set<std::string> reserved_;
    std::unordered_set<const H::Expr*> visited_;
    // Cache shared DAG nodes only. Owning keys keep a rewritten source alive
    // until the pass finishes, so allocator address reuse cannot alias a later
    // source node. Unique tree nodes need neither a cache entry nor retention.
    std::unordered_map<H::ExprPtr, H::ExprPtr> rewritten_;
    std::vector<H::FunDecl> auxiliary_functions_;
};

} // namespace

bool DecomposeGlobalsPass::run(H::ConstraintModel& model, Uir::LowerContext& ctx) {
    // The style is the profile's, not this pass's parameter: several passes
    // face the same question and must answer it identically within one
    // translation (profile.h).
    const EncodingStyle style =
        ctx.profile != nullptr ? ctx.profile->style() : EncodingStyle::UNSPECIFIED;

    Decomposer d(model, style, *ctx.report, *ctx.diagnostics);
    for (auto& c : model.constraints) {
        c.formula = d.rewrite(c.formula);
        if (!d.ok()) { return false; }
    }
    for (auto& o : model.objectives) {
        o.term = d.rewrite(o.term);
        if (!d.ok()) { return false; }
    }
    d.appendAuxiliaryFunctions(model);
    for (const auto& f : model.funs) {
        if (!f.body) { continue; }
        std::unordered_set<const H::Expr*> visited;
        std::vector<const H::Expr*> pending{f.body.get()};
        bool contains_global = false;
        while (!pending.empty()) {
            const auto* expression = pending.back();
            pending.pop_back();
            if (!expression || !visited.insert(expression).second) { continue; }
            if (expression->kind == H::ExprKind::GLOBAL) { contains_global = true; break; }
            for (const auto& child : expression->args) { pending.push_back(child.get()); }
        }
        if (contains_global) {
            ctx.diagnostics->error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "global decomposition inside defined function '" + f.name
                    + "' is unsupported because a rewrite may introduce call-shared witnesses",
                f.loc);
            return false;
        }
    }
    return true;
}

void registerDecompositionPasses(Uir::PassRegistry& registry) {
    if (registry.get("decompose-globals") == nullptr) {
        registry.add(std::make_shared<DecomposeGlobalsPass>());
    }
}

} // namespace SOMTParser::Lower
