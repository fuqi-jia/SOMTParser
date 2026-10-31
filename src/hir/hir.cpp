/* -*- Source -*-
 * HIR constructors and feature detection.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/hir/hir.h"

#include <charconv>
#include <array>
#include <algorithm>
#include <functional>
#include <cstdlib>
#include <cerrno>
#include <iterator>
#include <limits>
#include <new>
#include <stdexcept>
#include <unordered_set>
#include "somtparser/core/asserting.h"

#include <utility>

#if defined(_WIN32)
#include <io.h>
#else
#include <unistd.h>
#endif

namespace SOMTParser::Uir::Hir {

namespace {

// Only the pointer is thread-local; the outermost Expr destructor owns the
// queue. Concurrent final releases use independent queues, without relying on
// a use_count() snapshot or modifying any still-live immutable expression.
thread_local std::vector<ExprPtr>* releasingExpressions = nullptr;

struct SortReleaseQueue {
    const Sort* head = nullptr;
};
thread_local SortReleaseQueue* releasingSorts = nullptr;

void enqueueSort(std::shared_ptr<const Sort>& child, SortReleaseQueue& queue) noexcept {
    if (!child) return;
    auto& link = child->reclamation;
    while (link.busy.test_and_set(std::memory_order_acquire)) {}
    if (link.owner) {
        // A queue already pins this object (possibly on another thread).
        // Drop the duplicate edge while holding the lock: the draining thread
        // cannot remove that pin, so this reset cannot invoke Sort::~Sort.
        // Resetting after unlocking would race and allow recursive release.
        child.reset();
    } else {
        link.owner = std::move(child);
        link.next = queue.head;
        queue.head = link.owner.get();
    }
    link.busy.clear(std::memory_order_release);
}

template <std::size_t N>
[[noreturn]] void abortExpressionRelease(const char (&message)[N]) noexcept {
    // A destructor cannot report bad_alloc by throwing. Use a fixed buffer and
    // the file descriptor directly: formatting and iostreams may allocate.
    std::size_t written = 0;
    while (written < N - 1) {
#if defined(_WIN32)
        const auto count = _write(2, message + written,
                                  static_cast<unsigned>(N - 1 - written));
#else
        const auto count = ::write(STDERR_FILENO, message + written, N - 1 - written);
#endif
        if (count < 0 && errno == EINTR) { continue; }
        if (count <= 0) { break; }
        written += static_cast<std::size_t>(count);
    }
    std::abort();
}

bool isComparison(Op op) {
    // DISTINCT belongs here rather than with the connectives: it relates TERMS
    // and yields Bool, exactly as EQ does. Left out, mkOp's fallback would give
    // it widen(args) -- so `(distinct x y)` on two Ints recorded sort Int, and
    // typeCheck caught it as "'distinct' yields Bool here, but the expression
    // records Int". A sort that mkOp assigns before typeCheck runs is worth
    // getting right at the source: the checker is the net, not the rule.
    return op == Op::EQ || op == Op::DISTINCT || op == Op::LE || op == Op::LT
        || op == Op::GE || op == Op::GT;
}

bool isConnective(Op op) {
    return op == Op::AND || op == Op::OR || op == Op::NOT || op == Op::XOR
        || op == Op::IMPLIES;
}

/** The eight bit-vector orderings, which yield Bool rather than bits. */
bool isBitVecComparison(Op op) {
    switch (op) {
    case Op::BV_ULT: case Op::BV_ULE: case Op::BV_UGT: case Op::BV_UGE:
    case Op::BV_SLT: case Op::BV_SLE: case Op::BV_SGT: case Op::BV_SGE:
        return true;
    default:
        return false;
    }
}

/** Every bit-vector operator whose result is a bit-vector of its first
 *  argument's width -- so not the comparisons, not concat, not the indexed
 *  ones, each of which computes a width of its own. */
bool isWidthPreservingBitVec(Op op) {
    switch (op) {
    case Op::BV_NOT:  case Op::BV_NEG:
    case Op::BV_AND:  case Op::BV_OR:   case Op::BV_XOR:
    case Op::BV_NAND: case Op::BV_NOR:  case Op::BV_XNOR:
    case Op::BV_ADD:  case Op::BV_SUB:  case Op::BV_MUL:
    case Op::BV_UDIV: case Op::BV_UREM:
    case Op::BV_SDIV: case Op::BV_SREM: case Op::BV_SMOD:
    case Op::BV_SHL:  case Op::BV_LSHR: case Op::BV_ASHR:
        return true;
    default:
        return false;
    }
}

/** The three integer division conventions and their remainders. DIV_REAL is
 *  deliberately not one of them: it yields Real and has no sibling to disagree
 *  with. */
bool isIntegerDivision(Op op) {
    switch (op) {
    case Op::DIV_EUCLID: case Op::DIV_TRUNC: case Op::DIV_FLOOR:
    case Op::MOD_EUCLID: case Op::MOD_TRUNC: case Op::MOD_FLOOR:
        return true;
    default:
        return false;
    }
}

/** The floating-point operators that take a RoundingMode first. */
bool isFloatRounded(Op op) {
    switch (op) {
    case Op::FP_ADD: case Op::FP_SUB: case Op::FP_MUL: case Op::FP_DIV:
    case Op::FP_FMA: case Op::FP_SQRT: case Op::FP_ROUND_TO_INTEGRAL:
        return true;
    default:
        return false;
    }
}

/** Float-valued and taking no rounding mode. */
bool isFloatUnrounded(Op op) {
    switch (op) {
    case Op::FP_ABS: case Op::FP_NEG:
    case Op::FP_REM: case Op::FP_MIN: case Op::FP_MAX:
        return true;
    default:
        return false;
    }
}

/** Float-argumented and Bool-valued: the four orderings, fp.eq, and the seven
 *  classification predicates. */
bool isFloatPredicate(Op op) {
    switch (op) {
    case Op::FP_LEQ: case Op::FP_LT: case Op::FP_GEQ: case Op::FP_GT:
    case Op::FP_EQ:
    case Op::FP_IS_NORMAL: case Op::FP_IS_SUBNORMAL: case Op::FP_IS_ZERO:
    case Op::FP_IS_INFINITE: case Op::FP_IS_NAN: case Op::FP_IS_NEGATIVE:
    case Op::FP_IS_POSITIVE:
        return true;
    default:
        return false;
    }
}

} // namespace

bool isFloatOp(Op op) {
    return isFloatRounded(op) || isFloatUnrounded(op) || isFloatPredicate(op);
}


bool isRegexOp(Op op) {
    switch (op) {
    case Op::STR_TO_RE: case Op::STR_IN_RE:
    case Op::RE_CONCAT: case Op::RE_UNION: case Op::RE_INTER: case Op::RE_DIFF:
    case Op::RE_STAR: case Op::RE_PLUS: case Op::RE_OPT: case Op::RE_COMPLEMENT:
    case Op::RE_RANGE: case Op::RE_LOOP:
        return true;
    default:
        return false;
    }
}

bool isConversionOp(Op op) {
    switch (op) {
    case Op::TO_INT: case Op::TO_REAL:
    case Op::BV_TO_NAT: case Op::BV_TO_INT: case Op::INT_TO_BV:
    case Op::FP_TO_REAL: case Op::FP_TO_IEEE_BV:
    case Op::FP_TO_SBV: case Op::FP_TO_UBV:
    case Op::TO_FP: case Op::TO_FP_UNSIGNED:
    case Op::IEEE_BV_TO_FP:
    // A predicate rather than a conversion, and grouped here because that is
    // where SMT-LIB puts it and because the lowering treats the whole group as
    // "prefix application of a name" -- which is all is_int needs.
    case Op::IS_INT:
        return true;
    default:
        return false;
    }
}


bool isSetOp(Op op) {
    switch (op) {
    case Op::SET_SINGLETON: case Op::SET_UNION: case Op::SET_INTER:
    case Op::SET_MINUS: case Op::SET_MEMBER: case Op::SET_SUBSET:
    case Op::SET_CARD: case Op::SET_INSERT: case Op::SET_COMPLEMENT:
        return true;
    default:
        return false;
    }
}

bool isTupleOp(Op op) {
    switch (op) {
    case Op::TUPLE: case Op::TUPLE_SELECT: case Op::TUPLE_UPDATE:
    case Op::TUPLE_PROJECT:
        return true;
    default:
        return false;
    }
}

bool isStringOp(Op op) {
    switch (op) {
    case Op::STR_CONCAT: case Op::STR_LEN: case Op::STR_AT: case Op::STR_SUBSTR:
    case Op::STR_INDEXOF: case Op::STR_REPLACE: case Op::STR_REPLACE_ALL:
    case Op::STR_CONTAINS: case Op::STR_PREFIXOF: case Op::STR_SUFFIXOF:
    case Op::STR_LT: case Op::STR_LE:
    case Op::STR_TO_INT: case Op::STR_FROM_INT:
    case Op::STR_TO_CODE: case Op::STR_FROM_CODE:
    case Op::STR_IS_DIGIT:
    case Op::STR_INDEXOF_RE: case Op::STR_REPLACE_RE: case Op::STR_REPLACE_RE_ALL:
        return true;
    default:
        return false;
    }
}

bool isBitVecOp(Op op) {
    return isBitVecComparison(op) || isWidthPreservingBitVec(op)
        || op == Op::BV_CONCAT || op == Op::BV_EXTRACT
        || op == Op::BV_ZERO_EXTEND || op == Op::BV_SIGN_EXTEND
        || op == Op::BV_ROTATE_LEFT || op == Op::BV_ROTATE_RIGHT
        || op == Op::BV_REPEAT || op == Op::BV_COMP;
}

namespace {

/** REAL dominates INT; BOOL only survives when every argument is BOOL. */
Sort widen(const std::vector<ExprPtr>& args) {
    SortKind k = SortKind::BOOL;
    for (const auto& a : args) {
        condAssert(a != nullptr, "mkOp: null argument");
        if (a->sort.kind == SortKind::REAL) {
            return Sort::real();
        }
        if (a->sort.kind == SortKind::INT) {
            k = SortKind::INT;
        }
    }
    return Sort{k};
}

// The HIR is immutable and may share large subexpressions. Traverse each
// shared node once, without copying ExprPtr handles (which would inflate the
// reference count). Ordinary trees need no visited entry.
template <typename Visitor>
void visitDag(const ExprPtr& root, std::unordered_set<const Expr*>& shared,
              Visitor&& visit) {
    std::vector<const ExprPtr*> pending{&root};
    while (!pending.empty()) {
        const auto& expr = *pending.back();
        pending.pop_back();
        if (!expr) { continue; }
        if (expr.use_count() > 1 && !shared.insert(expr.get()).second) { continue; }
        visit(expr);
        for (const auto& arg : expr->args) { pending.push_back(&arg); }
    }
}

/** Every literal kind. Listing only two of them made (bvmul x #b10) count as
 *  nonlinear, because a bit-vector constant was read as a variable -- the same
 *  omission as the one in isNonlinearOperation, pointing the other way. */
bool isConstant(const ExprPtr& e) {
    switch (e->kind) {
    case ExprKind::LIT_INT:
    case ExprKind::LIT_BOOL:
    case ExprKind::LIT_BITVEC:
    case ExprKind::LIT_STRING:
    case ExprKind::LIT_ROUNDING_MODE:
    case ExprKind::LIT_REAL:
    case ExprKind::LIT_FLOAT:
    case ExprKind::LIT_REGLAN:
    case ExprKind::LIT_SET:
    case ExprKind::LIT_TUPLE_UNIT:
        return true;
    default:
        return false;
    }
}

/** A product is nonlinear once at least two factors are not constants. */
bool isNonlinearOperation(const ExprPtr& e) {
    if (!e || e->kind != ExprKind::OP) {
        return false;
    }
    if (e->op == Op::MUL || e->op == Op::BV_MUL) {
        int non_const = 0;
        for (const auto& a : e->args) {
            if (!isConstant(a)) {
                ++non_const;
            }
        }
        if (non_const >= 2) {
            return true;
        }
    }
    // Bit-vector operators that are nonlinear in their *second* argument.
    //
    // This function feeds ConstraintModel::features(), which the experiment
    // tabulates per instance, so an omission here does not fail loudly -- it
    // reports a corpus as linear that is not. bvmul above is the obvious case;
    // these are the ones that are easy to miss:
    //
    //   - division and remainder by a variable divisor, for the same reason
    //     (/ x y) is nonlinear over the integers;
    //   - a variable shift distance, because (bvshl x y) is multiplication by
    //     2^y, and a solver bit-blasts it as such.
    //
    // A constant second argument is linear in each case and stays unreported.
    if (e->args.size() == 2 && !isConstant(e->args[1])) {
        switch (e->op) {
        case Op::BV_UDIV: case Op::BV_SDIV:
        case Op::BV_UREM: case Op::BV_SREM: case Op::BV_SMOD:
        case Op::BV_SHL:  case Op::BV_LSHR: case Op::BV_ASHR:
        // Integer and real division by a non-constant divisor is nonlinear for
        // the same reason the bit-vector ones are, and this switch has a
        // `default:` -- so the arithmetic divisions had to be named here or
        // they would have been classified linear in silence. `x div y` with a
        // variable y is exactly as far outside LIA as `x * y` is.
        case Op::DIV_EUCLID: case Op::DIV_TRUNC: case Op::DIV_FLOOR:
        case Op::MOD_EUCLID: case Op::MOD_TRUNC: case Op::MOD_FLOOR:
        case Op::DIV_REAL:
            return true;
        default:
            break;
        }
    }
    return false;
}

} // namespace

Sort::~Sort() noexcept {
    if (!index && !elem && args.empty()) return;
    SortReleaseQueue local;
    const bool outer = releasingSorts == nullptr;
    if (outer) releasingSorts = &local;
    auto& queue = *releasingSorts;
    enqueueSort(index, queue);
    enqueueSort(elem, queue);
    for (auto& child : args) enqueueSort(child, queue);
    if (!outer) return;
    // No heap storage is acquired here, even for a branching DAG or an Array
    // with no argument vector to reuse. Only dying nodes' semantic edges move;
    // still-live/const descendants expose mutable, synchronized queue scratch.
    // Concurrent weak_ptr::lock is harmless: no use_count snapshot is used.
    // The queue pins its entries until the owning thread removes their link.
    while (queue.head) {
        auto& link = queue.head->reclamation;
        while (link.busy.test_and_set(std::memory_order_acquire)) {}
        queue.head = link.next;
        link.next = nullptr;
        auto child = std::move(link.owner);
        link.busy.clear(std::memory_order_release);
        // An actual last release enters one nested destructor, which only
        // enqueues children and returns. No depth-dependent call chain forms.
        child.reset();
    }
    releasingSorts = nullptr;
}

Expr::~Expr() noexcept {
    if (args.empty()) { return; }

    if (releasingExpressions) {
        // This object already has no strong owners. Moving its own operands is
        // valid even for a const allocation; no live child's args are changed.
        // Move before clearing so none of these references can recursively
        // release a grandchild. The outer destructor drains them after return.
        try {
            releasingExpressions->insert(releasingExpressions->end(),
                std::make_move_iterator(args.begin()), std::make_move_iterator(args.end()));
        } catch (const std::bad_alloc&) {
            abortExpressionRelease("SOMTParser HIR destruction: memory allocation failed\n");
        } catch (const std::length_error&) {
            abortExpressionRelease("SOMTParser HIR destruction: memory allocation failed (worklist capacity)\n");
        }
        args.clear();
        return;
    }

    // Reuse this root's already allocated operand buffer. A chain requires no
    // allocation. Each child whose final reference is released enqueues only
    // its immediate operands, bounding Expr destructor nesting to two frames.
    // Dropping a reference to a still-shared node does not visit its subtree.
    std::vector<ExprPtr> pending;
    pending.swap(args);
    releasingExpressions = &pending;
    while (!pending.empty()) {
        ExprPtr child = std::move(pending.back());
        pending.pop_back();
        child.reset();
    }
    releasingExpressions = nullptr;
}

ExprPtr mkBool(bool v, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_BOOL;
    e->sort = Sort::boolean();
    e->bool_value = v;
    e->loc = std::move(loc);
    return e;
}

ExprPtr mkInt(long long v, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_INT;
    e->sort = Sort::integer();
    e->int_value = v;
    e->name = std::to_string(v);
    e->loc = std::move(loc);
    return e;
}

ExprPtr mkIdent(std::string name, Sort sort, SourceLoc loc) {
    condAssert(!name.empty(), "mkIdent: empty name");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::IDENT;
    e->sort = sort;
    e->name = std::move(name);
    e->loc = std::move(loc);
    return e;
}

ExprPtr mkBoundVar(std::string name, Sort sort, SourceLoc loc) {
    condAssert(!name.empty(), "mkBoundVar: empty name");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::BOUND_VAR;
    e->sort = std::move(sort);
    e->name = std::move(name);
    e->loc = std::move(loc);
    return e;
}

namespace {
ExprPtr mkQuantifier(ExprKind kind, std::vector<Binder> binders, ExprPtr body,
                     SourceLoc loc) {
    condAssert(!binders.empty(), "quantifier with no bound variables");
    condAssert(body != nullptr, "quantifier with no body");
    auto e = std::make_shared<Expr>();
    e->kind = kind;
    e->sort = Sort::boolean();
    e->binders = std::move(binders);
    e->args = {std::move(body)};
    e->loc = std::move(loc);
    return e;
}
} // namespace

ExprPtr mkForall(std::vector<Binder> binders, ExprPtr body, SourceLoc loc) {
    return mkQuantifier(ExprKind::FORALL, std::move(binders), std::move(body),
                        std::move(loc));
}

ExprPtr mkExists(std::vector<Binder> binders, ExprPtr body, SourceLoc loc) {
    return mkQuantifier(ExprKind::EXISTS, std::move(binders), std::move(body),
                        std::move(loc));
}

ExprPtr mkBitVec(std::string literal, unsigned width, SourceLoc loc) {
    condAssert(!literal.empty(), "mkBitVec: empty literal");
    condAssert(width > 0, "mkBitVec: zero width");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_BITVEC;
    e->sort = Sort::bitvec(width);
    e->name = std::move(literal);
    e->loc = std::move(loc);
    return e;
}

ExprPtr mkString(std::string value, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_STRING;
    e->sort = Sort::string();
    e->name = std::move(value);
    e->loc = std::move(loc);
    return e;
}

ExprPtr mkApply(std::string name, Sort result, std::vector<ExprPtr> args,
                SourceLoc loc) {
    condAssert(!name.empty(), "mkApply: empty name");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::APPLY;
    e->sort = std::move(result);
    e->name = std::move(name);
    e->args = std::move(args);
    e->loc = std::move(loc);
    return e;
}

ExprPtr substituteIdents(const ExprPtr& e,
                         const std::unordered_map<std::string, std::string>& names,
                         const std::unordered_map<std::string, Sort>& sorts) {
    if (!e || names.empty()) { return e; }
    struct Scope {
        std::unordered_map<std::string, std::string> names;
        std::unordered_map<const Expr*, ExprPtr> rewritten;
    };
    // Scopes live in a flat arena, not a shared_ptr parent chain. A shared
    // expression under a binder can have a different result from the same
    // expression outside it, so memoization must include the lexical scope.
    std::vector<Scope> scopes{{names, {}}};
    struct Frame {
        ExprPtr expr;
        std::size_t scope;
        std::size_t inner;
        bool entered = false;
        bool changed = false;
        std::vector<ExprPtr> args{};
    };
    std::vector<Frame> stack{{e, 0, 0}};
    while (!stack.empty()) {
        auto& frame = stack.back();
        const auto& node = frame.expr;
        if (!frame.entered) {
            frame.entered = true;
            if (node->kind == ExprKind::IDENT) {
                ExprPtr result = node;
                const auto it = scopes[frame.scope].names.find(node->name);
                if (it != scopes[frame.scope].names.end()) {
                    const auto si = sorts.find(node->name);
                    result = mkIdent(it->second, si == sorts.end() ? node->sort : si->second,
                                     node->loc);
                }
                scopes[frame.scope].rewritten.emplace(node.get(), std::move(result));
                stack.pop_back();
                continue;
            }
            if (node->kind == ExprKind::FORALL || node->kind == ExprKind::EXISTS) {
                for (const Binder& binder : node->binders) {
                    if (!scopes[frame.inner].names.count(binder.name)) continue;
                    if (frame.inner == frame.scope) {
                        Scope inner{scopes[frame.scope].names, {}};
                        frame.inner = scopes.size();
                        scopes.push_back(std::move(inner));
                    }
                    scopes[frame.inner].names.erase(binder.name);
                }
            }
            frame.args.reserve(node->args.size());
        }
        if (frame.args.size() < node->args.size()) {
            const auto& child = node->args[frame.args.size()];
            if (!child) { frame.args.push_back(nullptr); continue; }
            const auto found = scopes[frame.inner].rewritten.find(child.get());
            if (found == scopes[frame.inner].rewritten.end()) {
                const auto inner = frame.inner;
                stack.push_back({child, inner, inner});
                continue;
            }
            frame.changed |= found->second != child;
            frame.args.push_back(found->second);
            continue;
        }
        ExprPtr result = node;
        if (frame.changed) {
            // Copy all metadata, including indexed operators and stored sorts.
            auto changed = std::make_shared<Expr>(*node);
            changed->args = std::move(frame.args);
            result = std::move(changed);
        }
        scopes[frame.scope].rewritten.emplace(node.get(), std::move(result));
        stack.pop_back();
    }
    return scopes[0].rewritten.at(e.get());
}

ExprPtr mkGlobal(std::string name, std::vector<ExprPtr> args, SourceLoc loc) {
    condAssert(!name.empty(), "mkGlobal: empty name");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::GLOBAL;
    e->sort = name == "count_value" ? Sort::integer() : Sort::boolean();
    e->name = std::move(name);
    e->args = std::move(args);
    e->loc = std::move(loc);
    return e;
}

bool sameSort(const Sort& a, const Sort& b) {
    using Pair = std::pair<const Sort*, const Sort*>;
    struct PairHash {
        std::size_t operator()(const Pair& p) const noexcept {
            return std::hash<const Sort*>{}(p.first)
                 ^ (std::hash<const Sort*>{}(p.second) << 1);
        }
    };
    std::vector<Pair> pending{{&a, &b}};
    std::unordered_set<Pair, PairHash> compared;
    while (!pending.empty()) {
        const auto pair = pending.back();
        pending.pop_back();
        if (!compared.insert(pair).second) continue;
        const auto& left = *pair.first;
        const auto& right = *pair.second;
        if (left.kind != right.kind) return false;
        switch (left.kind) {
        case SortKind::BITVEC:
            if (left.width != right.width) return false;
            break;
        case SortKind::FLOAT:
            if (left.exponent_bits != right.exponent_bits
                || left.significand_bits != right.significand_bits) return false;
            break;
        case SortKind::UNINTERPRETED: case SortKind::DATATYPE:
            // Both the constructor name and its ordered arguments identify a
            // parametric sort. Tuple fields have no constructor name.
            if (left.name != right.name) return false;
            [[fallthrough]];
        case SortKind::TUPLE:
            if (left.args.size() != right.args.size()) return false;
            for (std::size_t i = 0; i < left.args.size(); ++i) {
                if (!left.args[i] || !right.args[i]) return false;
                pending.emplace_back(left.args[i].get(), right.args[i].get());
            }
            break;
        case SortKind::SET:
            if (!left.elem || !right.elem) return false;
            pending.emplace_back(left.elem.get(), right.elem.get());
            break;
        case SortKind::ARRAY:
            // Null components are malformed, including when comparing a sort
            // with itself. Pointer equality must not bypass this validation.
            if (!left.index || !left.elem || !right.index || !right.elem) return false;
            pending.emplace_back(left.elem.get(), right.elem.get());
            pending.emplace_back(left.index.get(), right.index.get());
            break;
        default:
            break;
        }
    }
    return true;
}

std::string toString(const Sort& s) {
    struct Task {
        const Sort* sort;
        const char* text = nullptr;
    };
    std::vector<Task> pending{{&s}};
    std::string out;
    while (!pending.empty()) {
        const auto task = pending.back();
        pending.pop_back();
        if (task.text) { out += task.text; continue; }
        const Sort& node = *task.sort;
        switch (node.kind) {
        case SortKind::BOOL: out += "Bool"; break;
        case SortKind::INT: out += "Int"; break;
        case SortKind::REAL: out += "Real"; break;
        case SortKind::STRING: out += "String"; break;
        case SortKind::ROUNDING_MODE: out += "RoundingMode"; break;
        case SortKind::REGLAN: out += "RegLan"; break;
        case SortKind::BITVEC:
            out += "(_ BitVec " + std::to_string(node.width) + ")";
            break;
        case SortKind::FLOAT:
            out += "(_ FloatingPoint " + std::to_string(node.exponent_bits) + " "
                 + std::to_string(node.significand_bits) + ")";
            break;
        case SortKind::SET:
            if (!node.elem) { out += "<malformed Set>"; break; }
            out += "(Set ";
            pending.push_back({nullptr, ")"});
            pending.push_back({node.elem.get()});
            break;
        case SortKind::ARRAY:
            if (!node.index || !node.elem) { out += "<malformed Array>"; break; }
            out += "(Array ";
            pending.push_back({nullptr, ")"});
            pending.push_back({node.elem.get()});
            pending.push_back({nullptr, " "});
            pending.push_back({node.index.get()});
            break;
        case SortKind::TUPLE: case SortKind::DATATYPE: case SortKind::UNINTERPRETED: {
            const bool tuple = node.kind == SortKind::TUPLE;
            const bool datatype = node.kind == SortKind::DATATYPE;
            if (!tuple && node.name.empty()) {
                out += datatype ? "<unnamed datatype>" : "<unnamed sort>";
                break;
            }
            if (node.args.empty()) { out += tuple ? "UnitTuple" : node.name; break; }
            out += "(";
            out += tuple ? "Tuple" : node.name;
            pending.push_back({nullptr, ")"});
            for (auto it = node.args.rbegin(); it != node.args.rend(); ++it) {
                pending.push_back({it->get(), *it ? nullptr : datatype ? "<null>" : "<malformed>"});
                pending.push_back({nullptr, " "});
            }
            break;
        }
        default:
            condAssert(false, "Hir::toString: unhandled SortKind");
            out += "<unknown>";
        }
    }
    return out;
}

ExprPtr mkOp(Op op, std::vector<ExprPtr> args, SourceLoc loc) {
    condAssert(!args.empty(), "mkOp: no arguments");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::OP;
    e->op   = op;
    // The result sort of a connective or comparison is Bool whatever the
    // arguments are; that the arguments are *allowed* to be what they are is a
    // separate question, answered by Uir::Hir::typeCheck. Deriving it here
    // without checking is what let `b + 1 > 0` on a Bool b reach the Parser
    // builders and abort the process.
    if (op == Op::ITE) {
        // The branches carry the sort, not the condition. Deriving it from
        // args[0] would make every ite a Bool -- right for a Boolean ite and
        // silently wrong for every other one, which is the worst split.
        condAssert(args.size() == 3, "ite takes a condition and two branches");
        condAssert(args[1] != nullptr, "ite: null branch");
        e->sort = args[1]->sort;
    } else if (op == Op::STORE || op == Op::ARRAY_MAP_AND
               || op == Op::ARRAY_MAP_OR || op == Op::ARRAY_MAP_NOT) {
        // (store a i v) is an array, not an element: the result sort is the
        // array's. Falling through to widen() would have made it Bool.
        //
        // Arity is NOT asserted here, and neither is SELECT's below. A frontend
        // calls mkOp on input it has not validated, so an abort turns a
        // malformed benchmark into an E_INTERNAL with no source location --
        // exactly the confusion translation/diagnostic.h reserves that code against.
        // A wrong count yields a sort typeCheck then rejects, with a location.
        e->sort = (!args.empty() && args[0] != nullptr) ? args[0]->sort
                                                        : Sort::boolean();
    } else if (op == Op::SELECT) {
        // (select a i) has the array's *element* sort. Deriving it from the
        // arguments' widening -- the arithmetic rule -- would give it the array
        // sort itself, which is a different type entirely.
        e->sort = (!args.empty() && args[0] != nullptr
                   && args[0]->sort.kind == SortKind::ARRAY && args[0]->sort.elem)
                      ? *args[0]->sort.elem
                      : Sort::boolean();   // malformed; typeCheck reports it
    } else if (isFloatPredicate(op)) {
        e->sort = Sort::boolean();
    } else if (isFloatRounded(op)) {
        // The rounding mode is args[0], so the value sort is args[1]'s. Deriving
        // it from args[0] would make every fp.add a RoundingMode.
        condAssert(args.size() >= 2, "a rounded float operator takes rm and a value");
        condAssert(args[1] != nullptr, "mkOp: null argument");
        e->sort = args[1]->sort;
    } else if (isFloatUnrounded(op)) {
        condAssert(args[0] != nullptr, "mkOp: null argument");
        e->sort = args[0]->sort;
    } else if (isSetOp(op)) {
        condAssert(!args.empty() && args[0] != nullptr, "mkOp: null argument");
        switch (op) {
        case Op::SET_MEMBER: case Op::SET_SUBSET:
            e->sort = Sort::boolean();
            break;
        case Op::SET_CARD:
            e->sort = Sort::integer();
            break;
        case Op::SET_SINGLETON:
            e->sort = Sort::set(args[0]->sort);
            break;
        case Op::SET_INSERT:
            // The set is LAST, so taking args[0] here would give the element
            // sort -- which for a (Set Int) is Int, and type-checks nowhere.
            e->sort = args.back() != nullptr ? args.back()->sort : Sort::boolean();
            break;
        default:
            e->sort = args[0]->sort;
            break;
        }
    } else if (isTupleOp(op)) {
        if (op == Op::TUPLE) {
            // The sort is BUILT from the arguments -- a tuple sort is never
            // declared, it is written where it is used -- so the constructor
            // is the one tuple operator that needs no index and can go through
            // mkOp. A null argument is left to typeCheck, as everywhere else
            // here, so that a malformed model is a diagnostic and not an abort.
            std::vector<Sort> fields;
            fields.reserve(args.size());
            for (const auto& a : args) {
                fields.push_back(a ? a->sort : Sort::boolean());
            }
            e->sort = Sort::tuple(std::move(fields));
        } else {
            // tuple.select's result is the i-th FIELD, tuple.update's is the
            // whole tuple, tuple.project's is a tuple of the chosen fields --
            // and `i` is in Expr::indices, which mkOp cannot see. Deriving a
            // sort here without it would give tuple.select the tuple's own
            // sort, which type-checks nowhere and reads as a lowering bug far
            // from its cause.
            condAssert(false, "use the indexed builder for this tuple operator");
        }
    } else if (isRegexOp(op)) {
        e->sort = (op == Op::STR_IN_RE) ? Sort::boolean() : Sort::regLan();
    } else if (isConversionOp(op)) {
        switch (op) {
        case Op::TO_INT: case Op::BV_TO_NAT: case Op::BV_TO_INT:
            e->sort = Sort::integer();
            break;
        case Op::TO_REAL: case Op::FP_TO_REAL:
            e->sort = Sort::real();
            break;
        case Op::IS_INT:
            e->sort = Sort::boolean();
            break;
        case Op::FP_TO_IEEE_BV:
            // The IEEE bit pattern is exactly as wide as the format.
            condAssert(!args.empty() && args[0] != nullptr, "mkOp: null argument");
            e->sort = Sort::bitvec(args[0]->sort.exponent_bits
                                   + args[0]->sort.significand_bits);
            break;
        default:
            // INT_TO_BV, FP_TO_SBV/UBV, TO_FP: indexed, so the width or format
            // comes from Expr::indices, which mkOp cannot see.
            condAssert(false, "use the indexed builder for this conversion");
        }
    } else if (isStringOp(op)) {
        switch (op) {
        case Op::STR_LEN: case Op::STR_INDEXOF: case Op::STR_TO_INT:
        case Op::STR_TO_CODE: case Op::STR_INDEXOF_RE:
            e->sort = Sort::integer();
            break;
        case Op::STR_CONTAINS: case Op::STR_PREFIXOF: case Op::STR_SUFFIXOF:
        case Op::STR_LT: case Op::STR_LE: case Op::STR_IS_DIGIT:
            e->sort = Sort::boolean();
            break;
        case Op::STR_FROM_CODE:
            e->sort = Sort::string();
            break;
        default:
            e->sort = Sort::string();
            break;
        }
    } else if (isBitVecComparison(op)) {
        e->sort = Sort::boolean();
    } else if (op == Op::BV_CONCAT) {
        // The one non-indexed bit-vector operator whose width is neither its
        // first argument's nor fixed. A non-bit-vector argument contributes
        // nothing, which yields a width the checker then rejects -- better than
        // asserting here, since mkOp is what a frontend calls on input it has
        // not validated.
        unsigned total = 0;
        for (const auto& a : args) {
            condAssert(a != nullptr, "mkOp: null argument");
            if (a->sort.kind == SortKind::BITVEC) { total += a->sort.width; }
        }
        e->sort = Sort::bitvec(total);
    } else if (isWidthPreservingBitVec(op)) {
        condAssert(args[0] != nullptr, "mkOp: null argument");
        e->sort = args[0]->sort;
    } else if (op == Op::BV_COMP) {
        // One bit, always, whatever the arguments' width -- and NOT a Bool.
        // Getting this from args[0] would make `(bvcomp x y)` as wide as x, and
        // the result would then concatenate and compare like a value it is not.
        e->sort = Sort::bitvec(1);
    } else if (op == Op::BV_EXTRACT || op == Op::BV_ZERO_EXTEND
               || op == Op::BV_SIGN_EXTEND || op == Op::BV_ROTATE_LEFT
               || op == Op::BV_ROTATE_RIGHT || op == Op::BV_REPEAT) {
        // Indexed: the width comes from the indices, which mkOp cannot see.
        // The rotations are width-preserving and so would survive the generic
        // path, and are refused here anyway -- a rotation built without its
        // index is a rotation by an unknown amount, which prints as
        // `(_ rotate_left )` and is not a term.
        condAssert(false, "use mkBvExtract / mkBvExtend / mkBvRotate / "
                          "mkBvRepeat for indexed operators");
    } else if (op == Op::CONST_ARRAY) {
        // Indexed by the RESULT sort: the value fixes the element sort and
        // says nothing about the index sort, so there is nothing to derive.
        condAssert(false, "use mkConstArray: the array sort is not derivable");
    } else if (op == Op::IS_DIVISIBLE) {
        // Indexed by the divisor, which mkOp cannot see.
        condAssert(false, "use mkIsDivisible: the divisor is an index");
    } else if (op == Op::DIV_REAL) {
        // Not widen(): `(/ 1 2)` has two Int arguments and is one half, so
        // widening would give it sort Int and the literal would then be folded
        // to 0 -- a wrong answer that type-checks, which is the worst kind.
        e->sort = Sort::real();
    } else if (isIntegerDivision(op)) {
        // Int in, Int out, stated rather than widened. typeCheck refuses a Real
        // argument, but mkOp runs first and on unvalidated frontend input, so
        // relying on widen() here would give a Real-argumented `div` sort Real
        // and let it reach the checker describing itself as something it is
        // not.
        e->sort = Sort::integer();
    } else {
        e->sort = (isComparison(op) || isConnective(op)) ? Sort::boolean() : widen(args);
    }
    e->args = std::move(args);
    e->loc = std::move(loc);
    return e;
}

ExprPtr mkReal(std::string decimal_or_rational, SourceLoc loc) {
    // GMP rejects a leading plus. Remove it only from a complete decimal or
    // rational spelling; malformed text must still reach typeCheck unchanged.
    if (decimal_or_rational.size() > 1 && decimal_or_rational.front() == '+') {
        const auto digit = [](char c) { return c >= '0' && c <= '9'; };
        std::size_t end = 1;
        while (end < decimal_or_rational.size() && digit(decimal_or_rational[end])) { ++end; }
        const bool integer_part = end > 1;
        bool fractional_part = true;
        if (end < decimal_or_rational.size()
            && (decimal_or_rational[end] == '.' || decimal_or_rational[end] == '/')) {
            const std::size_t first = ++end;
            while (end < decimal_or_rational.size() && digit(decimal_or_rational[end])) { ++end; }
            fractional_part = end > first;
        }
        if (integer_part && fractional_part && end == decimal_or_rational.size()) {
            decimal_or_rational.erase(decimal_or_rational.begin());
        }
    }
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_REAL;
    e->sort = Sort::real();
    e->name = std::move(decimal_or_rational);
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkFloat(std::string decimal, unsigned exponent, unsigned significand,
                SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_FLOAT;
    e->sort = Sort::floating(exponent, significand);
    e->name = std::move(decimal);
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkInt(std::string decimal, SourceLoc loc) {
    // A leading plus is valid source syntax, but neither from_chars nor GMP's
    // decimal integer parser accepts it. Preserve malformed text for typeCheck.
    if (decimal.size() > 1 && decimal.front() == '+'
        && std::all_of(decimal.begin() + 1, decimal.end(),
                       [](char c) { return c >= '0' && c <= '9'; })) {
        decimal.erase(decimal.begin());
    }
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_INT;
    e->sort = Sort::integer();
    e->name = std::move(decimal);
    // Filled in when it fits, so the common path costs nothing; left at zero
    // otherwise, and fitsInt64 is what tells the two apart. Setting it to some
    // saturated value instead would be a wrong number that looks usable.
    //
    // from_chars and not strtoll, for exactly that reason: strtoll SATURATES to
    // LLONG_MAX on overflow, so a 2^127 coefficient would arrive as
    // 9223372036854775807 -- a plausible-looking integer that is not the one in
    // the file. from_chars reports the overflow and leaves the value untouched.
    const char* first = e->name.data();
    const char* last = first + e->name.size();
    long long v = 0;
    const auto conv = std::from_chars(first, last, v);
    if (conv.ec == std::errc() && conv.ptr == last) { e->int_value = v; }
    e->loc = std::move(loc);
    return e;
}

bool fitsInt64(const Expr& e) {
    if (e.kind != ExprKind::LIT_INT) { return false; }
    if (e.name.empty()) { return true; }   // built by mkInt(long long)
    const char* first = e.name.data();
    const char* last = first + e.name.size();
    long long v = 0;
    const auto conv = std::from_chars(first, last, v);
    return conv.ec == std::errc() && conv.ptr == last;
}

ExprPtr mkRoundingMode(std::string mode, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_ROUNDING_MODE;
    e->sort = Sort::roundingMode();
    // Not validated here: a frontend calls this on unvalidated input, and
    // hir/typecheck.h reports an unknown name against a source location rather
    // than aborting. The engine's builder takes the name as a string, so an
    // unchecked one would otherwise reach the emitted script.
    e->name = std::move(mode);
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkDtConstructor(std::string name, Sort result, std::vector<ExprPtr> args,
                        SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::DT_CONSTRUCTOR;
    e->name = std::move(name);
    e->sort = std::move(result);
    e->args = std::move(args);
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkDtSelector(std::string name, Sort result, ExprPtr value, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::DT_SELECTOR;
    e->name = std::move(name);
    e->sort = std::move(result);
    e->args = {std::move(value)};
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkDtTester(std::string constructor_name, ExprPtr value, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::DT_TESTER;
    e->name = std::move(constructor_name);
    e->sort = Sort::boolean();
    e->args = {std::move(value)};
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkSetConst(std::string name, Sort set_sort, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_SET;
    e->sort = std::move(set_sort);
    e->name = std::move(name);
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkReglanConst(std::string name, SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_REGLAN;
    e->sort = Sort::regLan();
    e->name = std::move(name);
    e->loc  = std::move(loc);
    return e;
}

/** The shared shape of every indexed builder: one operator, its arguments, and
 *  the indices that say which function is being applied. */
static ExprPtr mkIndexed(Op op, std::vector<ExprPtr> args,
                         std::vector<unsigned> indices, Sort sort,
                         SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind    = ExprKind::OP;
    e->op      = op;
    e->indices = std::move(indices);
    e->sort    = std::move(sort);
    e->args    = std::move(args);
    e->loc     = std::move(loc);
    return e;
}

ExprPtr mkReLoop(ExprPtr r, unsigned lo, unsigned hi, SourceLoc loc) {
    return mkIndexed(Op::RE_LOOP, {std::move(r)}, {lo, hi}, Sort::regLan(),
                     std::move(loc));
}

ExprPtr mkIntToBv(ExprPtr n, unsigned width, SourceLoc loc) {
    return mkIndexed(Op::INT_TO_BV, {std::move(n)}, {width},
                     Sort::bitvec(width), std::move(loc));
}

ExprPtr mkFpToBv(Op op, ExprPtr rm, ExprPtr x, unsigned width, SourceLoc loc) {
    condAssert(op == Op::FP_TO_SBV || op == Op::FP_TO_UBV,
               "mkFpToBv: not a float-to-bit-vector conversion");
    return mkIndexed(op, {std::move(rm), std::move(x)}, {width},
                     Sort::bitvec(width), std::move(loc));
}

ExprPtr mkToFp(Op op, ExprPtr rm, ExprPtr x, unsigned exponent,
               unsigned significand, SourceLoc loc) {
    condAssert(op == Op::TO_FP || op == Op::TO_FP_UNSIGNED,
               "mkToFp: not a to_fp conversion");
    return mkIndexed(op, {std::move(rm), std::move(x)},
                     {exponent, significand},
                     Sort::floating(exponent, significand), std::move(loc));
}

ExprPtr mkIeeeBvToFp(ExprPtr x, unsigned exponent, unsigned significand,
                     SourceLoc loc) {
    return mkIndexed(Op::IEEE_BV_TO_FP, {std::move(x)},
                     {exponent, significand},
                     Sort::floating(exponent, significand), std::move(loc));
}

ExprPtr mkTupleUnit(SourceLoc loc) {
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::LIT_TUPLE_UNIT;
    e->sort = Sort::tuple({});
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkTuple(std::vector<ExprPtr> fields, SourceLoc loc) {
    condAssert(!fields.empty(), "mkTuple: the nullary tuple is mkTupleUnit()");
    return mkOp(Op::TUPLE, std::move(fields), std::move(loc));
}

/** The i-th field sort of @p t, or Bool when @p t is not a tuple or @p index is
 *  past its end.
 *
 *  Bool as the malformed marker rather than an abort, for the reason mkOp's
 *  SELECT branch gives: a frontend calls these on input it has not validated,
 *  and typeCheck turns the mismatch into a diagnostic carrying a source
 *  location. An abort here would report a benchmark's type error as a crash. */
static Sort tupleFieldSort(const ExprPtr& t, unsigned index) {
    if (!t || t->sort.kind != SortKind::TUPLE
        || index >= t->sort.args.size() || !t->sort.args[index]) {
        return Sort::boolean();
    }
    return *t->sort.args[index];
}

ExprPtr mkTupleSelect(ExprPtr t, unsigned index, SourceLoc loc) {
    Sort field = tupleFieldSort(t, index);
    return mkIndexed(Op::TUPLE_SELECT, {std::move(t)}, {index},
                     std::move(field), std::move(loc));
}

ExprPtr mkTupleUpdate(ExprPtr t, unsigned index, ExprPtr value, SourceLoc loc) {
    // The result is the TUPLE's sort, not the updated field's: an update
    // returns a new tuple. Taking the field sort here -- the same shape as
    // select, one argument along -- would make `((_ tuple.update 0) t 5)` an
    // Int, and the error would surface as an unrelated sort mismatch wherever
    // the result was used.
    Sort result = (t && t->sort.kind == SortKind::TUPLE) ? t->sort
                                                         : Sort::boolean();
    return mkIndexed(Op::TUPLE_UPDATE, {std::move(t), std::move(value)}, {index},
                     std::move(result), std::move(loc));
}

ExprPtr mkTupleProject(ExprPtr t, std::vector<unsigned> indices, SourceLoc loc) {
    std::vector<Sort> fields;
    fields.reserve(indices.size());
    bool well_formed = t && t->sort.kind == SortKind::TUPLE;
    for (unsigned i : indices) {
        if (!well_formed || i >= t->sort.args.size() || !t->sort.args[i]) {
            well_formed = false;
            break;
        }
        fields.push_back(*t->sort.args[i]);
    }
    // An empty projection is `UnitTuple` and is well formed; only a bad
    // argument or an out-of-range index falls back to Bool.
    Sort result = well_formed ? Sort::tuple(std::move(fields)) : Sort::boolean();
    return mkIndexed(Op::TUPLE_PROJECT, {std::move(t)}, std::move(indices),
                     std::move(result), std::move(loc));
}

ExprPtr mkBvExtract(ExprPtr x, unsigned hi, unsigned lo, SourceLoc loc) {
    condAssert(x != nullptr, "mkBvExtract: null argument");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::OP;
    e->op   = Op::BV_EXTRACT;
    // hi >= lo and hi < width are the checker's business, not this builder's:
    // a frontend calls it on unvalidated input, and a diagnostic naming the
    // source location beats an abort. The width recorded here is what the
    // indices say, so an out-of-range pair yields a sort the checker rejects
    // rather than one it silently accepts.
    e->indices = {hi, lo};
    e->sort = Sort::bitvec(hi >= lo ? hi - lo + 1 : 0);
    e->args = {std::move(x)};
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkBvExtend(Op op, ExprPtr x, unsigned by, SourceLoc loc) {
    condAssert(op == Op::BV_ZERO_EXTEND || op == Op::BV_SIGN_EXTEND,
               "mkBvExtend: not an extension operator");
    condAssert(x != nullptr, "mkBvExtend: null argument");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::OP;
    e->op   = op;
    e->indices = {by};
    const unsigned w = x->sort.kind == SortKind::BITVEC ? x->sort.width : 0;
    e->sort = Sort::bitvec(w + by);
    e->args = {std::move(x)};
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkBvRotate(Op op, ExprPtr x, unsigned by, SourceLoc loc) {
    condAssert(op == Op::BV_ROTATE_LEFT || op == Op::BV_ROTATE_RIGHT,
               "mkBvRotate: not a rotation operator");
    condAssert(x != nullptr, "mkBvRotate: null argument");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::OP;
    e->op   = op;
    e->indices = {by};
    // Width-preserving: a rotation by any amount, including more than the
    // width, moves the same bits around. SMT-LIB does not require the index to
    // be less than the width and neither does this.
    e->sort = x->sort;
    e->args = {std::move(x)};
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkConstArray(Sort array_sort, ExprPtr value, SourceLoc loc) {
    condAssert(value != nullptr, "mkConstArray: null value");
    condAssert(array_sort.kind == SortKind::ARRAY,
               "mkConstArray: the sort is not an array sort");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::OP;
    e->op   = Op::CONST_ARRAY;
    e->sort = std::move(array_sort);
    e->args = {std::move(value)};
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkIsDivisible(ExprPtr t, unsigned by, SourceLoc loc) {
    condAssert(t != nullptr, "mkIsDivisible: null argument");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::OP;
    e->op   = Op::IS_DIVISIBLE;
    e->indices = {by};
    e->sort = Sort::boolean();
    e->args = {std::move(t)};
    e->loc  = std::move(loc);
    return e;
}

ExprPtr mkBvRepeat(ExprPtr x, unsigned times, SourceLoc loc) {
    condAssert(x != nullptr, "mkBvRepeat: null argument");
    auto e = std::make_shared<Expr>();
    e->kind = ExprKind::OP;
    e->op   = Op::BV_REPEAT;
    e->indices = {times};
    const unsigned w = x->sort.kind == SortKind::BITVEC ? x->sort.width : 0;
    // times == 0 yields width 0, which is not a bit-vector sort; the checker
    // refuses it there, where the diagnostic can name the source location, for
    // the reason mkBvExtract leaves its range check to the checker.
    e->sort = Sort::bitvec(w * times);
    e->args = {std::move(x)};
    e->loc  = std::move(loc);
    return e;
}

const char* objectiveCombinationName(ObjectiveCombination c) {
    switch (c) {
    case ObjectiveCombination::SINGLE:        return "single";
    case ObjectiveCombination::LEXICOGRAPHIC: return "lexicographic";
    case ObjectiveCombination::PARETO:        return "pareto";
    case ObjectiveCombination::BOX:           return "box";
    case ObjectiveCombination::MINMAX:        return "minmax";
    case ObjectiveCombination::MAXMIN:        return "maxmin";
    }
    // A new combination must fail here rather than print a stand-in, which the
    // evaluation would read as a different experiment.
    condAssert(false, "objectiveCombinationName: unhandled ObjectiveCombination");
    return "";   // unreachable; condAssert always throws
}

namespace {

// For each node retain the result for three enclosing contexts: no
// quantifier, forall, and exists. A node shared below different quantifiers
// cannot be cached with one context-independent number.
using Alternations = std::array<std::size_t, 3>;
using AlternationCache = std::unordered_map<const Expr*, Alternations>;

std::size_t alternationsIn(const ExprPtr& root, AlternationCache& shared) {
    if (!root) { return 0; }
    struct Frame {
        const ExprPtr* expr;
        std::size_t next = 0;
        Alternations below{};
    };
    std::vector<Frame> stack{{&root}};
    while (!stack.empty()) {
        auto& frame = stack.back();
        const auto& expr = *frame.expr;
        const auto found = shared.find(expr.get());
        Alternations result{};
        if (found != shared.end()) {
            result = found->second;
        } else if (frame.next < expr->args.size()) {
            const auto& child = expr->args[frame.next++];
            if (child) { stack.push_back({&child}); }
            continue;
        } else {
            result = frame.below;
            if (expr->kind == ExprKind::FORALL || expr->kind == ExprKind::EXISTS) {
                const std::size_t own = expr->kind == ExprKind::FORALL ? 1 : 2;
                result.fill(frame.below[own]);
                // Equal adjacent quantifiers form one block. Only a change
                // from an existing enclosing block adds an alternation.
                ++result[3 - own];
            }
            if (expr.use_count() > 1) { shared.emplace(expr.get(), result); }
        }
        stack.pop_back();
        if (stack.empty()) { return result[0]; }
        for (std::size_t i = 0; i < result.size(); ++i) {
            stack.back().below[i] = std::max(stack.back().below[i], result[i]);
        }
    }
    return 0;
}

} // namespace

bool BoolVarRange::contains(const std::string& symbol, std::uint64_t* index) const {
    if (prefix.empty() || symbol.size() <= prefix.size()
        || symbol.compare(0, prefix.size(), prefix) != 0) return false;
    const char* first_digit=symbol.data()+prefix.size();
    const char* last_digit=symbol.data()+symbol.size();
    if (*first_digit=='0' && last_digit-first_digit>1) return false;
    std::uint64_t value=0;
    const auto parsed=std::from_chars(first_digit,last_digit,value);
    if (parsed.ec!=std::errc() || parsed.ptr!=last_digit || value<first
        || value-first>=count) return false;
    if (index) *index=value;
    return true;
}

std::string BoolVarRange::name(std::uint64_t offset) const {
    if (offset>=count || offset>std::numeric_limits<std::uint64_t>::max()-first)
        throw std::out_of_range("BoolVarRange::name offset is outside range");
    return prefix+std::to_string(first+offset);
}

bool ScalarVarRange::contains(const std::string& symbol, std::uint64_t* index) const {
    if (prefix.empty() || symbol.size() <= prefix.size() + suffix.size()
        || symbol.compare(0, prefix.size(), prefix) != 0
        || symbol.compare(symbol.size() - suffix.size(), suffix.size(), suffix) != 0) {
        return false;
    }
    const char* begin = symbol.data() + prefix.size();
    const char* end = symbol.data() + symbol.size() - suffix.size();
    if (*begin == '0' && end - begin > 1) { return false; }
    std::uint64_t value = 0;
    const auto parsed = std::from_chars(begin, end, value);
    if (parsed.ec != std::errc() || parsed.ptr != end || value < first
        || value - first >= count) { return false; }
    if (index) { *index = value; }
    return true;
}

std::string ScalarVarRange::name(std::uint64_t offset) const {
    if (offset >= count || offset > std::numeric_limits<std::uint64_t>::max() - first) {
        throw std::out_of_range("ScalarVarRange::name offset is outside range");
    }
    return prefix + std::to_string(first + offset) + suffix;
}

std::size_t ConstraintModel::maxQuantifierAlternations() const {
    std::size_t deepest = 0;
    AlternationCache shared;
    for (const auto& fn : funs) {
        if (fn.body) {
            deepest = std::max(deepest,
                               alternationsIn(fn.body, shared));
        }
    }
    for (const auto& c : constraints) {
        deepest = std::max(deepest, alternationsIn(c.formula, shared));
    }
    for (const auto& o : objectives) {
        deepest = std::max(deepest, alternationsIn(o.term, shared));
    }
    return deepest;
}

std::unordered_set<Feature, Feature::Hash> ConstraintModel::features() const {
    std::unordered_set<Feature, Feature::Hash> f;
    for (const auto& range : scalar_var_ranges) {
        if (range.sort.kind == SortKind::INT && range.count) { f.insert(feat::intVar()); }
    }
    for (const auto& d : decls) {
        if (d.sort.kind == SortKind::INT) {
            f.insert(feat::intVar());
        } else if (d.sort.kind == SortKind::REAL) {
            f.insert(feat::realVar());
        }
    }
    std::unordered_set<const Expr*> shared;
    const auto inspect = [&](const ExprPtr& expr) {
        if (isNonlinearOperation(expr)) { f.insert(feat::nonlinear()); }
        if (expr->kind == ExprKind::GLOBAL) { f.insert(feat::globalConstraint()); }
        if (expr->kind == ExprKind::FORALL || expr->kind == ExprKind::EXISTS) {
            f.insert(feat::quantifier());
        }
    };
    for (const auto& fn : funs) { visitDag(fn.body, shared, inspect); }
    for (const auto& c : constraints) {
        if (c.soft) { f.insert(feat::softConstraint()); }
        visitDag(c.formula, shared, inspect);
    }
    for (const auto& batch : packed_bool_clauses) {
        const std::size_t clauses=batch.source_lines.size();
        if (batch.weight_offsets.size()==clauses+1) {
            for (std::size_t i=0;i<clauses;++i) {
                if (batch.weight_offsets[i]<batch.weight_offsets[i+1]) {
                    f.insert(feat::softConstraint()); break;
                }
            }
        }
    }
    for (const auto& o : objectives) { visitDag(o.term, shared, inspect); }
    return f;
}

SetSolverRequirements ConstraintModel::setSolverRequirements() const {
    SetSolverRequirements out;
    constexpr std::size_t MAX_SORT_DEPTH = 128;
    constexpr std::size_t MAX_DATATYPE_INSTANCES = 4096;
    std::unordered_map<std::string, const DatatypeDecl*> datatype_by_name;
    for (const auto& dt : datatypes) datatype_by_name.emplace(dt.name, &dt);

    bool classification_limited = false;
    constexpr std::size_t MAX_INSPECTED_SORTS = 16384;

    // Build the same injective, kind-tagged key as before. The classification
    // budget remains conservative; even its bounded traversals use heap frames
    // rather than relying on a particular native stack size.
    const auto structuralKey = [&](const Sort& root, std::string& out_key) {
        struct Frame { const Sort* sort; std::size_t depth; std::size_t stage = 0; };
        std::vector<Frame> pending{{&root, 0}};
        while (!pending.empty()) {
            auto& frame = pending.back();
            const Sort& s = *frame.sort;
            if (frame.depth > MAX_SORT_DEPTH) return false;
            const auto depth = frame.depth + 1;
            const auto stage = frame.stage++;
            if (stage == 0) {
                out_key += "K" + std::to_string(static_cast<unsigned>(s.kind)) + ";";
                out_key += std::to_string(s.name.size()) + ":" + s.name;
                out_key += "W" + std::to_string(s.width) + ";E" + std::to_string(s.exponent_bits)
                    + ";S" + std::to_string(s.significand_bits) + ";";
                out_key += s.index ? "I1" : "I0";
                if (s.index) pending.push_back({s.index.get(), depth});
            } else if (stage == 1) {
                out_key += s.elem ? "M1" : "M0";
                if (s.elem) pending.push_back({s.elem.get(), depth});
            } else if (stage == 2) {
                out_key += "A" + std::to_string(s.args.size()) + ";";
            } else if (stage - 3 < s.args.size()) {
                const auto& arg = s.args[stage - 3];
                out_key += arg ? "1" : "0";
                if (arg) pending.push_back({arg.get(), depth});
            } else {
                pending.pop_back();
            }
        }
        return true;
    };

    // Parameters are lexical to a datatype declaration. Substituting a leaf
    // returns the actual argument as-is, without substituting inside it again.
    const auto substitute = [&](const Sort& root,
                                const std::unordered_map<std::string, Sort>& bindings) {
        struct Frame {
            const Sort* source;
            std::size_t depth;
            std::size_t next = 0;
            bool entered = false;
            Sort result{};
        };
        std::vector<Frame> pending{{&root, 0}};
        Sort result;
        while (!pending.empty()) {
            auto& frame = pending.back();
            const Sort& source = *frame.source;
            bool complete = false;
            if (!frame.entered) {
                frame.entered = true;
                if (frame.depth > MAX_SORT_DEPTH) {
                    classification_limited = true;
                    frame.result = Sort::uninterpreted("<depth-limit>");
                    complete = true;
                } else if (source.kind == SortKind::UNINTERPRETED && source.args.empty()
                           && bindings.count(source.name)) {
                    frame.result = bindings.at(source.name);
                    complete = true;
                } else {
                    frame.result = source;
                }
            }
            if (!complete && frame.next < source.args.size() + 2) {
                const auto slot = frame.next++;
                const Sort* child = slot == 0 ? source.index.get()
                                  : slot == 1 ? source.elem.get() : source.args[slot - 2].get();
                if (child) {
                    const auto depth = frame.depth + 1;
                    pending.push_back({child, depth});
                }
                continue;
            }
            result = std::move(frame.result);
            pending.pop_back();
            if (!pending.empty()) {
                auto& parent = pending.back();
                auto child = std::make_shared<const Sort>(std::move(result));
                const auto slot = parent.next - 1;
                if (slot == 0) parent.result.index = std::move(child);
                else if (slot == 1) parent.result.elem = std::move(child);
                else parent.result.args[slot - 2] = std::move(child);
            }
        }
        return result;
    };

    std::unordered_map<std::string, bool> finite_cache;
    std::unordered_set<std::string> active_instances;
    std::size_t classified_instances = 0;
    const auto finite = [&](const Sort& root) {
        struct Frame {
            Sort sort;
            std::size_t depth;
            bool entered = false;
            bool result = true;
            bool all_fields = false;
            std::size_t next = 0;
            std::string key{};
            std::vector<std::shared_ptr<const Sort>> children{};
        };
        std::vector<Frame> pending{{root, 0}};
        bool result = false;
        const auto finish = [&](bool value) {
            auto& frame = pending.back();
            if (!frame.key.empty()) {
                active_instances.erase(frame.key);
                finite_cache.emplace(frame.key, value);
            }
            pending.pop_back();
            if (pending.empty()) result = value;
            else pending.back().result &= value;
        };
        while (!pending.empty()) {
            auto& frame = pending.back();
            if (!frame.entered) {
                frame.entered = true;
                const Sort& s = frame.sort;
                if (frame.depth > MAX_SORT_DEPTH) {
                    classification_limited = true;
                    finish(false);
                    continue;
                }
                switch (s.kind) {
                case SortKind::BOOL: case SortKind::BITVEC: case SortKind::FLOAT:
                case SortKind::ROUNDING_MODE:
                    finish(true);
                    continue;
                case SortKind::TUPLE:
                    frame.children = s.args;
                    break;
                case SortKind::ARRAY:
                    if (!s.index || !s.elem) { finish(false); continue; }
                    frame.children = {s.index, s.elem};
                    break;
                case SortKind::SET:
                    if (!s.elem) { finish(false); continue; }
                    frame.children = {s.elem};
                    break;
                case SortKind::DATATYPE: {
                    const auto found = datatype_by_name.find(s.name);
                    if (found == datatype_by_name.end()) { finish(false); continue; }
                    const DatatypeDecl& dt = *found->second;
                    if (dt.coinductive || dt.constructors.empty() || s.args.size() != dt.params.size()) {
                        finish(false); continue;
                    }
                    std::string key{};
                    if (!structuralKey(s, key)) {
                        classification_limited = true;
                        finish(false); continue;
                    }
                    if (active_instances.count(key)) { finish(false); continue; }
                    const auto cached = finite_cache.find(key);
                    if (cached != finite_cache.end()) { finish(cached->second); continue; }
                    if (++classified_instances > MAX_DATATYPE_INSTANCES) {
                        classification_limited = true;
                        finish(false); continue;
                    }
                    std::unordered_map<std::string, Sort> bindings;
                    bool malformed = false;
                    for (std::size_t i = 0; i < dt.params.size(); ++i) {
                        if (!s.args[i]) { malformed = true; break; }
                        bindings.emplace(dt.params[i], *s.args[i]);
                    }
                    if (malformed) { finish(false); continue; }
                    active_instances.insert(key);
                    frame.key = std::move(key);
                    // All datatype fields are classified, even after one is
                    // infinite. This preserves cache and budget accounting.
                    frame.all_fields = true;
                    for (const auto& ctor : dt.constructors)
                        for (const auto& field : ctor.selectors)
                            frame.children.push_back(std::make_shared<const Sort>(substitute(field.sort, bindings)));
                    break;
                }
                default:
                    finish(false);
                    continue;
                }
            }
            if (frame.next < frame.children.size() && (frame.result || frame.all_fields)) {
                const auto child = frame.children[frame.next++];
                if (!child) { frame.result = false; continue; }
                const auto depth = frame.depth + 1;
                pending.push_back({*child, depth});
            } else {
                finish(frame.result);
            }
        }
        return result;
    };

    std::unordered_set<std::string> inspected_sorts;
    std::size_t inspected_datatype_instances = 0;
    const auto inspectSort = [&](const Sort& root) {
        struct Task { Sort sort; std::size_t depth; bool fields = false; };
        std::vector<Task> pending{{root, 0}};
        while (!pending.empty()) {
            auto task = std::move(pending.back());
            pending.pop_back();
            const Sort& s = task.sort;
            if (task.fields) {
                const auto it = datatype_by_name.find(s.name);
                if (it == datatype_by_name.end()) continue;
                const DatatypeDecl& dt = *it->second;
                if (s.args.size() != dt.params.size()) { classification_limited = true; continue; }
                std::unordered_map<std::string, Sort> bindings;
                bool malformed = false;
                for (std::size_t i = 0; i < dt.params.size(); ++i) {
                    if (!s.args[i]) { malformed = true; break; }
                    bindings.emplace(dt.params[i], *s.args[i]);
                }
                if (malformed) { classification_limited = true; continue; }
                for (auto ctor = dt.constructors.rbegin(); ctor != dt.constructors.rend(); ++ctor)
                    for (auto field = ctor->selectors.rbegin(); field != ctor->selectors.rend(); ++field)
                        pending.push_back({substitute(field->sort, bindings), task.depth + 1});
                continue;
            }
            if (task.depth > MAX_SORT_DEPTH) { classification_limited = true; continue; }
            std::string key{};
            if (!structuralKey(s, key)) { classification_limited = true; continue; }
            if (inspected_sorts.count(key)) continue;
            if (inspected_sorts.size() >= MAX_INSPECTED_SORTS) { classification_limited = true; continue; }
            inspected_sorts.insert(std::move(key));
            if (s.kind == SortKind::DATATYPE && ++inspected_datatype_instances > MAX_DATATYPE_INSTANCES) {
                classification_limited = true;
                continue;
            }
            if (s.kind == SortKind::SET) {
                out.has_sets = true;
                if (!s.elem || s.elem->kind != SortKind::INT) out.non_integer_carrier = true;
                if (!s.elem || !finite(*s.elem)) out.infinite_or_unknown_carrier = true;
            }
            // Keep the original preorder: index, element, type arguments, then
            // instantiated datatype fields. A revisit uses its structural key.
            if (s.kind == SortKind::DATATYPE) pending.push_back({s, task.depth, true});
            for (auto arg = s.args.rbegin(); arg != s.args.rend(); ++arg)
                if (*arg) pending.push_back({**arg, task.depth + 1});
            if (s.elem) pending.push_back({*s.elem, task.depth + 1});
            if (s.index) pending.push_back({*s.index, task.depth + 1});
        }
    };

    // Generic Set T fields establish the theory requirement before a concrete
    // datatype instance is reachable. Classify carriers only after substitution.
    const auto containsSet = [&](const Sort& root) {
        std::vector<std::pair<const Sort*, std::size_t>> pending{{&root, 0}};
        while (!pending.empty()) {
            const auto task = pending.back();
            pending.pop_back();
            if (task.second > MAX_SORT_DEPTH) { classification_limited = true; continue; }
            const Sort& s = *task.first;
            if (s.kind == SortKind::SET) return true;
            const auto depth = task.second + 1;
            for (auto arg = s.args.rbegin(); arg != s.args.rend(); ++arg)
                if (*arg) pending.emplace_back(arg->get(), depth);
            if (s.elem) pending.emplace_back(s.elem.get(), depth);
            if (s.index) pending.emplace_back(s.index.get(), depth);
        }
        return false;
    };
    for (const auto& dt : datatypes)
        for (const auto& ctor : dt.constructors)
            for (const auto& field : ctor.selectors)
                out.has_sets |= containsSet(field.sort);

    std::unordered_set<const Expr*> inspected_exprs;
    const auto inspectExpr = [&](const ExprPtr& root) {
        // Solver requirement discovery also visits ordinary SMT formulas with
        // no sets. Their expression depth must not consume native stack space.
        std::vector<const Expr*> pending{root.get()};
        while (!pending.empty()) {
            const auto* e = pending.back();
            pending.pop_back();
            if (!e || !inspected_exprs.insert(e).second) continue;
            out.has_quantifiers |= e->kind == ExprKind::FORALL || e->kind == ExprKind::EXISTS;
            inspectSort(e->sort);
            for (const auto& binder : e->binders) inspectSort(binder.sort);
            for (auto it = e->args.rbegin(); it != e->args.rend(); ++it) {
                pending.push_back(it->get());
            }
        }
    };
    for (const auto& d : decls) { inspectSort(d.sort); inspectExpr(d.lower_bound); inspectExpr(d.upper_bound); }
    for (const auto& fn : funs) {
        for (const auto& s : fn.params) { inspectSort(s); }
        inspectSort(fn.result);
        for (const auto& binder : fn.binders) { inspectSort(binder.sort); }
        inspectExpr(fn.body);
    }
    for (const auto& c : constraints) inspectExpr(c.formula);
    for (const auto& o : objectives) inspectExpr(o.term);
    if (classification_limited) {
        // The omitted suffix could contain a Set sort; preserve backend setup
        // conservatively as well as refusing a quantified carrier claim.
        out.has_sets = true;
        out.infinite_or_unknown_carrier = true;
        out.non_integer_carrier = true;
    }
    return out;
}


} // namespace SOMTParser::Uir::Hir
