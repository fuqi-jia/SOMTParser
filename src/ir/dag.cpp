/* -*- Source -*-
 *
 * The Directed Acyclic Graph (DAG) Class
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include <cctype>
#include <cstring>
#include "somtparser/ir/dag.h"
#include "somtparser/core/timing.h"
#include "somtparser/core/util.h"
#include "somtparser/ir/value.h"
#include <stack>
#include <optional>
#include <ostream>
#include <stdexcept>
#include <sstream>
#include <streambuf>
#include <unordered_set>

namespace SOMTParser{
    bool DAGNode::isEquivalentTo(const DAGNode& other) const {
        TIME_FUNC();
        using Pair = std::pair<const DAGNode*, const DAGNode*>;
        std::vector<Pair> pending{{this, &other}};
        std::unordered_set<Pair, PairNodePtrHash, PairNodePtrEqual> visited;
        while (!pending.empty()) {
            const auto [a, b] = pending.back();
            pending.pop_back();
            if (a == b) continue;
            if (!a || !b || a->kind == NODE_KIND::NT_QUANT_VAR || b->kind == NODE_KIND::NT_QUANT_VAR ||
                a->kind == NODE_KIND::NT_FUNC_PARAM || b->kind == NODE_KIND::NT_FUNC_PARAM ||
                a->kind == NODE_KIND::NT_FUNC_REC || b->kind == NODE_KIND::NT_FUNC_REC) return false;
            if (a->kind != b->kind || a->sort.get() != b->sort.get() ||
                a->name != b->name || a->children.size() != b->children.size())
                return false;
            if (a->children_hash && b->children_hash &&
                a->children_hash != b->children_hash) return false;
            if (!visited.emplace(a, b).second) continue;
            for (size_t i = a->children.size(); i > 0; --i)
                pending.emplace_back(a->children[i - 1].get(), b->children[i - 1].get());
        }
        return true;
    }

    namespace {
        struct DAGReleaseQueue {
            DAGNode* head = nullptr;
        };
        // The outer destructor owns the queue; nested destructors only append
        // their edges. Independent threads drain their own queues.
        thread_local DAGReleaseQueue* releasingNodes = nullptr;
    }

    DAGNode::~DAGNode() noexcept {
        if (children.empty()) return;
        DAGReleaseQueue local;
        const bool outer = releasingNodes == nullptr;
        if (outer) releasingNodes = &local;
        auto& queue = *releasingNodes;
        for (auto& child : children) {
            if (!child) continue;
            auto& link = child->reclamation;
            while (link.busy.test_and_set(std::memory_order_acquire)) {}
            if (link.owner) {
                // A queue already pins this node. Release the duplicate edge
                // under the lock, before that queue can remove its pin.
                child.reset();
            } else {
                link.owner = std::move(child);
                link.next = queue.head;
                queue.head = link.owner.get();
            }
            link.busy.clear(std::memory_order_release);
        }
        if (!outer) return;
        while (queue.head) {
            auto& link = queue.head->reclamation;
            while (link.busy.test_and_set(std::memory_order_acquire)) {}
            queue.head = link.next;
            link.next = nullptr;
            auto child = std::move(link.owner);
            link.busy.clear(std::memory_order_release);
            // Only a true final release enters the child's destructor. That
            // destructor enqueues its children and returns, so nesting stays
            // constant even with deep, shared, or branching DAGs. No allocation
            // or use_count snapshot is needed; weak_ptr::lock remains safe.
            child.reset();
        }
        releasingNodes = nullptr;
    }

    using AliasMap = std::unordered_map<DAGNode*, std::string>;
    struct AliasPlan;
    struct AliasEnv {
        const AliasEnv* parent = nullptr;
        const AliasMap* root_aliases = nullptr;
        const AliasPlan* plan = nullptr;
        // Local aliases are visible only when their dependency level is
        // strictly below this bound.
        std::size_t visible_levels = 0;
    };
    struct AliasPlan {
        std::vector<std::vector<std::pair<DAGNode*, std::string>>> groups;
        AliasMap aliases;
        std::unordered_map<DAGNode*, std::size_t> levels;
        std::vector<AliasEnv> views;
    };
    static const std::string* lookup_alias(const AliasEnv* env, DAGNode* node) {
        for (const AliasEnv* current = env; current; current = current->parent) {
            if (current->plan) {
                const auto level = current->plan->levels.find(node);
                if (level != current->plan->levels.end()
                    && level->second < current->visible_levels) {
                    const auto alias = current->plan->aliases.find(node);
                    if (alias != current->plan->aliases.end()) return &alias->second;
                }
            }
            if (current->root_aliases) {
                const auto alias = current->root_aliases->find(node);
                if (alias != current->root_aliases->end()) return &alias->second;
            }
        }
        return nullptr;
    }

    void DAGNode::updateFuncDef(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params, bool is_rec){
        condAssert(out_sort == sort, "updateFuncDef: out_sort != sort");
        (void)out_sort;
        children.clear();
        children.emplace_back(body);
        for(auto& p : params){
            children.emplace_back(p);
        }
        kind = is_rec ? NODE_KIND::NT_FUNC_REC : NODE_KIND::NT_FUNC_DEF;
        // The node now prints differently, so any ordering key taken from the
        // old printed form is stale.
        cached_print_hash = 0;
        cached_print_len = 0;
        print_hash_computed = false;
    }

    
    void DAGNode::updateApplyFunc(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params, bool is_rec){
        condAssert(out_sort == sort, "updateApplyFunc: out_sort != sort");
        (void)out_sort;
        children.clear();
        children.emplace_back(body);
        for(auto& p : params){
            children.emplace_back(p);
        }
        kind = is_rec ? NODE_KIND::NT_FUNC_REC_APPLY : NODE_KIND::NT_FUNC_APPLY;
        // As in updateFuncDef: the printed form changed, drop the stale key.
        cached_print_hash = 0;
        cached_print_len = 0;
        print_hash_computed = false;
    }

    // Helper: check if a string is in canonical rational a/b form
    static bool isRationalFormat(const std::string& name) {
        size_t slashPos = name.find('/');
        return slashPos != std::string::npos && slashPos > 0 && slashPos + 1 < name.size();
    }

    // Helper: emit SMT-LIB2 division syntax for a/b form
    static std::string formatRationalDivision(const std::string& name) {
        bool neg = (name[0] == '-');
        std::string absName = neg ? name.substr(1) : name;
        size_t sp = absName.find('/');
        std::string num = absName.substr(0, sp);
        std::string den = absName.substr(sp + 1);
        std::string result = "(/ " + num + " " + den + ")";
        if (neg) {
            return "(- " + result + ")";
        }
        return result;
    }

    /** A symbol as SMT-LIB can legally spell it.
     *
     *  SMT-LIB 2.6 §3.1 has two spellings: a SIMPLE symbol, whose characters
     *  are letters, digits and `~!@$%^&*_-+=<>.?/` and which may not start with
     *  a digit; and a QUOTED one, `|...|`, which may contain anything but `|`
     *  and `\`. The two denote the same symbol -- that identity is what PR #52
     *  established -- so choosing between them is a printing decision.
     *
     *  It was not being made. A name PARSED as `|x(1)|` came back quoted
     *  because the bars were kept, and a name a frontend BUILT through the API
     *  as `x(1)` was printed raw, producing `(declare-fun x(1) () Int)` -- which
     *  no solver reads, and which this library's own parser only survives by
     *  the lenient scan in getSymbol(). Column names like `x(1)` are ordinary
     *  in MPS and LP, so a valid input file produced an unusable script.
     *
     *  This is the "buildable but not readable" shape again: the API accepted
     *  the name, everything downstream agreed, and the artefact was wrong. */
    // Declared in dag.h; see there.
    std::string smtSymbolImpl(const std::string& name) {
        if (name.empty()) { return "||"; }
        if (name.front() == '|' && name.back() == '|' && name.size() >= 2) {
            return name;                       // already quoted; do not double it
        }
        auto simple = [](char c) {
            return std::isalnum(static_cast<unsigned char>(c)) != 0
                || std::strchr("~!@$%^&*_-+=<>.?/", c) != nullptr;
        };
        bool ok = std::isdigit(static_cast<unsigned char>(name.front())) == 0;
        for (const char c : name) {
            if (!simple(c)) { ok = false; break; }
        }
        return ok ? name : "|" + name + "|";
    }

    std::string dumpConst(const std::string& name, const std::shared_ptr<Sort>& sort){
        // Rational a/b form is only meaningful for ARITHMETIC sorts.  It must
        // never apply to other sorts: a string literal may legitimately
        // contain '/' (e.g. "/api/v1/"), and splitting it at the slash used
        // to emit (/ " api/v1/") — a malformed division — corrupting every
        // string-theory query whose literals contain a slash.
        if (sort && (sort->isReal() || sort->isInt() || sort->isIntOrReal())
            && isRationalFormat(name)) {
            return formatRationalDivision(name);
        }
        // A mathematical integer can still have exact sort Real. A bare
        // numeral loses that sort in polymorphic contexts such as `as const`
        // arrays: ((as const (Array Int Real)) 0) is rejected by Z3. Keep the
        // decimal marker on Real numerals, including zero and negative values.
        if (sort && sort->isReal() && !name.empty()) {
            const bool signedName = name.front() == '-' || name.front() == '+';
            const std::size_t first = signedName ? 1 : 0;
            if (first < name.size()
                && name.find_first_not_of("0123456789", first) == std::string::npos) {
                const std::string numeral = name.substr(first) + ".0";
                return name.front() == '-' ? "(- " + numeral + ")" : numeral;
            }
        }
        if(sort->isReal() || sort->isInt() || sort->isIntOrReal()){
            if(name[0] == '-'){
                return "(- " + name.substr(1) + ")";
            }
            else{
                return name;
            }
        }
        else if(sort->isBool()){
            return name;
        }
        else if(sort->isBv()){
            return name;
        }
        else if(sort->isFp()){
            // A bare decimal is a *Real* in SMT-LIB, never a Float, so dumping
            // `1.5` for a FloatingPoint constant produced a script this library
            // could not read back: (fp.lt f 1.5) came back "Type mismatch in
            // fp_lt". The round-trip property test never saw it because no
            // instance in the corpus has a floating-point constant.
            //
            // The conversion form is the spelling that carries the format.
            // Non-numeral names -- the special constants, and the bit-triple
            // handled by the caller -- are left alone.
            bool numeral = !name.empty();
            for(size_t i = (name[0] == '-' || name[0] == '+') ? 1 : 0;
                numeral && i < name.size(); ++i){
                if(!std::isdigit(static_cast<unsigned char>(name[i])) && name[i] != '.'){
                    numeral = false;
                }
            }
            if(numeral && name.find_first_of("0123456789") != std::string::npos){
                std::string inner = name;
                if(inner[0] == '-'){
                    inner = "(- " + inner.substr(1) + ")";
                }
                else if(inner[0] == '+'){
                    inner = inner.substr(1);
                }
                return "((_ to_fp " + std::to_string(sort->getExponentWidth()) + " "
                     + std::to_string(sort->getSignificandWidth()) + ") RNE "
                     + inner + ")";
            }
            return name;
        }
        else if(sort->isStr()){
            // A string constant's name carries its SMT-LIB literal text, quotes
            // included -- that is what the parser stores, and what makes a
            // parsed script dump back to itself. Constants built through
            // mkConstStr do not go through the parser and arrive unquoted, so
            // dumping them verbatim produced `(str.contains s ab)`, which this
            // library then rejected as an unknown symbol. Every producer is
            // fixed at once by normalising here.
            //
            // SMT-LIB escapes a quote by doubling it, so an unquoted name
            // containing one has to be escaped on the way in.
            if(name.size() >= 2 && name.front() == '"' && name.back() == '"'){
                return name;
            }
            std::string out = "\"";
            for(char c : name){
                if(c == '"') out += '"';
                out += c;
            }
            return out + "\"";
        }
        else if(sort->isArray()){
            return name;
        }
        return name;
    }

    // Evaluate a closed arithmetic subterm to an exact rational, or nullopt if it
    // is not a constant.  Used to fold ((_ to_fp eb sb) RM <const>) into an
    // (fp #b..) literal at dump time, so the dumped query stays in the pure FP
    // theory and strict backends without the Reals theory (e.g. Bitwuzla) accept
    // it.  Handles the constant forms the parser leaves unfolded: rational
    // literals (kept as NT_DIV_REAL "(/ a b)") and negations (NT_NEG "(- x)").
    static std::optional<Number> constToNumber(const std::shared_ptr<DAGNode>& n) {
        if (!n) return std::nullopt;
        using NK = NODE_KIND;
        // Per-call memoization also keeps a shared arithmetic DAG from being
        // expanded exponentially while preparing a single FP literal.
        std::unordered_map<const DAGNode*, std::optional<Number>> values;
        std::vector<std::pair<const DAGNode*, bool>> pending{{n.get(), false}};
        while (!pending.empty()) {
            const auto [node, ready] = pending.back();
            pending.pop_back();
            if (values.count(node)) continue;
            if (!node) { values.emplace(node, std::nullopt); continue; }
            if (node->isCInt() || node->isCReal()) {
                try { values.emplace(node, Number(node->getName(), false)); }
                catch (const std::bad_alloc&) { throw; }
                catch (...) { values.emplace(node, std::nullopt); }
                continue;
            }
            const auto kind = node->getKind();
            const auto size = node->getChildrenSize();
            const bool unary = (kind == NK::NT_NEG || kind == NK::NT_TO_REAL) && size == 1;
            const bool division = (kind == NK::NT_DIV_REAL || kind == NK::NT_DIV_INT) && size == 2;
            const bool fold = (kind == NK::NT_ADD || kind == NK::NT_SUB || kind == NK::NT_MUL) && size >= 1;
            if (!unary && !division && !fold) {
                values.emplace(node, std::nullopt);
                continue;
            }
            if (!ready) {
                pending.emplace_back(node, true);
                for (std::size_t i = size; i > 0; --i) {
                    const auto* child = node->getChild(i - 1).get();
                    if (!values.count(child)) pending.emplace_back(child, false);
                }
                continue;
            }
            auto value = values.at(node->getChild(0).get());
            if (value && (kind == NK::NT_NEG || (kind == NK::NT_SUB && size == 1))) {
                value = -*value;
            } else if (value && division) {
                const auto& divisor = values.at(node->getChild(1).get());
                if (!divisor || divisor->isZero()) {
                    value.reset(); // An underspecified zero division cannot be folded.
                } else if (kind == NK::NT_DIV_INT) {
                    const auto dividend_int = value->asIntegerExact();
                    const auto divisor_int = divisor->asIntegerExact();
                    if (dividend_int && divisor_int) {
                        value = Number(dividend_int->euclideanDiv(*divisor_int));
                    } else { value.reset(); }
                } else { value = *value / *divisor; }
            } else if (value && fold) {
                for (std::size_t i = 1; value && i < size; ++i) {
                    const auto& child = values.at(node->getChild(i).get());
                    if (!child) { value.reset(); break; }
                    if (kind == NK::NT_ADD) value = *value + *child;
                    else if (kind == NK::NT_SUB) value = *value - *child;
                    else value = *value * *child;
                }
            }
            values.emplace(node, std::move(value));
        }
        return values.at(n.get());
    }

    // High-performance iterative streaming version to avoid stack overflow
    // Hashes everything written to it without ever materialising the text, so
    // a node's printed form can be hashed in place of being built.
    //
    // The hash is polynomial/rolling rather than a plain accumulator because it
    // has to compose: H(A.B) = H(A)*BASE^|B| + H(B). That identity is what lets
    // an already-hashed subtree be folded in as a single unit (absorb), so no
    // node ever re-walks a subtree an ancestor already walked. Hashing every
    // operand of n nested commutative operators is then linear; re-printing
    // each ancestor's whole subtree instead would be quadratic.
    //
    // BASE must be odd to stay invertible modulo 2^64 (unsigned overflow is
    // well-defined wraparound), otherwise low bits would decay to zero.
    class PrintHashBuf : public std::streambuf {
    public:
        static const uint64_t BASE = 1099511628211ull;  // FNV-1a prime, odd

        uint64_t hash() const { return h_; }
        uint64_t length() const { return len_; }

        void absorb(uint64_t chunk_hash, uint64_t chunk_len) {
            h_ = h_ * ipow(BASE, chunk_len) + chunk_hash;
            len_ += chunk_len;
        }

    protected:
        std::streamsize xsputn(const char* s, std::streamsize n) override {
            for (std::streamsize i = 0; i < n; i++) {
                h_ = h_ * BASE + static_cast<unsigned char>(s[i]);
            }
            len_ += static_cast<uint64_t>(n);
            return n;
        }

        int_type overflow(int_type c) override {
            if (c != traits_type::eof()) {
                h_ = h_ * BASE + static_cast<unsigned char>(c);
                len_ += 1;
            }
            return c;
        }

    private:
        static uint64_t ipow(uint64_t base, uint64_t exp) {
            uint64_t r = 1;
            while (exp) {
                if (exp & 1) r *= base;
                base *= base;
                exp >>= 1;
            }
            return r;
        }

        uint64_t h_ = 0;
        uint64_t len_ = 0;
    };

    struct ContextualPrintHashes {
        const void* alias_context = nullptr;
        std::unordered_map<DAGNode*, std::pair<uint64_t, uint64_t>> values;
        void clear() { values.clear(); alias_context = nullptr; }
    };

    // Takes a raw pointer so that a node can print itself without owning a
    // shared_ptr to itself (see DAGNode::orderKey). Ownership is the caller's;
    // this only reads.
    //
    // `hb`, when set, must be the streambuf backing `out`: it switches on the
    // subtree folding described on PrintHashBuf. It is null for ordinary
    // printing, which always walks the whole term.
    void dumpSMTLIB2_streaming(DAGNode* root, std::ostream& out, PrintHashBuf* hb = nullptr,
                              const std::unordered_map<DAGNode*, std::string>* aliases = nullptr,
                              bool lexical_sharing = false,
                              const DAGNode* lexical_function = nullptr,
                              ContextualPrintHashes* contextual_hashes = nullptr,
                              bool sort_alias_renderings = false,
                              const AliasEnv* inherited_alias_context = nullptr,
                              const void* hash_alias_context = nullptr) {
        if (!root) return;

        DAGNode* actualRoot = root;

        // Static kind string cache for performance
        static std::unordered_map<NODE_KIND, const char*> kind_cache;
        static bool cache_initialized = false;

        if (!cache_initialized) {
            kind_cache[NODE_KIND::NT_NOT] = "not";
            kind_cache[NODE_KIND::NT_AND] = "and";
            kind_cache[NODE_KIND::NT_OR] = "or";
            kind_cache[NODE_KIND::NT_ADD] = "+";
            kind_cache[NODE_KIND::NT_MUL] = "*";
            kind_cache[NODE_KIND::NT_SUB] = "-";
            kind_cache[NODE_KIND::NT_EQ] = "=";
            kind_cache[NODE_KIND::NT_LE] = "<=";
            kind_cache[NODE_KIND::NT_LT] = "<";
            kind_cache[NODE_KIND::NT_GE] = ">=";
            kind_cache[NODE_KIND::NT_GT] = ">";
            kind_cache[NODE_KIND::NT_ITE] = "ite";
            kind_cache[NODE_KIND::NT_IMPLIES] = "=>";
            kind_cache[NODE_KIND::NT_XOR] = "xor";
            kind_cache[NODE_KIND::NT_DIV_REAL] = "/";
            kind_cache[NODE_KIND::NT_NEG] = "-";
            kind_cache[NODE_KIND::NT_DISTINCT] = "distinct";
            kind_cache[NODE_KIND::NT_SEP_PTO] = "pto";
            kind_cache[NODE_KIND::NT_SEP_STAR] = "sep";
            kind_cache[NODE_KIND::NT_SEP_WAND] = "wand";
            kind_cache[NODE_KIND::NT_FP_ADD] = "fp.add";
            kind_cache[NODE_KIND::NT_FP_SUB] = "fp.sub";
            kind_cache[NODE_KIND::NT_FP_MUL] = "fp.mul";
            kind_cache[NODE_KIND::NT_FP_DIV] = "fp.div";
            kind_cache[NODE_KIND::NT_FP_ABS] = "fp.abs";
            kind_cache[NODE_KIND::NT_FP_NEG] = "fp.neg";
            kind_cache[NODE_KIND::NT_FP_SQRT] = "fp.sqrt";
            kind_cache[NODE_KIND::NT_FP_LE] = "fp.leq";
            kind_cache[NODE_KIND::NT_FP_LT] = "fp.lt";
            kind_cache[NODE_KIND::NT_FP_GE] = "fp.geq";
            kind_cache[NODE_KIND::NT_FP_GT] = "fp.gt";
            kind_cache[NODE_KIND::NT_FP_EQ] = "fp.eq";
            kind_cache[NODE_KIND::NT_FP_TO_IEEE_BV] = "fp.to_ieee_bv";
            cache_initialized = true;
        }

        // Optimized iterative implementation using minimal WorkItem structure
        struct WorkItem {
            DAGNode* node;
            uint8_t action; // 0=process, 1=space, 2=close_paren, 3=close_paren_space, 4=text_output
            const AliasEnv* aliases;

            WorkItem(DAGNode* n, uint8_t a = 0,
                     const AliasEnv* active_aliases = nullptr)
                : node(n), action(a), aliases(active_aliases) {}
            
            // For text output
            std::string text;
            WorkItem(const std::string& t, uint8_t a = 4) : node(nullptr), action(a), aliases(nullptr), text(t) {}
        };

        // Pre-allocate stack with reasonable capacity to avoid frequent reallocations
        std::vector<WorkItem> work_stack;
        // Hashing a node whose children are cached needs only a small local
        // stack; reserving the full text-printer stack per leaf wastes memory.
        work_stack.reserve(hb ? 64 : 65536);
        const uint8_t scope_action = lexical_sharing && !hb ? 5 : 0;
        AliasEnv root_alias_env{inherited_alias_context, aliases, nullptr, 0};
        work_stack.emplace_back(actualRoot, scope_action, &root_alias_env);

        // Alias planning and collision detection follow the serializer's
        // term edges.
        // Function applications store their declaration/definition in child
        // zero for evaluation and expansion, but the printer emits only the
        // actual arguments. Function declaration/definition nodes are metadata
        // when reached from a term and are printed by their dedicated command
        // writers, not by this expression serializer. Walking these edges can
        // hoist a function body's parameter-dependent subterm into the caller's
        // scope and emit a free parameter in an otherwise valid expression.
        const auto printed_child_range = [](DAGNode* n) {
            const std::size_t count = n->getChildrenSize();
            switch (n->getKind()) {
            case NODE_KIND::NT_FUNC_APPLY:
            case NODE_KIND::NT_FUNC_REC_APPLY:
                return std::pair<std::size_t, std::size_t>{
                    std::min<std::size_t>(1, count), count};
            case NODE_KIND::NT_FUNC_DEC:
            case NODE_KIND::NT_FUNC_DEF:
            case NODE_KIND::NT_FUNC_REC:
            case NODE_KIND::NT_FUNC_PARAM:
                return std::pair<std::size_t, std::size_t>{count, count};
            default:
                return std::pair<std::size_t, std::size_t>{0, count};
            }
        };

        std::vector<std::unique_ptr<AliasPlan>> owned_alias_plans;
        std::unordered_set<std::string> taken_symbols;
        std::size_t alias_serial = 0;
        const auto remember_symbol = [&](const std::string& name) {
            taken_symbols.insert(name.size() >= 2 && name.front() == '|' && name.back() == '|'
                ? name.substr(1, name.size() - 2) : name);
        };
        if (lexical_sharing) {
            std::vector<DAGNode*> names_to_scan{actualRoot};
            std::unordered_set<DAGNode*> names_seen;
            while (!names_to_scan.empty()) {
                DAGNode* n = names_to_scan.back(); names_to_scan.pop_back();
                if (!n || !names_seen.insert(n).second) continue;
                remember_symbol(n->getName());
                // A call prints its name and arguments, never the helper's
                // body or formal parameters. Scanning that metadata repeats
                // entire definition closures at every caller and reserves
                // names which are not visible in this lexical term.
                const auto range = printed_child_range(n);
                for (std::size_t i = range.first; i < range.second; ++i)
                    names_to_scan.push_back(n->getChild(i).get());
            }
            if (lexical_function) {
                remember_symbol(lexical_function->getName());
                for (std::size_t i = 1; i < lexical_function->getChildrenSize(); ++i)
                    remember_symbol(lexical_function->getChild(i)->getName());
            }
        }

        const auto is_scope_binder = [](DAGNode* n) {
            switch (n->getKind()) {
            case NODE_KIND::NT_FORALL: case NODE_KIND::NT_EXISTS:
            case NODE_KIND::NT_LET: case NODE_KIND::NT_LET_CHAIN:
            case NODE_KIND::NT_DT_MATCH:
            case NODE_KIND::NT_ATTRIBUTE: case NODE_KIND::NT_PATTERN:
            case NODE_KIND::NT_NO_PATTERN: case NODE_KIND::NT_WEIGHT:
            case NODE_KIND::NT_QID: case NODE_KIND::NT_LET_BIND_VAR:
            case NODE_KIND::NT_LET_BIND_VAR_LIST:
                return true;
            default: return false;
            }
        };
        const auto is_function_metadata = [](DAGNode* n) {
            switch (n->getKind()) {
            case NODE_KIND::NT_FUNC_DEC:
            case NODE_KIND::NT_FUNC_DEF:
            case NODE_KIND::NT_FUNC_REC:
            case NODE_KIND::NT_FUNC_PARAM:
                return true;
            default:
                return false;
            }
        };
        const auto is_commutative = [](NODE_KIND kind) {
            switch (kind) {
            case NODE_KIND::NT_ADD: case NODE_KIND::NT_MUL:
            case NODE_KIND::NT_AND: case NODE_KIND::NT_IAND:
            case NODE_KIND::NT_OR: case NODE_KIND::NT_XOR:
            case NODE_KIND::NT_BV_ADD: case NODE_KIND::NT_BV_MUL:
            case NODE_KIND::NT_BV_AND: case NODE_KIND::NT_BV_OR:
            case NODE_KIND::NT_BV_XOR: case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_DISTINCT: case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN: case NODE_KIND::NT_BV_NAND:
            case NODE_KIND::NT_BV_NOR: case NODE_KIND::NT_BV_XNOR:
            case NODE_KIND::NT_BV_COMP: case NODE_KIND::NT_BV_UADDO:
            case NODE_KIND::NT_BV_SADDO: case NODE_KIND::NT_BV_UMULO:
            case NODE_KIND::NT_BV_SMULO: case NODE_KIND::NT_FP_EQ:
            case NODE_KIND::NT_FP_MIN: case NODE_KIND::NT_FP_MAX:
                return true;
            default:
                return false;
            }
        };
        ContextualPrintHashes local_contextual_hashes;
        const void* local_context_env = nullptr;
        // The parser orders commutative children by the hash of their printed
        // form (DAGNode::orderKey). In shared output, that form includes aliases
        // at every descendant, with descendant commutative nodes already
        // canonicalized. Compute these hashes bottom-up and memoize by node in
        // the current alias environment: child hashes are absorbed by the
        // iterative printer, avoiding expanded strings and repeated DAG walks.
        const auto build_context_hash = [&](DAGNode* hash_root, const AliasEnv* env,
                                            ContextualPrintHashes& cache) {
            std::vector<std::pair<DAGNode*, bool>> pending{{hash_root, false}};
            std::unordered_set<DAGNode*> seen;
            while (!pending.empty()) {
                const auto item = pending.back();
                pending.pop_back();
                DAGNode* current = item.first;
                if (!current) continue;
                if (!item.second) {
                    if (const std::string* alias = lookup_alias(env, current)) {
                        uint64_t hash = 0;
                        for (unsigned char byte : *alias)
                            hash = hash * PrintHashBuf::BASE + byte;
                        cache.values[current] = {hash, static_cast<uint64_t>(alias->size())};
                        continue;
                    }
                    if (cache.values.count(current) || !seen.insert(current).second) continue;
                    if (is_scope_binder(current)) {
                        current->orderKey();
                        cache.values.emplace(current,
                            std::make_pair(current->printHash(), current->printLength()));
                        continue;
                    }
                    pending.emplace_back(current, true);
                    const auto range = printed_child_range(current);
                    for (std::size_t i = range.second; i > range.first; --i) {
                        DAGNode* child = current->getChild(i - 1).get();
                        if (child && !lookup_alias(env, child) && !cache.values.count(child))
                            pending.emplace_back(child, false);
                    }
                    continue;
                }
                PrintHashBuf hashbuf;
                std::ostream hashout(&hashbuf);
                dumpSMTLIB2_streaming(current, hashout, &hashbuf, nullptr, false,
                                      nullptr, &cache, true, env, env);
                cache.values[current] = {hashbuf.hash(), hashbuf.length()};
            }
        };
        const auto shared_ordered_children = [&](DAGNode* n, const AliasEnv* env) {
            std::vector<DAGNode*> children;
            const auto& source = n->getChildren();
            children.reserve(source.size());
            for (const auto& child : source) children.push_back(child.get());
            if ((!lexical_sharing && !sort_alias_renderings)
                || !is_commutative(n->getKind()) || children.size() < 2)
                return children;

            const void* cache_context = hash_alias_context
                ? hash_alias_context : static_cast<const void*>(env);
            ContextualPrintHashes* cache = contextual_hashes;
            if (cache) {
                // A nested hash printer may be invoked under a different alias
                // view while sharing the caller's memo table. Keep entries only
                // within that immutable alias context.
                if (cache->alias_context != cache_context) {
                    cache->values.clear();
                    cache->alias_context = cache_context;
                }
            } else {
                if (local_context_env != cache_context) {
                    local_contextual_hashes.clear();
                    local_contextual_hashes.alias_context = cache_context;
                    local_context_env = cache_context;
                }
                cache = &local_contextual_hashes;
            }
            std::vector<std::pair<DAGNode*, std::size_t>> keyed;
            keyed.reserve(children.size());
            for (DAGNode* child : children) {
                build_context_hash(child, env, *cache);
                const auto hash = cache->values.find(child);
                keyed.emplace_back(child, hash == cache->values.end()
                    ? child->orderKey()
                    : static_cast<std::size_t>(hash->second.first));
            }
            std::stable_sort(keyed.begin(), keyed.end(), [](const auto& a, const auto& b) {
                return a.second < b.second;
            });
            for (std::size_t i = 0; i < keyed.size(); ++i) children[i] = keyed[i].first;
            return children;
        };
        const auto make_alias_plan = [&](DAGNode* scope_root, const AliasEnv* base) {
            auto plan = std::make_unique<AliasPlan>();
            std::unordered_map<DAGNode*, unsigned char> state;
            std::unordered_map<DAGNode*, std::size_t> references;
            std::vector<DAGNode*> postorder;
            std::vector<std::pair<DAGNode*, bool>> pending{{scope_root, false}};
            references[scope_root] = 1;
            while (!pending.empty()) {
                const auto entry = pending.back(); pending.pop_back();
                DAGNode* n = entry.first;
                if (!n || lookup_alias(base, n)) continue;
                if (entry.second) {
                    state[n] = 2;
                    postorder.push_back(n);
                    continue;
                }
                const auto found = state.find(n);
                if (found != state.end()) {
                    if (found->second == 1) return plan;
                    continue;
                }
                state[n] = 1;
                pending.emplace_back(n, true);
                if (!is_scope_binder(n)) {
                    const auto range = printed_child_range(n);
                    for (std::size_t i = range.second; i > range.first; --i) {
                        DAGNode* child = n->getChild(i - 1).get();
                        if (!child || lookup_alias(base, child)) continue;
                        ++references[child];
                        if (state.find(child) == state.end())
                            pending.emplace_back(child, false);
                    }
                }
            }
            std::unordered_map<DAGNode*, std::size_t> costs;
            std::unordered_map<DAGNode*, int> levels;
            constexpr std::size_t cap = 1024ULL * 1024ULL * 1024ULL;
            std::vector<std::pair<DAGNode*, std::string>> selected;
            for (DAGNode* n : postorder) {
                int child_level = -1;
                std::size_t cost = std::min(cap, n->getName().size() + 4);
                if (!is_scope_binder(n)) {
                    const auto range = printed_child_range(n);
                    for (std::size_t i = range.first; i < range.second; ++i) {
                        DAGNode* child = n->getChild(i).get();
                        if (!child || lookup_alias(base, child)) continue;
                        const auto ci = costs.find(child);
                        const auto li = levels.find(child);
                        if (ci != costs.end()) cost = std::min(cap, cost + ci->second + 1);
                        if (li != levels.end()) child_level = std::max(child_level, li->second);
                    }
                }
                levels[n] = child_level;
                costs[n] = cost;
                if (references[n] < 2 || n->getChildrenSize() == 0
                    || is_function_metadata(n)
                    || n->getKind() == NODE_KIND::NT_ATTRIBUTE
                    || n->getKind() == NODE_KIND::NT_PATTERN
                    || n->getKind() == NODE_KIND::NT_NO_PATTERN
                    || n->getKind() == NODE_KIND::NT_WEIGHT
                    || n->getKind() == NODE_KIND::NT_QID
                    || n->getKind() == NODE_KIND::NT_LET_BIND_VAR
                    || n->getKind() == NODE_KIND::NT_LET_BIND_VAR_LIST
                    || n->getKind() == NODE_KIND::NT_DT_MATCH) continue;
                std::string name;
                do { name = "__somt_dag_" + std::to_string(alias_serial++); }
                while (taken_symbols.count(name));
                if (static_cast<long double>(references[n] - 1) * cost
                    <= static_cast<long double>(references[n] + 1) * name.size() + 8) continue;
                taken_symbols.insert(name);
                selected.emplace_back(n, name);
                costs[n] = name.size();
                levels[n] = child_level + 1;
            }
            if (selected.empty()) return plan;
            int max_level = 0;
            for (const auto& s : selected) max_level = std::max(max_level, levels[s.first]);
            plan->groups.resize(static_cast<std::size_t>(max_level + 1));
            for (auto& s : selected) {
                const std::size_t level = static_cast<std::size_t>(levels[s.first]);
                plan->levels.emplace(s.first, level);
                plan->aliases.emplace(s.first, s.second);
                plan->groups[level].push_back(std::move(s));
            }
            plan->views.resize(plan->groups.size() + 1);
            for (std::size_t i = 0; i < plan->views.size(); ++i) {
                plan->views[i] = AliasEnv{base, nullptr, plan.get(), i};
            }
            return plan;
        };
        const auto push_text = [&](const std::string& text) {
            work_stack.emplace_back(text, 4);
        };
        const auto schedule_scope = [&](DAGNode* scope_root, const AliasEnv* base) {
            auto plan = make_alias_plan(scope_root, base);
            if (plan->groups.empty()) {
                work_stack.emplace_back(scope_root, 0, base);
                return;
            }
            AliasPlan* active_plan = plan.get();
            owned_alias_plans.push_back(std::move(plan));
            for (std::size_t i = 0; i < active_plan->groups.size(); ++i) {
                work_stack.emplace_back(nullptr, 2);
            }
            work_stack.emplace_back(scope_root, 0, &active_plan->views.back());
            for (std::size_t gi = active_plan->groups.size(); gi-- > 0;) {
                const auto& group = active_plan->groups[gi];
                work_stack.emplace_back(") ", 4);
                for (std::size_t bi = group.size(); bi-- > 0;) {
                    work_stack.emplace_back(")", 4);
                    work_stack.emplace_back(group[bi].first, 0, &active_plan->views[gi]);
                    work_stack.emplace_back(" ", 4);
                    work_stack.emplace_back(group[bi].second, 4);
                    work_stack.emplace_back("(", 4);
                    if (bi) work_stack.emplace_back(" ", 4);
                }
                work_stack.emplace_back("(let (", 4);
            }
        };

        while (!work_stack.empty()) {
            // Once the sink fails, stop walking the remaining DAG. The public
            // streaming wrapper below turns this into a diagnostic exception.
            if (!out) return;
            WorkItem item = work_stack.back();
            work_stack.pop_back();

            if (item.action == 1) { // Write space
                out << " ";
                continue;
            }
            if (item.action == 2) { // Write closing paren
                out << ")";
                continue;
            }
            if (item.action == 3) { // Write ") " for special cases
                out << ") ";
                continue;
            }
            if (item.action == 4) { // Write text
                out << item.text;
                continue;
            }
            if (item.action == 5) { // Start a lexical scope with local aliases
                schedule_scope(item.node, item.aliases);
                continue;
            }
            

            // Process node (action == 0)
            DAGNode* node = item.node;
            if (!node) continue;

            // Local let references are a printing choice only. orderKey()
            // continues hashing the expanded canonical term without aliases.
            const auto* active_aliases = item.aliases ? item.aliases : &root_alias_env;
            if (const auto* alias = lookup_alias(active_aliases, node)) {
                out << *alias;
                continue;
            }

            if (hb && contextual_hashes) {
                const auto contextual = contextual_hashes->values.find(node);
                if (contextual != contextual_hashes->values.end()) {
                    hb->absorb(contextual->second.first, contextual->second.second);
                    continue;
                }
            }

            // Every node -- root and child alike -- reaches the printer through
            // this one point, so folding in an already-hashed subtree here
            // covers all of them.
            if (hb && !contextual_hashes && node->hasPrintHash()) {
                hb->absorb(node->printHash(), node->printLength());
                continue;
            }

            auto kind = node->getKind();
            switch (kind) {
            case NODE_KIND::NT_SEP_EMP:
                out << "sep.emp";
                break;
            case NODE_KIND::NT_SEP_NIL:
                out << "(as sep.nil " << node->getSort()->toString() << ")";
                break;
            case NODE_KIND::NT_CONST_TRUE:
                out << "true";
                break;
            case NODE_KIND::NT_CONST_FALSE:
                out << "false";
                break;
            case NODE_KIND::NT_CONST:
                if (node->getName() == "(fp_bit_representation)" && node->getChildrenSize() == 3) {
                    auto sign = node->getChild(0).get();
                    auto exp = node->getChild(1).get();
                    auto mant = node->getChild(2).get();
                    out << "(fp ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(mant, 0, active_aliases);     // mant
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(exp, 0, active_aliases);      // exp
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(sign, 0, active_aliases);     // sign
                } else {
                    out << dumpConst(node->getName(), node->getSort());
                }
                break;
            // set.empty and set.universe carry their sort in the term, not in
            // the operator, so printing the bare name loses it and the dumped
            // script does not re-parse -- the same failure the floating-point
            // and string constants had.
            case NODE_KIND::NT_SET_EMPTY:
            case NODE_KIND::NT_SET_UNIVERSE:
                out << "(as " << node->getName() << " "
                    << node->getSort()->toString() << ")";
                break;
            case NODE_KIND::NT_VAR:
            case NODE_KIND::NT_TEMP_VAR:
            case NODE_KIND::NT_PLACEHOLDER_VAR:
                out << smtSymbolImpl(node->getName());
                break;
            case NODE_KIND::NT_CONST_ARRAY: {
                out << "((as const ";
                out << node->getSort()->toString();
                out << ") ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(node->getChild(0).get(), 0, active_aliases);   // child0
                break;
            }

            // Binary operations - optimized for common case
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_LE:
            case NODE_KIND::NT_LT:
            case NODE_KIND::NT_GE:
            case NODE_KIND::NT_GT:
            case NODE_KIND::NT_ADD:
            case NODE_KIND::NT_MUL:
            case NODE_KIND::NT_SUB:
            case NODE_KIND::NT_DIV_REAL: {
                if (node->getChildrenSize() == 2) {
                    const auto children = shared_ordered_children(node, active_aliases);
                    auto child0 = children[0];
                    auto child1 = children[1];

                    const char* op = kind_cache[kind];
                    out << "(" << op << " ";

                    // Push in reverse order: close_paren, child1, space, child0
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(child1, 0, active_aliases);   // child1
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(child0, 0, active_aliases);   // child0
                    break;
                }
                // Fall through to n-ary case
                [[fallthrough]];
            }
            // N-ary operations - most common case, highly optimized
            case NODE_KIND::NT_AND:
            case NODE_KIND::NT_OR:
            case NODE_KIND::NT_SEP_PTO:
            case NODE_KIND::NT_SEP_STAR:
            case NODE_KIND::NT_SEP_WAND:
            case NODE_KIND::NT_DISTINCT: {
                const std::string op = kind_cache[kind] ? kind_cache[kind] : kindToString(kind);

                out << "(" << op;
                const auto children = shared_ordered_children(node, active_aliases);

                // Push closing paren first
                work_stack.emplace_back(nullptr, 2);

                // Push children in reverse order, each preceded by a space
                for (int i = static_cast<int>(children.size()) - 1; i >= 0; i--) {
                    auto child = children[static_cast<std::size_t>(i)];
                    work_stack.emplace_back(child, 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1); // space before child
                }
                break;
            }

            case NODE_KIND::NT_REG_LOOP: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "((_ re.loop ";

                // Push: ), child0, ") ", child2, " ", child1
                work_stack.emplace_back(nullptr, 2);     // )
                work_stack.emplace_back(child0, 0, active_aliases);      // child0
                work_stack.emplace_back(nullptr, 3);     // ") " - special case
                work_stack.emplace_back(child2, 0, active_aliases);      // child2
                work_stack.emplace_back(nullptr, 1);     // space
                work_stack.emplace_back(child1, 0, active_aliases);      // child1
                break;
            }
            // Unary operations
            case NODE_KIND::NT_NOT:
            case NODE_KIND::NT_NEG: {
                auto child = node->getChild(0).get();
                const char* op = kind_cache[kind];

                out << "(" << op << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child, 0, active_aliases);    // child
                break;
            }

            // Ternary operations
            case NODE_KIND::NT_ITE: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "(ite ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child2, 0, active_aliases);   // child2
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child1, 0, active_aliases);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0, active_aliases);   // child0
                break;
            }

            // Special processing operations
            case NODE_KIND::NT_BV_EXTRACT: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "((_ extract ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child0, 0, active_aliases);   // child0
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(child2, 0, active_aliases);   // child2
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child1, 0, active_aliases);   // child1
                break;
            }
            case NODE_KIND::NT_BV_REPEAT:
            case NODE_KIND::NT_BV_ZERO_EXT:
            case NODE_KIND::NT_BV_SIGN_EXT:
            case NODE_KIND::NT_BV_ROTATE_LEFT:
            case NODE_KIND::NT_BV_ROTATE_RIGHT:
            // int2bv/nat2bv are indexed too — without these two they fell to
            // the generic path and printed as (int2bv x 8) instead of
            // ((_ int2bv 8) x).  Ported from the SMTStabilizer fork.
            case NODE_KIND::NT_INT_TO_BV:
            case NODE_KIND::NT_NAT_TO_BV:
            // divisible is indexed for the same reason and was missing for the
            // same reason: it printed as (divisible x 3), which is not the
            // operator SMT-LIB defines and which this parser would read back as
            // a two-argument application.
            case NODE_KIND::NT_IS_DIVISIBLE: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();

                out << "((_ " << kindToString(kind) << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child0, 0, active_aliases);   // child0
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(child1, 0, active_aliases);   // child1
                break;
            }

            // Constants
            case NODE_KIND::NT_CONST_PI:
                out << "pi";
                break;
            case NODE_KIND::NT_CONST_E:
                out << "e";
                break;
            case NODE_KIND::NT_INFINITY:
                // If node has a name (e.g., "(_ +oo eb sb)"), use it; otherwise use default
                if (!node->getName().empty() && node->getName()[0] == '(') {
                    out << node->getName();
                } else {
                    out << "inf";
                }
                break;
            case NODE_KIND::NT_POS_INFINITY:
                // If node has a name (e.g., "(_ +oo eb sb)"), use it; otherwise use default
                if (!node->getName().empty() && node->getName()[0] == '(') {
                    out << node->getName();
                } else {
                    out << "+inf";
                }
                break;
            case NODE_KIND::NT_NEG_INFINITY:
                // If node has a name (e.g., "(_ -oo eb sb)"), use it; otherwise use default
                if (!node->getName().empty() && node->getName()[0] == '(') {
                    out << node->getName();
                } else {
                    out << "-inf";
                }
                break;
            case NODE_KIND::NT_NAN:
                // If node has a name (e.g., "(_ NaN eb sb)"), use it; otherwise use default
                if (!node->getName().empty() && node->getName()[0] == '(') {
                    out << node->getName();
                } else {
                    out << "NaN";
                }
                break;
            case NODE_KIND::NT_EPSILON:
                out << "epsilon";
                break;
            case NODE_KIND::NT_POS_EPSILON:
                out << "+epsilon";
                break;
            case NODE_KIND::NT_NEG_EPSILON:
                out << "-epsilon";
                break;
            case NODE_KIND::NT_REG_NONE:
                out << "re.none";
                break;
            case NODE_KIND::NT_REG_ALL:
                out << "re.all";
                break;
            case NODE_KIND::NT_REG_ALLCHAR:
                out << "re.allchar";
                break;

            // Quantifiers - handle inline for performance
            case NODE_KIND::NT_FORALL:
            case NODE_KIND::NT_EXISTS: {
                out << "(" << kindToString(kind) << " (";
                for (size_t i = 1; i < node->getChildrenSize(); i++) {
                    auto current_child = node->getChild(i).get();
                    if (i == 1){
                        out << "(" << smtSymbolImpl(current_child->getName()) << " " << current_child->getSort()->toString() << ")";
                    }
                    else{
                        out << " (" << smtSymbolImpl(current_child->getName()) << " " << current_child->getSort()->toString() << ")";
                    }
                }
                out << ") ";
                work_stack.emplace_back(nullptr, 2);  // )
                // Binder names may reuse the same hash-consed variable node
                // as an outer same-name/same-sort binder. Do not expose the
                // outer scope's aliases below this lexical boundary; build a
                // fresh local plan instead.
                work_stack.emplace_back(node->getChild(0).get(), scope_action, nullptr);  // scoped body
                break;
            }

            case NODE_KIND::NT_QUANT_VAR:
                // Binders and their uses must have the same legal spelling.
                // QCIR permits numeric names, which SMT-LIB requires quoted.
                out << smtSymbolImpl(node->getName());
                break;

            // Function related
            case NODE_KIND::NT_FUNC_DEC:
            case NODE_KIND::NT_FUNC_DEF:
            case NODE_KIND::NT_FUNC_REC:
            case NODE_KIND::NT_FUNC_PARAM:
                out << smtSymbolImpl(node->getName());
                break;

            // Function applications
            case NODE_KIND::NT_FUNC_APPLY: {
                // For NT_FUNC_APPLY, children[0] is function, children[1..] are parameters
                // If no parameters (size <= 1), output just the name without parentheses
                if (node->getChildrenSize() <= 1) {
                    out << smtSymbolImpl(node->getName());
                } else {
                    out << "(" << smtSymbolImpl(node->getName());
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = node->getChildrenSize() - 1; i >= 1; i--) {
                        auto current_child = node->getChild(i).get();
                        work_stack.emplace_back(current_child, 0, active_aliases);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }

            case NODE_KIND::NT_LET: {
                condAssert(node->getChildrenSize() > 0, "NT_LET should have at least one child");
                
                // Output: (let ((var1 value1) (var2 value2) ...) body)
                // Stack order (reverse): ) + body + ") " + bindings + "(let ("
                
                work_stack.emplace_back(")", 4);  // final )
                // A let body is under the new bindings; inherited DAG aliases
                // could refer to an outer same-name variable. Binding values
                // below remain in the enclosing scope.
                work_stack.emplace_back(node->getChild(0).get(), scope_action, nullptr);  // scoped body
                work_stack.emplace_back(") ", 4);  // close binding list and add space
                
                // Process bindings in reverse order for stack
                for(int i = node->getChildrenSize() - 1; i >= 1; i--){
                    work_stack.emplace_back(")", 4);  // ) for this binding
                    work_stack.emplace_back(node->getChild(i)->getChild(0).get(), scope_action, active_aliases);  // scoped binding value
                    work_stack.emplace_back(" ", 4);  // space before value
                    work_stack.emplace_back(node->getChild(i)->getPureName(), 4);  // variable name
                    work_stack.emplace_back("(", 4);  // ( for this binding
                    if (i > 1) {
                        work_stack.emplace_back(" ", 4);  // space between bindings
                    }
                }
                
                work_stack.emplace_back("(let (", 4);  // opening
                break;
            }
            case NODE_KIND::NT_LET_CHAIN: {
                // For let-chain: (let ((var1 val1)) (let ((var2 val2)) body))
                // This creates nested let expressions
                
                size_t num_bindings = node->getChildrenSize() - 1;
                
                // Add closing parentheses for all let expressions (in reverse order)
                for(size_t i = 0; i < num_bindings; i++){
                    work_stack.emplace_back(")", 4);  // ) for each let
                }
                
                // Add body
                // Later let-chain values can see earlier bindings, and the
                // final body sees the whole chain. Start an independent alias
                // environment at both positions to avoid capturing shadowed
                // nodes from the enclosing scope.
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 1).get(), scope_action, nullptr);
                
                // Process let bindings in reverse order
                for(int i = num_bindings - 1; i >= 0; i--){
                    condAssert(node->getChild(i)->isLetBindVarList(), "NT_LET_CHAIN: child is not LET_BIND_VAR_LIST");
                    auto var_list = node->getChild(i);
                    
                    work_stack.emplace_back(") ", 4);  // close binding list and add space
                    
                    // Process variables in this binding list (reverse order)
                    for(int j = var_list->getChildrenSize() - 1; j >= 0; j--){
                        work_stack.emplace_back(")", 4);  // ) for binding
                        work_stack.emplace_back(var_list->getChild(j)->getChild(0).get(), scope_action, nullptr);  // scoped binding value
                        work_stack.emplace_back(" ", 4);  // space before value
                        work_stack.emplace_back(var_list->getChild(j)->getPureName(), 4);  // variable name
                        work_stack.emplace_back("(", 4);  // ( for binding
                        if(j > 0) {
                            work_stack.emplace_back(" ", 4);  // space between bindings
                        }
                    }
                    
                    work_stack.emplace_back("(let (", 4);  // let opening
                }
                
                break;
            }
            case NODE_KIND::NT_LET_BIND_VAR: {
                out << node->getPureName();
                break;
            }
            case NODE_KIND::NT_LET_BIND_VAR_LIST: {
                // Output: ( (var1 value1) (var2 value2) ... )
                // Stack order (reverse): ) + bindings + "( "
                
                work_stack.emplace_back(")", 4);  // final )
                
                // Process bindings in reverse order for stack
                for(int i = node->getChildrenSize() - 1; i >= 1; i--){
                    work_stack.emplace_back(")", 4);  // ) for this binding
                    work_stack.emplace_back(node->getChild(i)->getChild(0).get(), scope_action, active_aliases);  // scoped binding value
                    work_stack.emplace_back(" ", 4);  // space before value
                    work_stack.emplace_back(node->getChild(i)->getPureName(), 4);  // variable name
                    work_stack.emplace_back("(", 4);  // ( for this binding
                    if (i > 1) {
                        work_stack.emplace_back(" ", 4);  // space between bindings
                    }
                }
                
                work_stack.emplace_back("( ", 4);  // opening "( "
                break;
            }

            case NODE_KIND::NT_UF_APPLY: {
                // For UF applications, all children are parameters (no function definition in children)
                // If no parameters (size == 0), output just the name without parentheses
                const auto& children = node->getChildren();
                if (children.empty()) {
                    out << smtSymbolImpl(node->getName());
                } else {
                    out << "(" << smtSymbolImpl(node->getName());
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 0; i--) {  // Start from 0
                        auto current_child = children[i].get();
                        work_stack.emplace_back(current_child, 0, active_aliases);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }

            // Datatype operations
            case NODE_KIND::NT_DT_CONSTRUCTOR: {
                // Constructor application: (CtorName arg1 arg2 ...) or just CtorName
                const auto& children = node->getChildren();
                if (children.empty()) {
                    // A NULLARY constructor of a PARAMETRIC datatype must keep
                    // its sort ascription. `nil` names a constructor of every
                    // instance of `L` at once, and having no arguments there is
                    // nothing to infer the instance from -- which is why SMT-LIB
                    // requires `(as nil (L Int))`. Printing the bare name gave a
                    // term this parser had built at a definite sort and could
                    // not read back at any.
                    std::shared_ptr<Sort> s = node->getSort();
                    if (s && s->isDatatype() && s->getChildrenSize() > 0) {
                        out << "(as " << node->getName() << " " << s->toString()
                            << ")";
                    } else {
                        out << node->getName();
                    }
                } else {
                    out << "(" << node->getName();
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 0; i--) {
                        work_stack.emplace_back(children[i].get(), 0, active_aliases);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }
            case NODE_KIND::NT_DT_SELECTOR: {
                // Selector application: (sel-name arg)
                const auto& children = node->getChildren();
                if (children.empty()) {
                    out << node->getName();
                } else {
                    out << "(" << node->getName();
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 0; i--) {
                        work_stack.emplace_back(children[i].get(), 0, active_aliases);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }
            case NODE_KIND::NT_DT_TESTER: {
                // Tester application.  SMT-LIB 2.6 spells this ((_ is C) arg);
                // we used to emit the legacy (is-C arg) form, which standard
                // solvers reject.  The node name is stored as "is-C", so strip
                // the prefix here.  Ported from the SMTStabilizer fork.
                const std::string& tester = node->getName();
                const std::string ctor = (tester.rfind("is-", 0) == 0) ? tester.substr(3) : tester;
                const auto& children = node->getChildren();
                if (children.empty()) {
                    out << "(_ is " << ctor << ")";
                } else {
                    out << "((_ is " << ctor << ")";
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 0; i--) {
                        work_stack.emplace_back(children[i].get(), 0, active_aliases);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }
            case NODE_KIND::NT_DT_UPDATER: {
                // ((_ update <selector>) t v) — ported from the SMTStabilizer fork.
                const auto& children = node->getChildren();
                out << "((_ update " << node->getName() << ")";
                work_stack.emplace_back(nullptr, 2);  // )
                for (int i = children.size() - 1; i >= 0; i--) {
                    work_stack.emplace_back(children[i].get(), 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }
            // TERM ANNOTATIONS: (! <term> :pattern (...) :qid q ...).
            // Ported from the SMTStabilizer fork: these used to be parsed and
            // then dropped, so quantifier triggers silently vanished from the
            // printed output.
            case NODE_KIND::NT_ATTRIBUTE: {
                const auto& children = node->getChildren();
                out << "(!";
                work_stack.emplace_back(nullptr, 2);  // )
                for (int i = children.size() - 1; i >= 0; i--) {
                    if (i == 0) {
                        work_stack.emplace_back(children[i].get(), scope_action, active_aliases);
                    } else {
                        work_stack.emplace_back(children[i].get(), 0, nullptr);
                    }
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }
            case NODE_KIND::NT_PATTERN: {
                const auto& children = node->getChildren();
                out << ":pattern (";
                work_stack.emplace_back(nullptr, 2);  // )
                for (int i = children.size() - 1; i >= 0; i--) {
                    work_stack.emplace_back(children[i].get(), 0, nullptr);
                    if (i) work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }
            case NODE_KIND::NT_NO_PATTERN: {
                out << ":no-pattern ";
                if (node->getChildrenSize() > 0) {
                    work_stack.emplace_back(node->getChild(0).get(), 0, nullptr);
                }
                break;
            }
            case NODE_KIND::NT_WEIGHT: {
                out << ":weight ";
                if (node->getChildrenSize() > 0) {
                    work_stack.emplace_back(node->getChild(0).get(), 0, nullptr);
                }
                break;
            }
            case NODE_KIND::NT_QID:
                out << ":qid " << node->getName();
                break;
            // TUPLE OPERATORS — ported from the SMTStabilizer fork.
            case NODE_KIND::NT_TUPLE_UNIT:
                out << "tuple.unit";
                break;
            case NODE_KIND::NT_TUPLE_CONSTRUCTOR: {
                const auto& children = node->getChildren();
                out << "(tuple";
                work_stack.emplace_back(nullptr, 2);  // )
                for (int i = children.size() - 1; i >= 0; i--) {
                    work_stack.emplace_back(children[i].get(), 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }
            case NODE_KIND::NT_TUPLE_SELECT:
            case NODE_KIND::NT_TUPLE_UPDATE:
            case NODE_KIND::NT_TUPLE_PROJECT: {
                // ((_ tuple.select i) t), ((_ tuple.update i) t v),
                // ((_ tuple.project i ...) t).  The index children are stored
                // after the tuple term, so emit them into the index list first.
                const auto& children = node->getChildren();
                const size_t nidx = (kind == NODE_KIND::NT_TUPLE_UPDATE) ? 1
                                  : (kind == NODE_KIND::NT_TUPLE_SELECT) ? 1
                                  : (children.size() >= 1 ? children.size() - 1 : 0);
                out << "((_ " << kindToString(kind);
                work_stack.emplace_back(nullptr, 2);  // )
                // terms: tuple (child 0), then the value for tuple.update
                if (kind == NODE_KIND::NT_TUPLE_UPDATE && children.size() >= 3) {
                    work_stack.emplace_back(children[2].get(), 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                if (!children.empty()) {
                    work_stack.emplace_back(children[0].get(), 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                work_stack.emplace_back(")", 4);
                for (size_t i = nidx; i >= 1; i--) {
                    work_stack.emplace_back(children[i].get(), 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }
            case NODE_KIND::NT_DT_MATCH: {
                // SMT-LIB: (match <scrutinee> ( (<pattern> <body>) ... ))
                out << "(match";
                const auto& children = node->getChildren();
                if (children.empty()) {
                    out << ")";
                    break;
                }
                const size_t n = children.size();
                work_stack.emplace_back(nullptr, 2);  // close outer (match ...)

                if (n >= 2) {
                    work_stack.emplace_back(nullptr, 2);  // close case-list )
                    const size_t pairs = (n - 1) / 2;
                    for (int ci = static_cast<int>(pairs) - 1; ci >= 0; --ci) {
                        const size_t pi = 1u + static_cast<size_t>(ci) * 2u;
                        const size_t bi = pi + 1;
                        if (bi >= n) {
                            break;
                        }
                        work_stack.emplace_back(nullptr, 2);  // close (pat body)
                        // Each case body is a fresh lexical scope containing its
                        // pattern variables. Pattern syntax itself is metadata,
                        // never an aliasable term.
                        work_stack.emplace_back(children[bi].get(), scope_action, nullptr);
                        work_stack.emplace_back(nullptr, 1);
                        work_stack.emplace_back(children[pi].get(), 0, nullptr);
                        work_stack.emplace_back("(", 4);
                        if (ci > 0) {
                            work_stack.emplace_back(nullptr, 1);  // space between cases
                        }
                    }
                    work_stack.emplace_back("(", 4);  // open case-list (
                } else {
                    // n == 1: only scrutinee — (match s ())
                    work_stack.emplace_back(nullptr, 2);  // close empty case-list
                    work_stack.emplace_back("(", 4);
                }

                work_stack.emplace_back(nullptr, 1);
                // The scrutinee is an ordinary term in the enclosing scope.
                // Give it the same lexical sharing plan as any other scope
                // root; case bodies still get fresh plans under their pattern
                // binders above.
                work_stack.emplace_back(children[0].get(), scope_action, active_aliases);
                work_stack.emplace_back(nullptr, 1);
                break;
            }
            
            case NODE_KIND::NT_FUNC_REC_APPLY: {
                // For recursive function applications, children[0] is the function definition, children[1..] are parameters
                // Only output the parameters, not the function definition
                // If no parameters (size <= 1), output just the name without parentheses
                const auto& children = node->getChildren();
                if (children.size() <= 1) {
                    out << smtSymbolImpl(node->getName());
                } else {
                    out << "(" << smtSymbolImpl(node->getName());
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 1; i--) {  // Start from 1, not 0
                        auto current_child = children[i].get();
                        work_stack.emplace_back(current_child, 0, active_aliases);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }

            // FLOATING POINT OPERATIONS
            case NODE_KIND::NT_FP_ADD:
            case NODE_KIND::NT_FP_SUB:
            case NODE_KIND::NT_FP_MUL:
            case NODE_KIND::NT_FP_DIV:
            case NODE_KIND::NT_FP_FMA:
            case NODE_KIND::NT_FP_MIN:
            case NODE_KIND::NT_FP_MAX: {
                std::string kind_str = kindToString(kind);
                out << "(" << kind_str;
                work_stack.emplace_back(nullptr, 2);  // )
                const auto& children = node->getChildren();
                for (int i = children.size() - 1; i >= 0; i--) {
                    auto current_child = children[i].get();
                    work_stack.emplace_back(current_child, 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }

            case NODE_KIND::NT_FP_SQRT:
            case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL: {
                // fp.sqrt and fp.roundToIntegral require rounding mode and input: (fp.sqrt <rm> <arg>)
                std::string kind_str = kindToString(kind);
                out << "(" << kind_str;
                work_stack.emplace_back(nullptr, 2);  // )
                const auto& children = node->getChildren();
                for (int i = children.size() - 1; i >= 0; i--) {
                    auto current_child = children[i].get();
                    work_stack.emplace_back(current_child, 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }

            case NODE_KIND::NT_FP_ABS:
            case NODE_KIND::NT_FP_NEG:
            case NODE_KIND::NT_FP_IS_NORMAL:
            case NODE_KIND::NT_FP_IS_SUBNORMAL:
            case NODE_KIND::NT_FP_IS_ZERO:
            case NODE_KIND::NT_FP_IS_INF:
            case NODE_KIND::NT_FP_IS_NAN:
            case NODE_KIND::NT_FP_IS_NEG:
            case NODE_KIND::NT_FP_IS_POS:
            case NODE_KIND::NT_FP_TO_REAL: {
                std::string kind_str = kindToString(kind);
                auto child = node->getChild(0).get();
                out << "(" << kind_str << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child, 0, active_aliases);    // child
                break;
            }

            case NODE_KIND::NT_FP_REM: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                out << "(fp.rem ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child1, 0, active_aliases);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0, active_aliases);   // child0
                break;
            }

            case NODE_KIND::NT_FP_LE:
            case NODE_KIND::NT_FP_LT:
            case NODE_KIND::NT_FP_GE:
            case NODE_KIND::NT_FP_GT:
            case NODE_KIND::NT_FP_EQ: {
                std::string kind_str = kindToString(kind);
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                out << "(" << kind_str << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child1, 0, active_aliases);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0, active_aliases);   // child0
                break;
            }

            case NODE_KIND::NT_FP_TO_UBV:
            case NODE_KIND::NT_FP_TO_SBV: {
                // Format: ((_ fp.to_ubv size) rm fp) or ((_ fp.to_sbv size) rm fp)
                std::string kind_str = kindToString(kind);
                auto rm = node->getChild(0).get();
                auto fp = node->getChild(1).get();
                auto size = node->getChild(2).get();
                out << "((_ " << kind_str << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(fp, 0, active_aliases);       // fp
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(rm, 0, active_aliases);       // rm
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(size, 0, active_aliases);     // size
                break;
            }

            case NODE_KIND::NT_FP_TO_FP: {
                auto eb = node->getChild(0).get();
                auto sb = node->getChild(1).get();
                
                if(node->getChildrenSize() == 4) {
                    // Constant folding for output: ((_ to_fp eb sb) RM <const>) is
                    // rounded to a concrete value and emitted as an (fp #b..)
                    // literal, keeping the dumped term in the pure FP theory so
                    // strict backends without the Reals theory (e.g. Bitwuzla)
                    // accept it.  realToFpValue rounds the exact rational in one
                    // correct step, so the literal matches native to_fp (no
                    // change for lenient backends such as z3/cvc5).
                    {
                        auto fpsort = node->getSort();
                        // A symbolic rounding mode is part of the formula. The helper's
                        // default RNE is not a valid replacement for that variable.
                        if (fpsort && fpsort->isFp() && node->getChild(2)->isCRoundingMode()) {
                            auto num = constToNumber(node->getChild(3));
                            if (num) {
                                mpfr_rnd_t rnd = FloatingPointUtils::getFPRoundingModeMpfr(node->getChild(2));
                                auto fv = FloatingPointUtils::realToFpValue(
                                    *num, fpsort->getExponentWidth(), fpsort->getSignificandWidth(), rnd);
                                if (fv) { out << fv->toSMTFP(); break; }
                            }
                        }
                    }
                    // 4-parameter version: ((_ to_fp eb sb) rm param)
                    auto rm = node->getChild(2).get();
                    auto param = node->getChild(3).get();
                    out << "((_ to_fp ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(param, 0, active_aliases);    // param
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(rm, 0, active_aliases);       // rm
                    work_stack.emplace_back(nullptr, 3);  // ") "
                    work_stack.emplace_back(sb, 0, active_aliases);       // sb
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(eb, 0, active_aliases);       // eb
                } else if(node->getChildrenSize() == 3) {
                    // 3-parameter version: ((_ to_fp eb sb) param)
                    auto param = node->getChild(2).get();
                    out << "((_ to_fp ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(param, 0, active_aliases);    // param
                    work_stack.emplace_back(nullptr, 3);  // ") "
                    work_stack.emplace_back(sb, 0, active_aliases);       // sb
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(eb, 0, active_aliases);       // eb
                } else {
                    // Invalid number of children
                    out << "INVALID_FP_TO_FP_NODE";
                }
                break;
            }

            case NODE_KIND::NT_FP_TO_FP_UNSIGNED: {
                auto eb = node->getChild(0).get();
                auto sb = node->getChild(1).get();
                auto rm = node->getChild(2).get();
                auto param = node->getChild(3).get();
                out << "((_ to_fp_unsigned ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(param, 0, active_aliases);    // param
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(rm, 0, active_aliases);       // rm
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(sb, 0, active_aliases);       // sb
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(eb, 0, active_aliases);       // eb
                break;
            }

            case NODE_KIND::NT_FP_TO_IEEE_BV: {
                auto param = node->getChild(0).get();
                size_t nbits = node->getSort()->getBitWidth();
                out << "((_ fp.to_ieee_bv " << nbits << ") ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(param, 0, active_aliases);    // param
                break;
            }

            case NODE_KIND::NT_ROOT_OBJ: {
                auto expr = node->getChild(0).get();
                auto index = node->getChild(1).get();
                out << "(root-obj ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(index, 0, active_aliases);    // index
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(expr, 0, active_aliases);     // expr
                break;
            }

            case NODE_KIND::NT_ROOT_OF_WITH_INTERVAL: {
                out << "(root-of-with-interval (coeffs ";
                
                // Stack order (LIFO - Last In First Out):
                // We want output: (root-of-with-interval (coeffs c1 c2 ...) lower upper)
                // So we push in reverse order:
                
                // 1. Push closing parenthesis for root-of-with-interval (will be printed last)
                work_stack.emplace_back(nullptr, 2);  // )
                
                // 2. Push upper bound
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 1).get(), 0, active_aliases);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 3. Push lower bound
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 2).get(), 0, active_aliases);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 4. Push closing parenthesis for coeffs list
                work_stack.emplace_back(nullptr, 2);  // )
                
                // 5. Push coefficients in reverse order (so they print in correct order)
                for(int i = node->getChildrenSize() - 3; i >= 0; i--) {
                    work_stack.emplace_back(node->getChild(i).get(), 0, active_aliases);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                
                break;
            }

            case NODE_KIND::NT_REAL_ALGEBRAIC_NUMBER: {
                // Format: (_ real_algebraic_number <polynomial>, (lower_bound, upper_bound)>)
                out << "(_ real_algebraic_number <";
                
                // Stack order (LIFO - Last In First Out):
                // We want output: (_ real_algebraic_number <polynomial>, (lower_bound, upper_bound)>)
                // So we push in reverse order:
                
                // 1. Push closing '>' for angle brackets
                work_stack.emplace_back(">", 4);  // '>'
                
                // 2. Push closing parenthesis for interval
                work_stack.emplace_back(nullptr, 2);  // )
                
                // 3. Push upper bound
                work_stack.emplace_back(node->getChild(2).get(), 0, active_aliases);
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(",", 4);  // ','
                
                // 4. Push lower bound
                work_stack.emplace_back(node->getChild(1).get(), 0, active_aliases);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 5. Push opening parenthesis for interval
                work_stack.emplace_back("(", 4);  // '('
                
                // 6. Push comma and space
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(",", 4);  // ','
                
                // 7. Push polynomial
                work_stack.emplace_back(node->getChild(0).get(), 0, active_aliases);
                
                break;
            }

            // Array operations
            case NODE_KIND::NT_SELECT: {
                // select(array, index) -> (select array index)
                auto array = node->getChild(0).get();
                auto index = node->getChild(1).get();
                out << "(select ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(index, 0, active_aliases);    // index
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(array, 0, active_aliases);    // array
                break;
            }

            case NODE_KIND::NT_STORE: {
                // store(array, index, value) -> (store array index value)
                // Note: The array should already be normalized as a store-chain
                auto array = node->getChild(0).get();
                auto index = node->getChild(1).get();
                auto value = node->getChild(2).get();
                out << "(store ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(value, 0, active_aliases);    // value
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(index, 0, active_aliases);    // index
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(array, 0, active_aliases);    // array
                break;
            }

            default: {
                // Fallback for other cases - iterative version
                std::string kind_str = kindToString(kind);
                const auto children = shared_ordered_children(node, active_aliases);

                if (children.empty()) {
                    out << kind_str;
                } else if (children.size() == 1) {
                    auto child = children[0];
                    out << "(" << kind_str << " ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(child, 0, active_aliases);    // child
                } else {
                    out << "(" << kind_str;
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = static_cast<int>(children.size()) - 1; i >= 0; i--) {
                        auto child = children[static_cast<std::size_t>(i)];
                        work_stack.emplace_back(child, 0, active_aliases);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }
            }
        }
    }

    void dumpSMTLIB2(const std::shared_ptr<DAGNode>& root, std::ostream& out) {
        dumpSMTLIB2_streaming(root.get(), out);  // ordinary output walks the full term
        if (!out) {
            throw std::runtime_error("dumpSMTLIB2: failed while writing SMT-LIB expression");
        }
    }

    // Compatibility wrapper. Checking the intermediate stream is essential:
    // std::ostringstream can enter badbit after an allocation/write failure,
    // and str() would otherwise return a syntactically incomplete prefix.
    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& root) {
        std::ostringstream oss;
        dumpSMTLIB2(root, oss);
        return oss.str();
    }

    std::size_t DAGNode::orderKey() const {
        if(print_hash_computed) {
            return static_cast<std::size_t>(cached_print_hash);
        }
        // Populate children first even if nobody has requested their order
        // keys yet. Merely reusing *existing* caches expands a shared chain
        // exponentially on its first comparison (for example a nested max
        // used as an equality operand). The rolling hash composes the exact
        // same canonical bytes while visiting each DAG node only once.
        std::vector<std::pair<DAGNode*, bool>> pending{
            {const_cast<DAGNode*>(this), false}};
        while (!pending.empty()) {
            const auto item = pending.back();
            pending.pop_back();
            DAGNode* node = item.first;
            if (!node || node->print_hash_computed) { continue; }
            if (!item.second) {
                pending.emplace_back(node, true);
                const auto& children = node->getChildren();
                for (auto it = children.rbegin(); it != children.rend(); ++it) {
                    if (*it && !(*it)->print_hash_computed) {
                        pending.emplace_back(it->get(), false);
                    }
                }
                continue;
            }
            PrintHashBuf buf;
            std::ostream os(&buf);
            dumpSMTLIB2_streaming(node, os, &buf);
            node->cached_print_hash = buf.hash();
            node->cached_print_len = buf.length();
            node->print_hash_computed = true;
        }
        return static_cast<std::size_t>(cached_print_hash);
    }

    
    void dumpSMTLIB2Shared(const std::shared_ptr<DAGNode>& node, std::ostream& out) {
        dumpSMTLIB2_streaming(node.get(), out, nullptr, nullptr, true);
        if (!out) {
            throw std::runtime_error("dumpSMTLIB2Shared: failed while writing SMT-LIB expression");
        }
    }

    void dumpFuncDef(const std::shared_ptr<DAGNode>& node, std::ostream& out){
        out << "(define-fun " << smtSymbolImpl(node->getName()) << " (";
        // For NT_FUNC_DEF, children[0] is body, children[1..n] are parameters
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i!=1) out << " ";
            out << "(" << smtSymbolImpl(node->getChild(i)->getName()) << " "
                << node->getChild(i)->getSort()->toString() << ")";
        }
        // Use node's declared sort, not body's inferred sort (which may be widened to IntOrReal)
        out << ") " << node->getSort()->toString() << " ";
        dumpSMTLIB2_streaming(node->getChild(0).get(), out, nullptr, nullptr, true, node.get());
        out << ")";
        if (!out) throw std::runtime_error("dumpFuncDef: failed while writing SMT-LIB function");
    }
    std::string dumpFuncDef(const std::shared_ptr<DAGNode>& node){
        std::ostringstream out;
        dumpFuncDef(node, out);
        return out.str();
    }

    void dumpFuncRec(const std::shared_ptr<DAGNode>& node, std::ostream& out){
        out << "(define-fun-rec " << smtSymbolImpl(node->getName()) << " (";
        // For NT_FUNC_REC, children[0] is body, children[1..n] are parameters
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i!=1) out << " ";
            out << "(" << smtSymbolImpl(node->getChild(i)->getName()) << " "
                << node->getChild(i)->getSort()->toString() << ")";
        }
        // Use node's declared sort, not body's inferred sort (which may be widened to IntOrReal)
        out << ") " << node->getSort()->toString() << " ";
        dumpSMTLIB2_streaming(node->getChild(0).get(), out, nullptr, nullptr, true, node.get());
        out << ")";
        if (!out) throw std::runtime_error("dumpFuncRec: failed while writing SMT-LIB function");
    }
    std::string dumpFuncRec(const std::shared_ptr<DAGNode>& node){
        std::ostringstream out;
        dumpFuncRec(node, out);
        return out.str();
    }
    // (define-funs-rec ((f (params) sort) ...) (body ...))
    //
    // A mutually recursive group has to be emitted as one command: its members
    // call each other, so a sequence of define-fun-rec commands would refer to
    // a function that the script has not defined yet.  SMT-LIB puts all the
    // signatures first precisely so every body can see every name.
    void dumpFuncsRec(const std::vector<std::shared_ptr<DAGNode>>& nodes, std::ostream& out){
        condAssert(!nodes.empty(), "dumpFuncsRec: empty group");
        out << "(define-funs-rec (";
        for(size_t n = 0; n < nodes.size(); n++){
            const auto& node = nodes[n];
            condAssert(node != nullptr, "dumpFuncsRec: null member");
            if(n != 0) out << " ";
            out << "(" << smtSymbolImpl(node->getName()) << " (";
            // children[0] is the body, children[1..n] are the parameters.
            for(size_t i = 1; i < node->getChildrenSize(); i++){
                if(i != 1) out << " ";
                out << "(" << smtSymbolImpl(node->getChild(i)->getName()) << " "
                    << node->getChild(i)->getSort()->toString() << ")";
            }
            out << ") " << node->getSort()->toString() << ")";
        }
        out << ") (";
        for(size_t n = 0; n < nodes.size(); n++){
            if(n != 0) out << " ";
            dumpSMTLIB2(nodes[n]->getChild(0), out);
        }
        out << "))";
        if (!out) throw std::runtime_error("dumpFuncsRec: failed while writing SMT-LIB functions");
    }

    std::string dumpFuncsRec(const std::vector<std::shared_ptr<DAGNode>>& nodes){
        std::ostringstream out;
        dumpFuncsRec(nodes, out);
        return out.str();
    }

    void dumpFuncDec(const std::shared_ptr<DAGNode>& node, std::ostream& out){
        out << "(declare-fun " << smtSymbolImpl(node->getName()) << " (";
        // For NT_FUNC_DEC, children[0] is NULL_NODE, children[1..n] are parameter type nodes
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i!=1) out << " ";
            out << node->getChild(i)->getSort()->toString();
        }
        // The return type is stored in the node's sort, not in children[0]
        out << ") " << node->getSort()->toString() << ")";
        if (!out) throw std::runtime_error("dumpFuncDec: failed while writing SMT-LIB declaration");
    }
    std::string dumpFuncDec(const std::shared_ptr<DAGNode>& node){
        std::ostringstream out;
        dumpFuncDec(node, out);
        return out.str();
    }

    // NodeManager
    
    // Static constant nodes are now defined inline in the header file

    NodeManager::NodeManager() {
        // 1. Reserve before inserting anything
        nodes.reserve(65536);
        for (size_t i = 0; i < NUM_KINDS; i++) {
            NODE_KIND kind = static_cast<NODE_KIND>(i);
            if (static_kinds.count(kind) > 0) {
                node_buckets[i].reserve(1);
            }
            else{
                node_buckets[i].reserve(8192);
            }
        }
        // 2. Initialize static constant nodes and insert them into buckets
        initializeStaticNodes();
    }

    NodeManager::~NodeManager(){
        clear();
    }

    std::shared_ptr<DAGNode> NodeManager::getNode(const size_t index) const{
        return nodes[index];
    }
    size_t NodeManager::getIndex(const std::shared_ptr<DAGNode>& node) const{
        auto bucket_index = static_cast<size_t>(node->getKind());
        auto& kind_bucket = node_buckets[bucket_index];
        size_t node_hash = node->hashCode();
        
        auto hash_it = kind_bucket.find(node_hash);
        if(hash_it != kind_bucket.end()) {
            for(const auto& pair : hash_it->second) {
                if(pair.first.get() == node.get() ||
                pair.first->isEquivalentTo(*node)) {
                    return pair.second;
                }
            }
        }
        return -1;
    }
    size_t NodeManager::size() const{
        return nodes.size();
    }

    void NodeManager::clear() {
        // Unlink non-static nodes so that (a) destruction never recurses deeply
        // through long child chains and (b) recursive-function definitions
        // (which form reference cycles) cannot leak. Nodes that are still
        // referenced from outside the manager (API users, language bindings)
        // are preserved together with their whole subtree, so external holders
        // never observe a cleared node.
        //
        // Internal owners of every managed node are exactly:
        //   1 x nodes vector + 1 x bucket entry + one per parent child-link.
        std::unordered_map<const DAGNode*, size_t> internal_refs;
        internal_refs.reserve(nodes.size());
        for (size_t i = static_node_count; i < nodes.size(); i++) {
            internal_refs[nodes[i].get()] += 2; // nodes vector + bucket entry
        }
        // Borrow child vectors during this read-only traversal. Copying them
        // allocates storage proportional to fanout while we are freeing a DAG.
        for (size_t i = static_node_count; i < nodes.size(); i++) {
            for (const auto& child : nodes[i]->children) {
                auto it = internal_refs.find(child.get());
                if (it != internal_refs.end()) it->second += 1;
            }
        }

        // Roots referenced from outside; keep their whole subtrees intact.
        // Mark before enqueueing so a wide node with repeated child links
        // needs work-list space only for distinct nodes, not every edge.
        std::unordered_set<const DAGNode*> keep;
        std::vector<const DAGNode*> stack;
        for (size_t i = static_node_count; i < nodes.size(); i++) {
            const size_t uc = static_cast<size_t>(nodes[i].use_count());
            auto it = internal_refs.find(nodes[i].get());
            if (it != internal_refs.end() && uc > it->second
                && keep.insert(nodes[i].get()).second) {
                stack.push_back(nodes[i].get());
            }
        }
        while (!stack.empty()) {
            const DAGNode* n = stack.back();
            stack.pop_back();
            for (const auto& child : n->children) {
                if (keep.insert(child.get()).second) {
                    stack.push_back(child.get());
                }
            }
        }

        for (size_t i = static_node_count; i < nodes.size(); i++) {
            if (keep.find(nodes[i].get()) == keep.end()) {
                nodes[i]->clear();
            }
        }
        nodes.clear();

        // Clear hash buckets and re-insert static nodes
        for (auto& bucket : node_buckets) {
            bucket.clear();
        }
        nodes.clear();
    }
    
    std::shared_ptr<DAGNode> NodeManager::insertNodeToBucket(const std::shared_ptr<DAGNode>& node) {
        TIME_FUNC();
        auto bucket_index = static_cast<size_t>(node->getKind());
        auto& kind_bucket = node_buckets[bucket_index];
        
        // pre-calculate hash code to avoid repeated calculation
        size_t node_hash = node->hashCode();
        
        // secondary hash lookup: first use hash code to locate the small bucket
        auto hash_it = kind_bucket.find(node_hash);
        if(hash_it != kind_bucket.end()) {
            TIME_BLOCK("NodeManager::insertNodeToBucket: hash_it != kind_bucket.end()");
            // linear search in the small bucket
            for(const auto& pair : hash_it->second) {
                // optimize comparison order: the most likely different ones are in front, to avoid the expensive isEquivalentTo
                if(pair.first.get() == node.get()) {
                    // completely the same pointer, return directly
                    auto node_ptr = nodes[pair.second];
                    node_ptr->incUseCount();
                    return node_ptr;
                }
                // fast structure comparison (avoid the expensive isEquivalentTo call)
                if(pair.first->getKind() == node->getKind() &&
                pair.first->getChildrenSize() == node->getChildrenSize() &&
                pair.first->getName() == node->getName()) {
                    // only call the expensive isEquivalentTo when the structure matches completely
                    if(pair.first->isEquivalentTo(*node)) {
                        auto node_ptr = nodes[pair.second];
                        node_ptr->incUseCount();
                        return node_ptr;
                    }
                }
            }
        }
        
        // node does not exist, insert new node
        size_t new_index = nodes.size();
        kind_bucket[node_hash].emplace_back(node, new_index);
        nodes.emplace_back(node);
        node->incUseCount();
        return node;
    }

    void NodeManager::initializeStaticNodes() {
        // Basic constants
        insertNodeToBucket(NULL_NODE);
        insertNodeToBucket(UNKNOWN_NODE);
        insertNodeToBucket(ERROR_NODE);
        insertNodeToBucket(TRUE_NODE);
        insertNodeToBucket(FALSE_NODE);
        insertNodeToBucket(E_NODE);
        insertNodeToBucket(PI_NODE);
        insertNodeToBucket(NAN_NODE);
        insertNodeToBucket(EPSILON_NODE);
        insertNodeToBucket(POS_EPSILON_NODE);
        insertNodeToBucket(NEG_EPSILON_NODE);
        
        // Infinity nodes
        insertNodeToBucket(STR_INF_NODE);
        insertNodeToBucket(STR_POS_INF_NODE);
        insertNodeToBucket(STR_NEG_INF_NODE);
        insertNodeToBucket(INT_INF_NODE);
        insertNodeToBucket(INT_POS_INF_NODE);
        insertNodeToBucket(INT_NEG_INF_NODE);
        insertNodeToBucket(REAL_INF_NODE);
        insertNodeToBucket(REAL_POS_INF_NODE);
        insertNodeToBucket(REAL_NEG_INF_NODE);
        
        // Mark how many nodes are static constants so we can preserve them during clear()
        static_node_count = nodes.size();
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name, std::vector<std::shared_ptr<DAGNode>> children) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, kind, name, children);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, kind, name);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, NODE_KIND kind) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, kind);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode() {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>();
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(NODE_KIND kind, std::string name) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(kind, name);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(NODE_KIND kind) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(kind);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const Integer& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const Real& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const double& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const int& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const bool& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(const std::string& n) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(n);
        return insertNodeToBucket(node);
    }

}

namespace SOMTParser {
std::string smtSymbol(const std::string& name) { return smtSymbolImpl(name); }
}
