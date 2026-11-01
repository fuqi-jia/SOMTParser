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

#include "somtparser/ir/dag.h"
#include "somtparser/core/timing.h"
#include "somtparser/core/util.h"
#include "somtparser/ir/value.h"
#include <stack>
#include <optional>
#include <ostream>
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
            if (!a->children_hash.empty() && !b->children_hash.empty() &&
                a->children_hash != b->children_hash) return false;
            if (!visited.emplace(a, b).second) continue;
            for (size_t i = a->children.size(); i > 0; --i)
                pending.emplace_back(a->children[i - 1].get(), b->children[i - 1].get());
        }
        return true;
    }

    DAGNode::~DAGNode() {
        // Release arbitrarily deep DAGs without recursion through shared_ptr.
        // A nested destructor only queues its children; the outermost one
        // drains the queue. Live shared nodes are never modified.
        static thread_local std::vector<std::shared_ptr<DAGNode>>* active = nullptr;
        if (active) {
            for (auto& child : children) active->push_back(std::move(child));
            return;
        }
        std::vector<std::shared_ptr<DAGNode>> pending;
        pending.swap(children);
        active = &pending;
        while (!pending.empty()) {
            auto child = std::move(pending.back());
            pending.pop_back();
            child.reset();
        }
        active = nullptr;
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
     *  SMT-LIB 2.6 §3.1 gives a symbol two spellings: a SIMPLE symbol, whose
     *  characters are letters, digits and `~!@$%^&*_-+=<>.?/` and which may not
     *  start with a digit; and a QUOTED one, `|...|`, which may contain
     *  anything but `|` and `\`. The two denote the same symbol, so choosing
     *  between them is a printing decision.
     *
     *  It was not being made. A name that arrived quoted was printed quoted,
     *  because the bars were kept as part of the name; a name built through the
     *  public API was printed exactly as given. So a variable created as
     *  `x(1)` -- legal through mkVar, and a perfectly ordinary identifier in
     *  several input languages this library reads -- was emitted as
     *
     *      (declare-fun x(1) () Int)
     *
     *  which is not a well-formed command. No other solver accepts it, and this
     *  library reads it back only because getSymbol() scans leniently, so the
     *  defect did not show up in a round trip through this parser alone.
     *
     *  Quoting is applied where the symbol is printed rather than where it is
     *  stored, because the stored name is the symbol's identity and `x(1)` and
     *  `|x(1)|` are the same symbol. */
    std::string smtSymbolImpl(const std::string& name) {
        if (name.empty()) { return "||"; }
        if (name.size() >= 2 && name.front() == '|' && name.back() == '|') {
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
            return name;
        }
        else if(sort->isStr()){
            return name;
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
        if (n->isCInt() || n->isCReal()) {
            try { return Number(n->getName(), false); } catch (...) { return std::nullopt; }
        }
        const NODE_KIND k = n->getKind();
        const size_t sz = n->getChildrenSize();
        if (k == NODE_KIND::NT_NEG && sz == 1) {
            auto a = constToNumber(n->getChild(0));
            if (a) return -*a;
        } else if ((k == NODE_KIND::NT_DIV_REAL || k == NODE_KIND::NT_DIV_INT) && sz == 2) {
            auto a = constToNumber(n->getChild(0));
            auto b = constToNumber(n->getChild(1));
            if (a && b && !b->isZero()) return *a / *b;
        } else if (k == NODE_KIND::NT_ADD && sz >= 1) {
            auto acc = constToNumber(n->getChild(0)); if (!acc) return std::nullopt;
            for (size_t i = 1; i < sz; ++i) { auto c = constToNumber(n->getChild(i)); if (!c) return std::nullopt; acc = *acc + *c; }
            return acc;
        } else if (k == NODE_KIND::NT_SUB && sz >= 1) {
            auto acc = constToNumber(n->getChild(0)); if (!acc) return std::nullopt;
            if (sz == 1) return -*acc;
            for (size_t i = 1; i < sz; ++i) { auto c = constToNumber(n->getChild(i)); if (!c) return std::nullopt; acc = *acc - *c; }
            return acc;
        } else if (k == NODE_KIND::NT_MUL && sz >= 1) {
            auto acc = constToNumber(n->getChild(0)); if (!acc) return std::nullopt;
            for (size_t i = 1; i < sz; ++i) { auto c = constToNumber(n->getChild(i)); if (!c) return std::nullopt; acc = *acc * *c; }
            return acc;
        }
        return std::nullopt;
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

    // Takes a raw pointer so that a node can print itself without owning a
    // shared_ptr to itself (see DAGNode::orderKey). Ownership is the caller's;
    // this only reads.
    //
    // `hb`, when set, must be the streambuf backing `out`: it switches on the
    // subtree folding described on PrintHashBuf. It is null for ordinary
    // printing, which always walks the whole term.
    void dumpSMTLIB2_streaming(DAGNode* root, std::ostream& out, PrintHashBuf* hb = nullptr) {
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

            WorkItem(DAGNode* n, uint8_t a = 0) : node(n), action(a) {}
            
            // For text output
            std::string text;
            WorkItem(const std::string& t, uint8_t a = 4) : node(nullptr), action(a), text(t) {}
        };

        // Pre-allocate stack with reasonable capacity to avoid frequent reallocations
        std::vector<WorkItem> work_stack;
        work_stack.reserve(65536); // Reserve space for deep expressions
        work_stack.emplace_back(actualRoot, 0);

        while (!work_stack.empty()) {
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
            

            // Process node (action == 0)
            DAGNode* node = item.node;
            if (!node) continue;

            // Every node -- root and child alike -- reaches the printer through
            // this one point, so folding in an already-hashed subtree here
            // covers all of them.
            if (hb && node->hasPrintHash()) {
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
                    work_stack.emplace_back(mant, 0);     // mant
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(exp, 0);      // exp
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(sign, 0);     // sign
                } else {
                    out << dumpConst(node->getName(), node->getSort());
                }
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
                work_stack.emplace_back(node->getChild(0).get(), 0);   // child0
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
                    auto child0 = node->getChild(0).get();
                    auto child1 = node->getChild(1).get();

                    const char* op = kind_cache[kind];
                    out << "(" << op << " ";

                    // Push in reverse order: close_paren, child1, space, child0
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(child1, 0);   // child1
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(child0, 0);   // child0
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
                const auto& children = node->getChildren();

                // Push closing paren first
                work_stack.emplace_back(nullptr, 2);

                // Push children in reverse order, each preceded by a space
                for (int i = children.size() - 1; i >= 0; i--) {
                    auto child = children[i].get();
                    work_stack.emplace_back(child, 0);
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
                work_stack.emplace_back(child0, 0);      // child0
                work_stack.emplace_back(nullptr, 3);     // ") " - special case
                work_stack.emplace_back(child2, 0);      // child2
                work_stack.emplace_back(nullptr, 1);     // space
                work_stack.emplace_back(child1, 0);      // child1
                break;
            }
            // Unary operations
            case NODE_KIND::NT_NOT:
            case NODE_KIND::NT_NEG: {
                auto child = node->getChild(0).get();
                const char* op = kind_cache[kind];

                out << "(" << op << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child, 0);    // child
                break;
            }

            // Ternary operations
            case NODE_KIND::NT_ITE: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "(ite ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child2, 0);   // child2
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child1, 0);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0);   // child0
                break;
            }

            // Special processing operations
            case NODE_KIND::NT_BV_EXTRACT: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "((_ extract ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child0, 0);   // child0
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(child2, 0);   // child2
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child1, 0);   // child1
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
                work_stack.emplace_back(child0, 0);   // child0
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(child1, 0);   // child1
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
                        out << "(" << current_child->getName() << " " << current_child->getSort()->toString() << ")";
                    }
                    else{
                        out << " (" << current_child->getName() << " " << current_child->getSort()->toString() << ")";
                    }
                }
                out << ") ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(node->getChild(0).get(), 0);  // body
                break;
            }

            case NODE_KIND::NT_QUANT_VAR:
                out << node->getName();
                break;

            // Function related
            case NODE_KIND::NT_FUNC_DEC:
            case NODE_KIND::NT_FUNC_DEF:
            case NODE_KIND::NT_FUNC_REC:
            case NODE_KIND::NT_FUNC_PARAM:
                out << node->getName();
                break;

            // Function applications
            case NODE_KIND::NT_FUNC_APPLY: {
                // For NT_FUNC_APPLY, children[0] is function, children[1..] are parameters
                // If no parameters (size <= 1), output just the name without parentheses
                if (node->getChildrenSize() <= 1) {
                    out << node->getName();
                } else {
                    out << "(" << node->getName();
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = node->getChildrenSize() - 1; i >= 1; i--) {
                        auto current_child = node->getChild(i).get();
                        work_stack.emplace_back(current_child, 0);
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
                work_stack.emplace_back(node->getChild(0).get(), 0);  // body
                work_stack.emplace_back(") ", 4);  // close binding list and add space
                
                // Process bindings in reverse order for stack
                for(int i = node->getChildrenSize() - 1; i >= 1; i--){
                    work_stack.emplace_back(")", 4);  // ) for this binding
                    work_stack.emplace_back(node->getChild(i)->getChild(0).get(), 0);  // binding value
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
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 1).get(), 0);
                
                // Process let bindings in reverse order
                for(int i = num_bindings - 1; i >= 0; i--){
                    condAssert(node->getChild(i)->isLetBindVarList(), "NT_LET_CHAIN: child is not LET_BIND_VAR_LIST");
                    auto var_list = node->getChild(i);
                    
                    work_stack.emplace_back(") ", 4);  // close binding list and add space
                    
                    // Process variables in this binding list (reverse order)
                    for(int j = var_list->getChildrenSize() - 1; j >= 0; j--){
                        work_stack.emplace_back(")", 4);  // ) for binding
                        work_stack.emplace_back(var_list->getChild(j)->getChild(0).get(), 0);  // binding value
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
                    work_stack.emplace_back(node->getChild(i)->getChild(0).get(), 0);  // binding value
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
                    out << node->getName();
                } else {
                    out << "(" << node->getName();
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 0; i--) {  // Start from 0
                        auto current_child = children[i].get();
                        work_stack.emplace_back(current_child, 0);
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
                        work_stack.emplace_back(children[i].get(), 0);
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
                        work_stack.emplace_back(children[i].get(), 0);
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
                        work_stack.emplace_back(children[i].get(), 0);
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
                    work_stack.emplace_back(children[i].get(), 0);
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
                    work_stack.emplace_back(children[i].get(), 0);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }
            case NODE_KIND::NT_PATTERN: {
                const auto& children = node->getChildren();
                out << ":pattern (";
                work_stack.emplace_back(nullptr, 2);  // )
                for (int i = children.size() - 1; i >= 0; i--) {
                    work_stack.emplace_back(children[i].get(), 0);
                    if (i) work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }
            case NODE_KIND::NT_NO_PATTERN: {
                out << ":no-pattern ";
                if (node->getChildrenSize() > 0) {
                    work_stack.emplace_back(node->getChild(0).get(), 0);
                }
                break;
            }
            case NODE_KIND::NT_WEIGHT: {
                out << ":weight ";
                if (node->getChildrenSize() > 0) {
                    work_stack.emplace_back(node->getChild(0).get(), 0);
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
                    work_stack.emplace_back(children[i].get(), 0);
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
                    work_stack.emplace_back(children[2].get(), 0);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                if (!children.empty()) {
                    work_stack.emplace_back(children[0].get(), 0);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                work_stack.emplace_back(")", 4);
                for (size_t i = nidx; i >= 1; i--) {
                    work_stack.emplace_back(children[i].get(), 0);
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
                        work_stack.emplace_back(children[bi].get(), 0);
                        work_stack.emplace_back(nullptr, 1);
                        work_stack.emplace_back(children[pi].get(), 0);
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
                work_stack.emplace_back(children[0].get(), 0);
                work_stack.emplace_back(nullptr, 1);
                break;
            }
            
            case NODE_KIND::NT_FUNC_REC_APPLY: {
                // For recursive function applications, children[0] is the function definition, children[1..] are parameters
                // Only output the parameters, not the function definition
                // If no parameters (size <= 1), output just the name without parentheses
                const auto& children = node->getChildren();
                if (children.size() <= 1) {
                    out << node->getName();
                } else {
                    out << "(" << node->getName();
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 1; i--) {  // Start from 1, not 0
                        auto current_child = children[i].get();
                        work_stack.emplace_back(current_child, 0);
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
                    work_stack.emplace_back(current_child, 0);
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
                    work_stack.emplace_back(current_child, 0);
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
                work_stack.emplace_back(child, 0);    // child
                break;
            }

            case NODE_KIND::NT_FP_REM: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                out << "(fp.rem ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child1, 0);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0);   // child0
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
                work_stack.emplace_back(child1, 0);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0);   // child0
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
                work_stack.emplace_back(fp, 0);       // fp
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(rm, 0);       // rm
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(size, 0);     // size
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
                        if (fpsort && fpsort->isFp()) {
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
                    work_stack.emplace_back(param, 0);    // param
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(rm, 0);       // rm
                    work_stack.emplace_back(nullptr, 3);  // ") "
                    work_stack.emplace_back(sb, 0);       // sb
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(eb, 0);       // eb
                } else if(node->getChildrenSize() == 3) {
                    // 3-parameter version: ((_ to_fp eb sb) param)
                    auto param = node->getChild(2).get();
                    out << "((_ to_fp ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(param, 0);    // param
                    work_stack.emplace_back(nullptr, 3);  // ") "
                    work_stack.emplace_back(sb, 0);       // sb
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(eb, 0);       // eb
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
                work_stack.emplace_back(param, 0);    // param
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(rm, 0);       // rm
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(sb, 0);       // sb
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(eb, 0);       // eb
                break;
            }

            case NODE_KIND::NT_FP_TO_IEEE_BV: {
                auto param = node->getChild(0).get();
                size_t nbits = node->getSort()->getBitWidth();
                out << "((_ fp.to_ieee_bv " << nbits << ") ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(param, 0);    // param
                break;
            }

            case NODE_KIND::NT_ROOT_OBJ: {
                auto expr = node->getChild(0).get();
                auto index = node->getChild(1).get();
                out << "(root-obj ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(index, 0);    // index
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(expr, 0);     // expr
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
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 1).get(), 0);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 3. Push lower bound
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 2).get(), 0);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 4. Push closing parenthesis for coeffs list
                work_stack.emplace_back(nullptr, 2);  // )
                
                // 5. Push coefficients in reverse order (so they print in correct order)
                for(int i = node->getChildrenSize() - 3; i >= 0; i--) {
                    work_stack.emplace_back(node->getChild(i).get(), 0);
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
                work_stack.emplace_back(node->getChild(2).get(), 0);
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(",", 4);  // ','
                
                // 4. Push lower bound
                work_stack.emplace_back(node->getChild(1).get(), 0);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 5. Push opening parenthesis for interval
                work_stack.emplace_back("(", 4);  // '('
                
                // 6. Push comma and space
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(",", 4);  // ','
                
                // 7. Push polynomial
                work_stack.emplace_back(node->getChild(0).get(), 0);
                
                break;
            }

            // Array operations
            case NODE_KIND::NT_SELECT: {
                // select(array, index) -> (select array index)
                auto array = node->getChild(0).get();
                auto index = node->getChild(1).get();
                out << "(select ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(index, 0);    // index
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(array, 0);    // array
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
                work_stack.emplace_back(value, 0);    // value
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(index, 0);    // index
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(array, 0);    // array
                break;
            }

            default: {
                // Fallback for other cases - iterative version
                std::string kind_str = kindToString(kind);
                const auto& children = node->getChildren();

                if (children.empty()) {
                    out << kind_str;
                } else if (children.size() == 1) {
                    auto child = children[0].get();
                    out << "(" << kind_str << " ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(child, 0);    // child
                } else {
                    out << "(" << kind_str;
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 0; i--) {
                        auto child = children[i].get();
                        work_stack.emplace_back(child, 0);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }
            }
        }
    }

    // Wrapper function that returns string for compatibility
    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& root) {
        std::ostringstream oss;
        dumpSMTLIB2_streaming(root.get(), oss);  // enable cache by default
        return oss.str();
    }

    std::size_t DAGNode::orderKey() const {
        if(print_hash_computed) {
            return static_cast<std::size_t>(cached_print_hash);
        }
        // const_cast is safe: the printer only reads. Its parameter is
        // non-const because its internal work stack holds DAGNode*.
        PrintHashBuf buf;
        std::ostream os(&buf);
        dumpSMTLIB2_streaming(const_cast<DAGNode*>(this), os, &buf);
        cached_print_hash = buf.hash();
        cached_print_len = buf.length();
        print_hash_computed = true;
        return static_cast<std::size_t>(cached_print_hash);
    }

    
    std::string dumpFuncDef(const std::shared_ptr<DAGNode>& node){
        std::string res = "(define-fun " + node->getName() + " (";
        // For NT_FUNC_DEF, children[0] is body, children[1..n] are parameters
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i==1) res += "(" + node->getChild(i)->getName() +" " + node->getChild(i)->getSort()->toString() +")";
            else res += " (" + node->getChild(i)->getName() +" " + node->getChild(i)->getSort()->toString() +")";
        }
        // Use node's declared sort, not body's inferred sort (which may be widened to IntOrReal)
        res += ") " + node->getSort()->toString() + " ";
        res += dumpSMTLIB2(node->getChild(0)) +  ")";
        return res;
    }
    std::string dumpFuncRec(const std::shared_ptr<DAGNode>& node){
        std::string res = "(define-fun-rec " + node->getName() + " (";
        // For NT_FUNC_REC, children[0] is body, children[1..n] are parameters
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i==1) res += "(" + node->getChild(i)->getName() +" " + node->getChild(i)->getSort()->toString() +")";
            else res += " (" + node->getChild(i)->getName() +" " + node->getChild(i)->getSort()->toString() +")";
        }
        // Use node's declared sort, not body's inferred sort (which may be widened to IntOrReal)
        res += ") " + node->getSort()->toString() + " ";
        res += dumpSMTLIB2(node->getChild(0)) +  ")";
        return res;
    }
    // (define-funs-rec ((f (params) sort) ...) (body ...))
    //
    // A mutually recursive group has to be emitted as one command: its members
    // call each other, so a sequence of define-fun-rec commands would refer to
    // a function that the script has not defined yet.  SMT-LIB puts all the
    // signatures first precisely so every body can see every name.
    std::string dumpFuncsRec(const std::vector<std::shared_ptr<DAGNode>>& nodes){
        condAssert(!nodes.empty(), "dumpFuncsRec: empty group");
        std::string res = "(define-funs-rec (";
        for(size_t n = 0; n < nodes.size(); n++){
            const auto& node = nodes[n];
            condAssert(node != nullptr, "dumpFuncsRec: null member");
            if(n != 0) res += " ";
            res += "(" + node->getName() + " (";
            // children[0] is the body, children[1..n] are the parameters.
            for(size_t i = 1; i < node->getChildrenSize(); i++){
                if(i != 1) res += " ";
                res += "(" + node->getChild(i)->getName() + " " +
                       node->getChild(i)->getSort()->toString() + ")";
            }
            res += ") " + node->getSort()->toString() + ")";
        }
        res += ") (";
        for(size_t n = 0; n < nodes.size(); n++){
            if(n != 0) res += " ";
            res += dumpSMTLIB2(nodes[n]->getChild(0));
        }
        res += "))";
        return res;
    }

    std::string dumpFuncDec(const std::shared_ptr<DAGNode>& node){
        std::string res = "(declare-fun " + node->getName() + " (";
        // For NT_FUNC_DEC, children[0] is NULL_NODE, children[1..n] are parameter type nodes
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i==1) res += node->getChild(i)->getSort()->toString();
            else res += " " + node->getChild(i)->getSort()->toString();
        }
        // The return type is stored in the node's sort, not in children[0]
        res += ") " + node->getSort()->toString() + ")";
        return res;
    }

    // NodeManager
    
    // Static constant nodes are now defined inline in the header file

    NodeManager::NodeManager() {
        // Grow the node vector and each kind's hash table on insertion. Most
        // contexts use only a few kinds; reserving thousands of entries for
        // every kind made creating and clearing even tiny contexts expensive.
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
        // Drop manager ownership, preserving nodes retained by query handles.
        // Destructive node->clear() invalidated DAGs shared with other users.
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
