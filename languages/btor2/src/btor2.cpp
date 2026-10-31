/* -*- Source -*-
 * BTOR2 frontend — bounded model checking of a word-level transition system.
 *
 * The format is docs/languages/btor2.md; its `implicit-constraints` block is
 * the specification this file implements, and each entry has a fixture in
 * languages/btor2/instances.
 *
 * **A BTOR2 file is a machine, not a query.** It has state variables, an `init`
 * for step 0, a `next` for every step after, environment `constraint`s that hold
 * at every step, and a `bad` property asking whether some reachable state
 * satisfies it. No assignment answers that: the question is about an unbounded
 * sequence of steps.
 *
 * So the translation is an UNROLLING, and it is an under-approximation with a
 * bound. `docs/design-transition-system.md` proposed three places to put the
 * transition-system shape; this takes the third -- the system exists inside the
 * frontend and never reaches a consumer -- and the objection recorded against
 * that option ("the report cannot say the input was a system") turned out to be
 * wrong. The fidelity channel says exactly that: an EncodingChoice carrying
 * `underApprox(Bound{BMC_DEPTH, k})` records both the shape and the bound, with
 * no change to ConstraintModel's contract.
 *
 * **The direction of the approximation is easy to get backwards.** A BMC run
 * finds counterexamples; it does not prove safety.
 *
 *     sat at depth k    a real trace to the bad state -- comparable to the
 *                       competition's answer
 *     unsat at depth k  NO COUNTEREXAMPLE WITHIN k STEPS -- not "safe"
 *
 * That is `sound = true, complete = false`, and reporting an unsat as "safe"
 * would be wrong twice over.
 *
 * **The two absent functions** (§4.3) both denote nondeterminism:
 *
 *   * A `state` with no `next` is treated as a primary input by BTOR2. Its value
 *     is fresh at each step. Adding `s_{i+1} = s_i` removes source traces and can
 *     miss a real counterexample.
 *   * A `state` with no `init` is UNCONSTRAINED at step 0. The tempting default
 *     is zero, because hardware registers usually reset to zero. Adding
 *     `s_0 = 0` REMOVES initial states, so a bad state reachable only from a
 *     non-zero start becomes unreachable -- **incomplete**, reporting "safe"
 *     for an unsafe circuit.
 *
 * The rule is: add no equation for a function the source did not define.
 *
 * **The unrolling depth has no default.** §4.3 names silent defaults as this
 * format's hazard and a frontend-chosen depth is one of them: every instance
 * would then be measured at a bound nobody recorded choosing. It comes from
 * `ParseOptions::options["bmc_depth"]`, and an instance translated without one
 * is refused.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/btor2.h"
#include "somtparser/hir/typecheck.h"

#include <algorithm>
#include <array>
#include <cerrno>
#include <cctype>
#include <cstdlib>
#include <deque>
#include <filesystem>
#include <fstream>
#include <limits>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <streambuf>
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

// Every fixed-arity BTOR2 record has at most four numeric fields. Keep them
// in the record so a large circuit does not allocate a tiny vector per gate.
// Only variable-arity justice records borrow a parser-owned overflow vector.
class NumericArguments {
public:
    void push_back(long long value) {
        if (count_ >= 4) { throw std::length_error("fixed BTOR2 record has more than four fields"); }
        storage_.values[count_++] = value;
    }
    void useOverflow(const std::vector<long long>& values) {
        if (values.size() <= 4) { throw std::logic_error("BTOR2 argument overflow is not needed"); }
        storage_.overflow = &values;
        count_ = values.size();
    }
    std::size_t size() const { return count_; }
    bool empty() const { return count_ == 0; }
    const long long* data() const {
        return count_ <= 4 ? storage_.values.data() : storage_.overflow->data();
    }
    const long long* begin() const { return data(); }
    const long long* end() const { return data() + count_; }
    long long operator[](std::size_t index) const { return data()[index]; }

private:
    union Storage {
        std::array<long long, 4> values;
        const std::vector<long long>* overflow;
        Storage() : values{} {}
    } storage_;
    std::size_t count_ = 0;
};

struct OperandRange {
    const long long* first = nullptr;
    const long long* last = nullptr;
    const long long* begin() const { return first; }
    const long long* end() const { return last; }
};

struct Line {
    long long                 id = 0;
    std::string_view          op;
    NumericArguments         args;       // sort id first for most operators
    // Nonempty text is owned by Btor2Parser::text_storage_; most records have
    // neither field, and these pointers never refer into the input buffer.
    const std::string*        literal = nullptr; // const/constd/consth
    const std::string*        symbol = nullptr;  // state/input/output names only
    int                       lineno = 0;
    bool                      array_sort = false;
    mutable bool              depends_on_input = false;
    // Every source term is checked at frame zero. Store that dense cache in
    // its existing record rather than allocating a hash node for every ID.
    // Later, potentially sparse frames retain the pair-keyed cache below.
    mutable H::ExprPtr         frame_zero_term;

    const std::string& literalText() const {
        static const std::string empty;
        return literal == nullptr ? empty : *literal;
    }

    const std::string& symbolText() const {
        static const std::string empty;
        return symbol == nullptr ? empty : *symbol;
    }
};

/** A sort table entry. BTOR2 sorts are explicit, so nothing is inferred. */
struct SortDef {
    bool      is_array = false;
    unsigned  width = 0;              // bitvec
    long long index_sort = 0, elem_sort = 0;
};

// std::istringstream owns another complete string. This get-only buffer borrows
// the immutable SourceUnit text for the synchronous parse instead; no HIR node
// retains a pointer into it. std::istream never writes to the get area.
class SourceBuffer : public std::streambuf {
public:
    explicit SourceBuffer(const std::string& source) {
        char* begin = const_cast<char*>(source.data());
        setg(begin, begin, begin + source.size());
    }
};

class Btor2Parser {
public:
    Btor2Parser(std::istream& input, std::string file, unsigned depth)
        : input_(input), file_(std::move(file)), depth_(depth) {}

    ~Btor2Parser() {
        // Drop parents before their earlier source operands. An unused deep
        // circuit must not turn record teardown into recursive Expr teardown;
        // each child is still owned by its own record when its parent drops.
        for (auto it = lines_.rbegin(); it != lines_.rend(); ++it) {
            it->frame_zero_term.reset();
        }
    }

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        try {
            phase_ = "reading source records";
            if (!read(diags)) { return nullptr; }
            phase_ = "validating references";
            if (!validateReferences(diags)) { return nullptr; }
            return build(diags, report);
        } catch (const std::bad_alloc&) {
            diags.error(ErrorCode::E_RESOURCE,
                        std::string("BTOR2 exhausted memory while ") + phase_);
            return nullptr;
        }
    }

private:
    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = line;
        return l;
    }

    bool integerToken(const std::string& token, long long& out, int line,
                      Uir::Diagnostics& diags) const {
        char* end = nullptr;
        errno = 0;
        out = std::strtoll(token.c_str(), &end, 10);
        if (errno == ERANGE || end == token.c_str() || *end != '\0') {
            diags.error(ErrorCode::E_PARSE,
                        "expected a machine integer, got `" + token + "`", at(line));
            return false;
        }
        return true;
    }

    static std::string trailingSymbol(const std::vector<std::string>& tok,
                                      std::size_t start) {
        std::string out;
        for (std::size_t i = start; i < tok.size(); ++i) {
            if (!out.empty()) { out += " "; }
            out += tok[i];
        }
        return out;
    }

    /** Fixed numeric fields after the operator, including a sort id where the
     *  grammar has one. Keys are static literals, so returned operator views
     *  never point into a token or source buffer. Sort/constants/justice are
     *  handled separately because their fields are not all numeric. */
    static const std::unordered_map<std::string_view, int>& fixedArgCounts() {
        static const std::unordered_map<std::string_view, int> counts = {
            {"input", 1}, {"state", 1}, {"zero", 1}, {"one", 1}, {"ones", 1},
            {"init", 3}, {"next", 3},
            {"bad", 1}, {"constraint", 1}, {"fair", 1}, {"output", 1},
            {"slice", 4}, {"uext", 3}, {"sext", 3},
            {"not", 2}, {"inc", 2}, {"dec", 2}, {"neg", 2},
            {"redand", 2}, {"redor", 2}, {"redxor", 2},
            {"add", 3}, {"sub", 3}, {"mul", 3}, {"udiv", 3}, {"sdiv", 3},
            {"urem", 3}, {"srem", 3}, {"smod", 3}, {"and", 3}, {"or", 3},
            {"xor", 3}, {"nand", 3}, {"nor", 3}, {"xnor", 3},
            {"sll", 3}, {"srl", 3}, {"sra", 3}, {"rol", 3}, {"ror", 3},
            {"concat", 3}, {"eq", 3}, {"neq", 3}, {"ult", 3}, {"ulte", 3},
            {"ugt", 3}, {"ugte", 3}, {"slt", 3}, {"slte", 3}, {"sgt", 3},
            {"sgte", 3}, {"implies", 3}, {"iff", 3}, {"read", 3},
            {"uaddo", 3}, {"saddo", 3}, {"usubo", 3}, {"ssubo", 3},
            {"umulo", 3}, {"smulo", 3}, {"sdivo", 3},
            {"ite", 4}, {"write", 4},
        };
        return counts;
    }

    static std::string_view canonicalOperator(std::string_view op, int& fixed_args) {
        const auto it = fixedArgCounts().find(op);
        if (it != fixedArgCounts().end()) {
            fixed_args = it->second;
            return it->first;
        }
        static constexpr std::array<std::string_view, 5> special = {
            "sort", "const", "constd", "consth", "justice"
        };
        for (const std::string_view known : special) {
            if (op == known) { return known; }
        }
        return {};
    }

    static std::string quotedOperator(std::string_view op) {
        std::string result;
        result.reserve(op.size() + 2);
        result.push_back('\'');
        result.append(op.data(), op.size());
        result.push_back('\'');
        return result;
    }

    const std::string* storeText(std::string value) {
        if (value.empty()) { return nullptr; }
        // deque end insertion preserves references to existing elements. Lines
        // keep these pointers only until parse/build finishes; no source view
        // or token buffer is borrowed.
        text_storage_.push_back(std::move(value));
        return &text_storage_.back();
    }

    bool read(Uir::Diagnostics& diags) {
        std::string raw;
        int lineno = 0;
        long long previous_id = 0;
        while (std::getline(input_, raw)) {
            ++lineno;
            if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
            const std::size_t comment = raw.find(';');
            if (comment != std::string::npos) { raw.erase(comment); }
            const std::size_t a = raw.find_first_not_of(" \t");
            if (a == std::string::npos) { continue; }
            std::istringstream ls(raw);
            std::vector<std::string> tok;
            std::string t;
            while (ls >> t) { tok.push_back(t); }
            if (tok.size() < 2) {
                diags.error(ErrorCode::E_PARSE, "a line needs an id and a name",
                            at(lineno));
                return false;
            }
            Line l;
            l.lineno = lineno;
            if (!integerToken(tok[0], l.id, lineno, diags)) { return false; }
            if (l.id <= previous_id) {
                diags.error(ErrorCode::E_PARSE,
                            "node ids must be positive and strictly increasing", at(lineno));
                return false;
            }
            previous_id = l.id;
            int fixed_args = -1;
            l.op = canonicalOperator(tok[1], fixed_args);
            if (l.op.empty()) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "unknown BTOR2 tag `" + tok[1] + "`", at(lineno));
                return false;
            }

            std::size_t symbol_at = 2;
            if (l.op == "sort") {
                if (tok.size() < 4 || (tok[2] != "bitvec" && tok[2] != "array")) {
                    diags.error(ErrorCode::E_PARSE,
                                "sort must be `bitvec <width>` or `array <index> <element>`",
                                at(lineno));
                    return false;
                }
                l.array_sort = tok[2] == "array";
                const std::size_t nargs = l.array_sort ? 2 : 1;
                if (tok.size() < 3 + nargs) {
                    diags.error(ErrorCode::E_PARSE, "incomplete sort declaration", at(lineno));
                    return false;
                }
                for (std::size_t i = 0; i < nargs; ++i) {
                    long long value = 0;
                    if (!integerToken(tok[3 + i], value, lineno, diags)) { return false; }
                    l.args.push_back(value);
                }
                symbol_at = 3 + nargs;
            } else if (l.op == "const" || l.op == "constd" || l.op == "consth") {
                if (tok.size() < 4) {
                    diags.error(ErrorCode::E_PARSE,
                                quotedOperator(l.op) + " needs a sort and a literal",
                                at(lineno));
                    return false;
                }
                long long sort_id = 0;
                if (!integerToken(tok[2], sort_id, lineno, diags)) { return false; }
                l.args.push_back(sort_id);
                l.literal = storeText(tok[3]);
                symbol_at = 4;
            } else if (l.op == "justice") {
                if (tok.size() < 3) {
                    diags.error(ErrorCode::E_PARSE, "'justice' needs an arity", at(lineno));
                    return false;
                }
                long long count = 0;
                if (!integerToken(tok[2], count, lineno, diags) || count <= 0
                    || static_cast<unsigned long long>(count)
                           > static_cast<unsigned long long>(tok.size() - 3)) {
                    diags.error(ErrorCode::E_PARSE, "invalid justice arity", at(lineno));
                    return false;
                }
                std::vector<long long>* overflow = nullptr;
                if (count > 4) {
                    justice_arguments_.emplace_back();
                    overflow = &justice_arguments_.back();
                    overflow->reserve(static_cast<std::size_t>(count));
                }
                for (long long i = 0; i < count; ++i) {
                    long long id = 0;
                    if (!integerToken(tok[3 + static_cast<std::size_t>(i)], id,
                                      lineno, diags)) {
                        return false;
                    }
                    if (overflow) { overflow->push_back(id); }
                    else { l.args.push_back(id); }
                }
                if (overflow) { l.args.useOverflow(*overflow); }
                symbol_at = 3 + static_cast<std::size_t>(count);
            } else {
                const int nargs = fixed_args;
                if (tok.size() < 2 + static_cast<std::size_t>(nargs)) {
                    diags.error(ErrorCode::E_PARSE,
                                quotedOperator(l.op) + " has too few arguments", at(lineno));
                    return false;
                }
                for (int i = 0; i < nargs; ++i) {
                    long long value = 0;
                    if (!integerToken(tok[2 + static_cast<std::size_t>(i)], value,
                                      lineno, diags)) {
                        return false;
                    }
                    l.args.push_back(value);
                }
                symbol_at = 2 + static_cast<std::size_t>(nargs);
            }
            // Only these names affect declarations/projections. Gate, sort,
            // and liveness annotations have never been observed downstream.
            if (l.op == "state" || l.op == "input" || l.op == "output") {
                l.symbol = storeText(trailingSymbol(tok, symbol_at));
            }
            lines_.push_back(std::move(l));
        }
        if (input_.bad()) {
            diags.error(ErrorCode::E_IO, "failed to read BTOR2 source", at(lineno));
            return false;
        }
        if (lines_.empty()) {
            diags.error(ErrorCode::E_PARSE, "the file has no lines", at(0));
            return false;
        }
        return true;
    }

    static bool hasSortId(std::string_view op) {
        return op != "sort" && op != "bad" && op != "constraint" && op != "fair"
            && op != "output" && op != "justice";
    }

    OperandRange nodeOperands(const Line& l) const {
        if (l.op == "sort" || l.op == "state" || l.op == "input" || l.op == "zero"
            || l.op == "one" || l.op == "ones" || l.op == "const"
            || l.op == "constd" || l.op == "consth") {
            return {};
        }
        if (l.op == "bad" || l.op == "constraint" || l.op == "fair"
            || l.op == "output" || l.op == "justice") {
            return {l.args.begin(), l.args.end()};
        }
        if (l.op == "slice" || l.op == "uext" || l.op == "sext") {
            return l.args.size() > 1 ? OperandRange{l.args.begin() + 1, l.args.begin() + 2}
                                     : OperandRange{};
        }
        if (l.args.size() <= 1) { return {}; }
        return {l.args.begin() + 1, l.args.end()};
    }

    bool validateReferences(Uir::Diagnostics& diags) const {
        for (const Line& l : lines_) {
            // References must point strictly backwards. Propagate input
            // dependence in that same pass, without rewalking each init DAG
            // or using the C++ call stack for arbitrarily deep circuits.
            l.depends_on_input = l.op == "input";
            if (l.op == "sort") {
                if (l.array_sort) {
                    for (const long long sid : l.args) {
                        const Line* sort = lineOf(sid);
                        if (sid <= 0 || sid >= l.id || sort == nullptr || sort->op != "sort") {
                            diags.error(ErrorCode::E_PARSE,
                                        "array sort references undeclared earlier sort "
                                            + std::to_string(sid),
                                        at(l.lineno));
                            return false;
                        }
                    }
                }
            } else if (hasSortId(l.op)) {
                if (l.args.empty()) {
                    diags.error(ErrorCode::E_PARSE, quotedOperator(l.op) + " needs a sort",
                                at(l.lineno));
                    return false;
                }
                const Line* sort = lineOf(l.args[0]);
                if (l.args[0] <= 0 || l.args[0] >= l.id || sort == nullptr
                    || sort->op != "sort") {
                    diags.error(ErrorCode::E_PARSE,
                                quotedOperator(l.op) + " references undeclared earlier sort "
                                    + std::to_string(l.args[0]),
                                at(l.lineno));
                    return false;
                }
            }

            for (const long long signed_id : nodeOperands(l)) {
                if (signed_id == std::numeric_limits<long long>::min()) {
                    diags.error(ErrorCode::E_PARSE, "a negated node id is out of range",
                                at(l.lineno));
                    return false;
                }
                const long long id = std::llabs(signed_id);
                const Line* operand = lineOf(id);
                if (id <= 0 || id >= l.id || operand == nullptr || operand->op == "sort") {
                    diags.error(ErrorCode::E_PARSE,
                                quotedOperator(l.op) + " references undeclared earlier node "
                                    + std::to_string(signed_id),
                                at(l.lineno));
                    return false;
                }
                l.depends_on_input = l.depends_on_input || operand->depends_on_input;
            }

            if (l.op == "init" || l.op == "next") {
                const long long state_id = l.args[1];
                const Line* state = lineOf(state_id);
                if (state_id <= 0 || state == nullptr || state->op != "state") {
                    diags.error(ErrorCode::E_PARSE,
                                quotedOperator(l.op) + " first operand must be a state",
                                at(l.lineno));
                    return false;
                }
                if (l.op == "init") {
                    if (state_id <= std::llabs(l.args[2])) {
                        diags.error(ErrorCode::E_PARSE,
                                    "an init state id must be greater than its value id",
                                    at(l.lineno));
                        return false;
                    }
                    if (lineOf(std::llabs(l.args[2]))->depends_on_input) {
                        diags.error(ErrorCode::E_PARSE,
                                    "inputs are not allowed in initialization expressions",
                                    at(l.lineno));
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** The sort of a node id, resolved through the sort table. */
    bool sortOf(long long node_sort_id, H::Sort& out, int lineno,
                Uir::Diagnostics& diags) {
        const auto it = sorts_.find(node_sort_id);
        if (it == sorts_.end()) {
            diags.error(ErrorCode::E_PARSE,
                        "sort " + std::to_string(node_sort_id) + " is not declared",
                        at(lineno));
            return false;
        }
        if (it->second.is_array) {
            H::Sort idx, elem;
            if (!sortOf(it->second.index_sort, idx, lineno, diags)) { return false; }
            if (!sortOf(it->second.elem_sort, elem, lineno, diags)) { return false; }
            out = H::Sort::array(idx, elem);
            return true;
        }
        out = H::Sort::bitvec(it->second.width);
        return true;
    }

    /** `s@k` -- the name of a state or input at step k. Inputs are FRESH at
     *  every step, which is what makes them inputs rather than state. */
    static std::string stepName(const std::string& base, unsigned k) {
        return base + "@" + std::to_string(k);
    }

    std::string baseName(const Line& l) const {
        return l.symbolText().empty()
            ? (std::string(l.op) + std::to_string(l.id)) : l.symbolText();
    }

    std::string uniqueBaseName(const Line& l) {
        std::string name = baseName(l);
        if (!used_base_names_.insert(name).second) {
            name += "$" + std::to_string(l.id);
            used_base_names_.insert(name);
        }
        return name;
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        phase_ = "building declarations";
        auto model = std::make_shared<H::ConstraintModel>();

        // Pass 1: sorts, states and inputs, so the unrolling can declare every
        // step's variables before any term refers to them.
        for (const Line& l : lines_) {
            if (l.op == "sort") {
                SortDef s;
                if (l.array_sort) {
                    s.is_array = true;
                    s.index_sort = l.args[0];
                    s.elem_sort = l.args[1];
                    if (s.index_sort <= 0 || s.elem_sort <= 0) {
                        diags.error(ErrorCode::E_PARSE,
                                    "array sort ids must be positive", at(l.lineno));
                        return nullptr;
                    }
                } else {
                    if (l.args[0] <= 0
                        || static_cast<unsigned long long>(l.args[0])
                               > std::numeric_limits<unsigned>::max()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "a bit-vector width must be a positive machine width",
                                    at(l.lineno));
                        return nullptr;
                    }
                    s.width = static_cast<unsigned>(l.args[0]);
                }
                if (!s.is_array && s.width == 0) {
                    diags.error(ErrorCode::E_PARSE, "a bit-vector sort has width 0",
                                at(l.lineno));
                    return nullptr;
                }
                sorts_[l.id] = s;
            } else if (l.op == "state" || l.op == "input") {
                if (l.args.empty()) {
                    diags.error(ErrorCode::E_PARSE, quotedOperator(l.op) + " needs a sort",
                                at(l.lineno));
                    return nullptr;
                }
                H::Sort s;
                if (!sortOf(l.args[0], s, l.lineno, diags)) { return nullptr; }
                node_sort_[l.id] = s;
                (l.op == "state" ? states_ : inputs_).push_back(l.id);
                names_[l.id] = uniqueBaseName(l);
            } else if (l.op == "init") {
                if (l.args.size() < 3) {
                    diags.error(ErrorCode::E_PARSE, "'init' needs a sort, a state and a value",
                                at(l.lineno));
                    return nullptr;
                }
                H::Sort declared_sort;
                if (!sortOf(l.args[0], declared_sort, l.lineno, diags)) { return nullptr; }
                const auto state_sort = node_sort_.find(l.args[1]);
                if (state_sort == node_sort_.end()
                    || !H::sameSort(state_sort->second, declared_sort)) {
                    diags.error(ErrorCode::E_TYPE,
                                "init sort does not match its state", at(l.lineno));
                    return nullptr;
                }
                if (init_.count(l.args[1]) != 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "state " + std::to_string(l.args[1])
                                    + " has more than one init line",
                                at(l.lineno));
                    return nullptr;
                }
                init_[l.args[1]] = l.args[2];
            } else if (l.op == "next") {
                if (l.args.size() < 3) {
                    diags.error(ErrorCode::E_PARSE, "'next' needs a sort, a state and a value",
                                at(l.lineno));
                    return nullptr;
                }
                H::Sort declared_sort;
                if (!sortOf(l.args[0], declared_sort, l.lineno, diags)) { return nullptr; }
                const auto state_sort = node_sort_.find(l.args[1]);
                if (state_sort == node_sort_.end()
                    || !H::sameSort(state_sort->second, declared_sort)) {
                    diags.error(ErrorCode::E_TYPE,
                                "next sort does not match its state", at(l.lineno));
                    return nullptr;
                }
                if (next_.count(l.args[1]) != 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "state " + std::to_string(l.args[1])
                                    + " has more than one next line",
                                at(l.lineno));
                    return nullptr;
                }
                next_[l.args[1]] = l.args[2];
            } else if (l.op == "output") {
                outputs_.push_back(l.id);
                names_[l.id] = uniqueBaseName(l);
            } else if (l.op == "justice" || l.op == "fair") {
                // Liveness is a DIFFERENT problem, not a harder one (§4.5): it
                // asks about infinite behaviour, and a bounded unrolling cannot
                // express it. Translating it as a safety property would answer
                // a different question with the right shape.
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            quotedOperator(l.op) + " is a liveness property, which asks about "
                            "infinite behaviour; a bounded unrolling cannot express it, "
                            "and translating it as a safety property would answer a "
                            "different question",
                            at(l.lineno));
                return nullptr;
            }
        }

        if (bads().empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "no `bad` property: there is nothing to check, and an unrolling "
                        "with no property asserted is trivially satisfiable",
                        at(lines_.back().lineno));
            return nullptr;
        }

        // Every step gets its own copy of every state AND every input,
        // including the last. An input is fresh at every step -- that is what
        // makes it an input rather than a state -- and a `constraint` holds at
        // every step including step k, so an input is read there too.
        for (unsigned k = 0; k <= depth_; ++k) {
            for (const long long id : states_) {
                declare(*model, stepName(names_[id], k), node_sort_[id]);
            }
            for (const long long id : inputs_) {
                declare(*model, stepName(names_[id], k), node_sort_[id]);
            }
        }

        phase_ = "building and validating the term DAG";
        if (!validateAllTerms(*model, diags)) { return nullptr; }
        phase_ = "unrolling outputs and transitions";

        // Outputs are observations, not safety properties. Give each one a
        // defined target symbol at every frame so beta can reconstruct the
        // source trace without reinterpreting it as `bad`.
        for (const long long output_id : outputs_) {
            const Line* output = lineOf(output_id);
            for (unsigned k = 0; k <= depth_; ++k) {
                H::ExprPtr value = term(output->args[0], k, diags);
                if (!value) { return nullptr; }
                if (value->sort.kind != H::SortKind::BITVEC) {
                    diags.error(ErrorCode::E_TYPE,
                                "a BTOR2 output must have bit-vector sort",
                                at(output->lineno));
                    return nullptr;
                }
                const std::string name = stepName(names_[output_id], k);
                declare(*model, name, value->sort);
                add(*model, H::mkOp(H::Op::EQ,
                                    {H::mkIdent(name, value->sort), value}));
            }
        }

        // Step 0: the init values. A state with NO init is left unconstrained,
        // deliberately -- see the header. Adding `s = 0` would remove initial
        // states and report "safe" for an unsafe circuit.
        for (const long long id : states_) {
            const auto it = init_.find(id);
            if (it == init_.end()) { continue; }
            H::ExprPtr v = term(it->second, 0, diags);
            if (!v) { return nullptr; }
            if (node_sort_[id].kind == H::SortKind::ARRAY
                && v->sort.kind == H::SortKind::BITVEC) {
                const Line* initializer = lineOf(std::llabs(it->second));
                if (initializer == nullptr
                    || (initializer->op != "const" && initializer->op != "constd"
                        && initializer->op != "consth" && initializer->op != "zero"
                        && initializer->op != "one" && initializer->op != "ones")) {
                    diags.error(ErrorCode::E_TYPE,
                                "a bit-vector array initializer must be a constant");
                    return nullptr;
                }
                v = H::mkConstArray(node_sort_[id], v);
            }
            add(*model, H::mkOp(H::Op::EQ,
                                {H::mkIdent(stepName(names_[id], 0), node_sort_[id]), v}));
        }

        // Steps 0..k-1: only source-declared transition functions become
        // equations. CAV'18 defines a state without `next` as a primary input,
        // hence fresh/nondeterministic at each step; a frame equation would
        // remove legal traces.
        for (unsigned k = 0; k < depth_; ++k) {
            for (const long long id : states_) {
                const auto it = next_.find(id);
                if (it == next_.end()) { continue; }
                H::ExprPtr v = term(it->second, k, diags);
                if (!v) { return nullptr; }
                add(*model, H::mkOp(H::Op::EQ,
                                    {H::mkIdent(stepName(names_[id], k + 1),
                                                node_sort_[id]), v}));
            }
        }

        // A bad witness is a finite initialized path which contains a bad state
        // and satisfies every invariant constraint on that path (CAV'18). For
        // an at-most-k query, each candidate bad frame therefore carries only
        // its own constraint prefix. Globally constraining all k frames would
        // erase a valid shorter witness that cannot be extended under c.
        phase_ = "building the bounded property";
        H::ExprPtr any;
        H::ExprPtr constraint_prefix = H::mkBool(true);
        const std::vector<long long> bad_nodes = bads();
        for (unsigned k = 0; k <= depth_; ++k) {
            for (const Line& l : lines_) {
                if (l.op != "constraint" || l.args.empty()) { continue; }
                H::ExprPtr c = term(l.args[0], k, diags);
                if (!c) { return nullptr; }
                H::ExprPtr formula = asBool(c, l.lineno, diags);
                if (!formula) { return nullptr; }
                constraint_prefix = H::mkOp(
                    H::Op::AND, {constraint_prefix, formula});
            }
            for (const long long bad : bad_nodes) {
                H::ExprPtr b = term(bad, k, diags);
                if (!b) { return nullptr; }
                const Line* bad_line = lineOf(std::llabs(bad));
                H::ExprPtr t = asBool(b, bad_line ? bad_line->lineno : 0, diags);
                if (!t) { return nullptr; }
                H::ExprPtr witness = H::mkOp(
                    H::Op::AND, {constraint_prefix, t});
                any = any ? H::mkOp(H::Op::OR, {any, witness}) : witness;
            }
        }
        add(*model, any);

        // The record. This is what makes option C of the design note adequate:
        // the shape AND the bound are in the report, with no change to
        // ConstraintModel's contract.
        Uir::EncodingChoice ch;
        ch.site       = file_;
        ch.unified_op = "transition-system";
        ch.strategy   = "bmc-unrolling";
        Uir::Fidelity::Bound b;
        b.kind  = Uir::Fidelity::Bound::BMC_DEPTH;
        b.value = static_cast<int64_t>(depth_);
        b.site  = file_;
        ch.fidelity = Uir::Fidelity::underApprox(b);
        ch.rationale =
            "a BTOR2 file is a transition system, unrolled here to depth "
            + std::to_string(depth_)
            + "; SAT is a real trace to the bad state and comparable to the "
              "competition's answer, UNSAT means NO COUNTEREXAMPLE WITHIN "
            + std::to_string(depth_) + " STEPS and must not be reported as safe";
        report.addChoice(std::move(ch));
        return model;
    }

    std::vector<long long> bads() const {
        std::vector<long long> out;
        for (const Line& l : lines_) {
            if (l.op == "bad" && !l.args.empty()) { out.push_back(l.args[0]); }
        }
        return out;
    }

    void declare(H::ConstraintModel& m, const std::string& name, const H::Sort& s) {
        if (!declared_.insert(name).second) { return; }
        H::VarDecl d;
        d.name = name;
        d.sort = s;
        m.decls.push_back(std::move(d));
    }
    static void add(H::ConstraintModel& m, const H::ExprPtr& e) {
        H::Constraint c;
        c.formula = e;
        m.constraints.push_back(c);
    }
    /** Boolean/BV1 adapters need the same two immutable constants at every
     * gate and time frame. Keep only these two lazy owning pointers, not an
     * unbounded interning table. Source diagnostics are still checked before
     * adapters use the literals; returned HIR owns them after parser teardown. */
    H::ExprPtr oneBitLiteral(bool value) const {
        H::ExprPtr& literal = one_bit_literals_[value ? 1 : 0];
        if (!literal) { literal = H::mkBitVec(value ? "#b1" : "#b0", 1); }
        return literal;
    }

    /** A BTOR2 property is a 1-bit vector; an HIR constraint is a Bool. */
    H::ExprPtr asBool(const H::ExprPtr& e, int lineno, Uir::Diagnostics& diags) const {
        if (e->sort.kind == H::SortKind::BOOL) { return e; }
        if (e->sort.kind != H::SortKind::BITVEC || e->sort.width != 1) {
            diags.error(ErrorCode::E_TYPE,
                        "a Boolean BTOR2 operand must have bit-vector width 1",
                        at(lineno));
            return nullptr;
        }
        return H::mkOp(H::Op::EQ, {e, oneBitLiteral(true)});
    }

    const Line* lineOf(long long id) const {
        if (id <= 0) { return nullptr; }
        // read() proves strict increasing order. Most generated inputs have
        // dense IDs, but holes and very large IDs are equally legal: never
        // index or allocate from an unchecked source ID.
        if (static_cast<unsigned long long>(id) <= lines_.size()) {
            const Line& candidate = lines_[static_cast<std::size_t>(id - 1)];
            if (candidate.id == id) { return &candidate; }
        }
        const auto it = std::lower_bound(
            lines_.begin(), lines_.end(), id,
            [](const Line& line, long long wanted) { return line.id < wanted; });
        return it != lines_.end() && it->id == id ? &*it : nullptr;
    }

    bool validateAllTerms(const H::ConstraintModel& declarations,
                          Uir::Diagnostics& diags) {
        std::vector<H::LocatedExpr> terms;
        const auto isTerm = [](const Line& line) {
            return line.op != "sort" && line.op != "init" && line.op != "next"
                && line.op != "bad" && line.op != "constraint" && line.op != "fair"
                && line.op != "justice" && line.op != "output";
        };
        const auto isCheckedAlias = [](const Line& line) {
            // Positive references name an earlier source term whose expression
            // is already a batch root. Negative references create a fresh NOT
            // expression and must remain independently checked.
            return line.op == "uext" && line.args.size() == 3
                && line.args[1] > 0 && line.args[2] == 0;
        };
        std::size_t root_count = 0;
        for (const Line& line : lines_) {
            if (isTerm(line) && !isCheckedAlias(line)) { ++root_count; }
        }
        terms.reserve(root_count);
        for (const Line& l : lines_) {
            if (!isTerm(l)) { continue; }
            H::ExprPtr value = term(l.id, 0, diags);
            if (!value) { return false; }
            H::Sort expected;
            if (!sortOf(l.args[0], expected, l.lineno, diags)) { return false; }
            if (!H::sameSort(value->sort, expected)) {
                diags.error(ErrorCode::E_TYPE,
                            quotedOperator(l.op) + " declares result sort " + H::toString(expected)
                                + " but its operands produce " + H::toString(value->sort),
                            at(l.lineno));
                return false;
            }
            // Check the declared result sort of EVERY source ID above, even
            // unused aliases. Only the repeated expression-type traversal is
            // omitted; the earlier referent (or its non-alias ancestor) stays
            // in this same immutable batch and is checked by typeCheckTerms.
            if (isCheckedAlias(l) && value->sort.kind == H::SortKind::BITVEC) {
                continue;
            }
            // The batch owns one source path, not a copy per circuit gate.
            terms.push_back({std::move(value), {"", l.lineno, 0}});
        }
        // Validate unused source nodes too, but do not materialize a Boolean
        // equality and a constraint for every gate merely to check its type.
        return H::typeCheckTerms(declarations, terms, diags, file_);
    }

    /** The term for node @p id at step @p k. Negative ids are BTOR2's
     *  shorthand for the bitwise negation of the node. */
    H::ExprPtr term(long long id, unsigned k, Uir::Diagnostics& diags) {
        if (id < 0) {
            if (id == std::numeric_limits<long long>::min()) {
                diags.error(ErrorCode::E_PARSE, "a negated node id is out of range");
                return nullptr;
            }
            H::ExprPtr inner = term(-id, k, diags);
            if (!inner) { return nullptr; }
            return H::mkOp(H::Op::BV_NOT, {inner});
        }
        const auto memo_key = std::make_pair(id, k);
        if (k != 0) {
            const auto mi = memo_.find(memo_key);
            if (mi != memo_.end()) { return mi->second; }
        }

        const Line* l = lineOf(id);
        if (l == nullptr) {
            diags.error(ErrorCode::E_PARSE, "node " + std::to_string(id) + " is not defined");
            return nullptr;
        }
        if (k == 0 && l->frame_zero_term) { return l->frame_zero_term; }
        H::ExprPtr r = termOf(*l, k, diags);
        if (r) {
            if (k == 0) { l->frame_zero_term = r; }
            else { memo_[memo_key] = r; }
        }
        return r;
    }

    static std::string decimalMagnitudeBits(std::string digits) {
        const std::size_t first = digits.find_first_not_of('0');
        if (first == std::string::npos) { return "0"; }
        digits.erase(0, first);
        std::string reversed;
        while (digits != "0") {
            std::string quotient;
            unsigned carry = 0;
            for (const char c : digits) {
                const unsigned value = carry * 10 + static_cast<unsigned>(c - '0');
                if (!quotient.empty() || value / 2 != 0) {
                    quotient.push_back(static_cast<char>('0' + value / 2));
                }
                carry = value % 2;
            }
            reversed.push_back(carry == 0 ? '0' : '1');
            digits = quotient.empty() ? "0" : quotient;
        }
        return std::string(reversed.rbegin(), reversed.rend());
    }

    bool constantBits(const Line& l, unsigned width, std::string& out,
                      Uir::Diagnostics& diags) const {
        std::string bits_text;
        if (l.op == "const") {
            for (const char c : l.literalText()) {
                if (c != '0' && c != '1') {
                    diags.error(ErrorCode::E_PARSE,
                                "binary constant contains non-binary digit", at(l.lineno));
                    return false;
                }
            }
            if (l.literalText().size() != width) {
                diags.error(ErrorCode::E_PARSE,
                            "binary constant has " + std::to_string(l.literalText().size())
                                + " bits but its sort has width " + std::to_string(width),
                            at(l.lineno));
                return false;
            }
            bits_text = l.literalText();
        } else if (l.op == "consth") {
            for (const char c : l.literalText()) {
                unsigned value = 0;
                if (c >= '0' && c <= '9') { value = static_cast<unsigned>(c - '0'); }
                else if (c >= 'a' && c <= 'f') {
                    value = 10U + static_cast<unsigned>(c - 'a');
                } else if (c >= 'A' && c <= 'F') {
                    value = 10U + static_cast<unsigned>(c - 'A');
                } else {
                    diags.error(ErrorCode::E_PARSE,
                                "hexadecimal constant contains a non-hex digit", at(l.lineno));
                    return false;
                }
                for (int bit = 3; bit >= 0; --bit) {
                    bits_text.push_back(((value >> bit) & 1U) != 0 ? '1' : '0');
                }
            }
            const std::size_t first = bits_text.find('1');
            bits_text = first == std::string::npos ? "0" : bits_text.substr(first);
            if (bits_text.size() > width) {
                diags.error(ErrorCode::E_PARSE,
                            "hexadecimal constant does not fit bit-vector width "
                                + std::to_string(width), at(l.lineno));
                return false;
            }
            bits_text.insert(0, width - bits_text.size(), '0');
        } else {
            bool negative = false;
            std::string magnitude = l.literalText();
            if (!magnitude.empty() && magnitude[0] == '-') {
                negative = true;
                magnitude.erase(0, 1);
            }
            if (magnitude.empty()) {
                diags.error(ErrorCode::E_PARSE, "empty decimal constant", at(l.lineno));
                return false;
            }
            for (const char c : magnitude) {
                if (!std::isdigit(static_cast<unsigned char>(c))) {
                    diags.error(ErrorCode::E_PARSE,
                                "decimal constant contains a non-decimal digit", at(l.lineno));
                    return false;
                }
            }
            bits_text = decimalMagnitudeBits(magnitude);
            bool is_min = bits_text[0] == '1';
            for (std::size_t i = 1; is_min && i < bits_text.size(); ++i) {
                is_min = bits_text[i] == '0';
            }
            const bool fits = !negative ? bits_text.size() <= width
                : is_min ? bits_text.size() <= width : bits_text.size() + 1 <= width;
            if (!fits) {
                diags.error(ErrorCode::E_PARSE,
                            "decimal constant `" + l.literalText()
                                + "` does not fit bit-vector width " + std::to_string(width),
                            at(l.lineno));
                return false;
            }
            bits_text.insert(0, width - bits_text.size(), '0');
            if (negative) {
                for (char& c : bits_text) { c = c == '0' ? '1' : '0'; }
                for (std::size_t i = bits_text.size(); i > 0; --i) {
                    if (bits_text[i - 1] == '0') {
                        bits_text[i - 1] = '1';
                        break;
                    }
                    bits_text[i - 1] = '0';
                }
            }
        }
        out = "#b" + bits_text;
        return true;
    }

    static H::ExprPtr bitConstant(unsigned width, unsigned long long value) {
        std::string bits(width, '0');
        for (std::size_t i = 0; i < bits.size() && value != 0; ++i) {
            bits[bits.size() - 1 - i] = (value & 1ULL) != 0 ? '1' : '0';
            value >>= 1U;
        }
        return H::mkBitVec("#b" + bits, width);
    }

    bool sameBitVectors(const H::ExprPtr& a, const H::ExprPtr& b, const Line& l,
                        Uir::Diagnostics& diags) const {
        if (a->sort.kind != H::SortKind::BITVEC || b->sort.kind != H::SortKind::BITVEC
            || a->sort.width != b->sort.width) {
            diags.error(ErrorCode::E_TYPE,
                        quotedOperator(l.op) + " requires equally wide bit-vector operands",
                        at(l.lineno));
            return false;
        }
        return true;
    }

    H::ExprPtr reduction(std::string_view op, const H::ExprPtr& a, const Line& l,
                         Uir::Diagnostics& diags) const {
        if (a->sort.kind != H::SortKind::BITVEC || a->sort.width == 0) {
            diags.error(ErrorCode::E_TYPE,
                        quotedOperator(op) + " requires a non-empty bit-vector operand",
                        at(l.lineno));
            return nullptr;
        }
        if (op == "redand") {
            return fromBool(H::mkOp(H::Op::EQ,
                                    {a, H::mkBitVec("#b" + std::string(a->sort.width, '1'),
                                                    a->sort.width)}));
        }
        if (op == "redor") {
            return fromBool(H::mkOp(
                H::Op::NOT,
                {H::mkOp(H::Op::EQ,
                         {a, H::mkBitVec("#b" + std::string(a->sort.width, '0'),
                                         a->sort.width)})}));
        }
        H::ExprPtr parity = H::mkBvExtract(a, 0, 0);
        for (unsigned bit = 1; bit < a->sort.width; ++bit) {
            parity = H::mkOp(H::Op::BV_XOR,
                             {parity, H::mkBvExtract(a, bit, bit)});
        }
        return parity;
    }

    H::ExprPtr rotate(std::string_view op, const H::ExprPtr& a,
                      const H::ExprPtr& amount, const Line& l,
                      Uir::Diagnostics& diags) const {
        if (!sameBitVectors(a, amount, l, diags)) { return nullptr; }
        const H::ExprPtr width = bitConstant(a->sort.width, a->sort.width);
        const H::ExprPtr reduced = H::mkOp(H::Op::BV_UREM, {amount, width});
        const H::ExprPtr reverse = H::mkOp(H::Op::BV_SUB, {width, reduced});
        const H::Op first = op == "rol" ? H::Op::BV_SHL : H::Op::BV_LSHR;
        const H::Op second = op == "rol" ? H::Op::BV_LSHR : H::Op::BV_SHL;
        return H::mkOp(H::Op::BV_OR,
                       {H::mkOp(first, {a, reduced}), H::mkOp(second, {a, reverse})});
    }

    H::ExprPtr overflow(std::string_view op, const H::ExprPtr& a,
                        const H::ExprPtr& b, const Line& l,
                        Uir::Diagnostics& diags) const {
        if (!sameBitVectors(a, b, l, diags)) { return nullptr; }
        const unsigned width = a->sort.width;
        const H::ExprPtr zero = bitConstant(width, 0);
        const H::ExprPtr ones = H::mkBitVec("#b" + std::string(width, '1'), width);
        const H::ExprPtr minimum = H::mkBitVec(
            "#b1" + std::string(width - 1, '0'), width);
        const auto equal = [](const H::ExprPtr& x, const H::ExprPtr& y) {
            return H::mkOp(H::Op::EQ, {x, y});
        };
        const auto different = [&](const H::ExprPtr& x, const H::ExprPtr& y) {
            return H::mkOp(H::Op::NOT, {equal(x, y)});
        };
        const auto sign = [&](const H::ExprPtr& x) {
            return H::mkBvExtract(x, width - 1, width - 1);
        };
        H::ExprPtr result;
        if (op == "uaddo") {
            result = H::mkOp(H::Op::BV_ULT, {H::mkOp(H::Op::BV_ADD, {a, b}), a});
        } else if (op == "usubo") {
            result = H::mkOp(H::Op::BV_ULT, {a, b});
        } else if (op == "saddo") {
            const H::ExprPtr sum = H::mkOp(H::Op::BV_ADD, {a, b});
            result = H::mkOp(H::Op::AND,
                             {equal(sign(a), sign(b)), different(sign(sum), sign(a))});
        } else if (op == "ssubo") {
            const H::ExprPtr difference = H::mkOp(H::Op::BV_SUB, {a, b});
            result = H::mkOp(H::Op::AND,
                             {different(sign(a), sign(b)),
                              different(sign(difference), sign(a))});
        } else if (op == "sdivo") {
            result = H::mkOp(H::Op::AND, {equal(a, minimum), equal(b, ones)});
        } else {
            const bool signed_mul = op == "smulo";
            const H::ExprPtr product = H::mkOp(H::Op::BV_MUL, {a, b});
            const H::ExprPtr nonzero = different(b, zero);
            const H::ExprPtr quotient = H::mkOp(
                signed_mul ? H::Op::BV_SDIV : H::Op::BV_UDIV, {product, b});
            result = H::mkOp(H::Op::AND, {nonzero, different(quotient, a)});
            if (signed_mul) {
                const H::ExprPtr exceptional =
                    H::mkOp(H::Op::AND, {equal(a, minimum), equal(b, ones)});
                result = H::mkOp(H::Op::OR, {result, exceptional});
            }
        }
        return fromBool(result);
    }

    H::ExprPtr termOf(const Line& l, unsigned k, Uir::Diagnostics& diags) {
        if (l.op == "state" || l.op == "input") {
            return H::mkIdent(stepName(names_.at(l.id), k), node_sort_.at(l.id));
        }
        H::Sort s;
        if (l.args.empty() || !sortOf(l.args[0], s, l.lineno, diags)) {
            diags.error(ErrorCode::E_PARSE, quotedOperator(l.op) + " needs a sort",
                        at(l.lineno));
            return nullptr;
        }
        const auto arg = [&](std::size_t i) -> H::ExprPtr {
            if (l.args.size() <= i + 1) {
                diags.error(ErrorCode::E_PARSE,
                            quotedOperator(l.op) + " needs " + std::to_string(i + 1)
                                + " argument(s)",
                            at(l.lineno));
                return nullptr;
            }
            return term(l.args[i + 1], k, diags);
        };

        // Constants.
        if (l.op == "zero" || l.op == "one" || l.op == "ones") {
            if (s.kind != H::SortKind::BITVEC) {
                diags.error(ErrorCode::E_TYPE,
                            quotedOperator(l.op) + " requires a bit-vector sort", at(l.lineno));
                return nullptr;
            }
        }
        if (l.op == "zero")  { return H::mkBitVec("#b" + std::string(s.width, '0'), s.width); }
        if (l.op == "one") {
            std::string one(s.width, '0');
            one.back() = '1';
            return H::mkBitVec("#b" + one, s.width);
        }
        if (l.op == "ones")  { return H::mkBitVec(std::string("#b") + std::string(s.width, '1'), s.width); }
        if (l.op == "const" || l.op == "constd" || l.op == "consth") {
            if (s.kind != H::SortKind::BITVEC) {
                diags.error(ErrorCode::E_TYPE,
                            quotedOperator(l.op) + " requires a bit-vector sort", at(l.lineno));
                return nullptr;
            }
            std::string literal;
            if (!constantBits(l, s.width, literal, diags)) { return nullptr; }
            return H::mkBitVec(literal, s.width);
        }
        if (l.op == "inc" || l.op == "dec") {
            H::ExprPtr a = arg(0);
            if (!a) { return nullptr; }
            if (a->sort.kind != H::SortKind::BITVEC) {
                diags.error(ErrorCode::E_TYPE,
                            quotedOperator(l.op) + " requires a bit-vector operand", at(l.lineno));
                return nullptr;
            }
            return H::mkOp(l.op == "inc" ? H::Op::BV_ADD : H::Op::BV_SUB,
                           {a, bitConstant(a->sort.width, 1)});
        }
        if (l.op == "redand" || l.op == "redor" || l.op == "redxor") {
            H::ExprPtr a = arg(0);
            return a ? reduction(l.op, a, l, diags) : nullptr;
        }
        if (l.op == "rol" || l.op == "ror") {
            H::ExprPtr a = arg(0), amount = arg(1);
            return a && amount ? rotate(l.op, a, amount, l, diags) : nullptr;
        }
        if (l.op == "uaddo" || l.op == "saddo" || l.op == "usubo"
            || l.op == "ssubo" || l.op == "umulo" || l.op == "smulo"
            || l.op == "sdivo") {
            H::ExprPtr a = arg(0), b = arg(1);
            return a && b ? overflow(l.op, a, b, l, diags) : nullptr;
        }

        static const std::unordered_map<std::string_view, H::Op> kBin = {
            {"add", H::Op::BV_ADD},   {"sub", H::Op::BV_SUB},   {"mul", H::Op::BV_MUL},
            {"udiv", H::Op::BV_UDIV}, {"sdiv", H::Op::BV_SDIV},
            {"urem", H::Op::BV_UREM}, {"srem", H::Op::BV_SREM}, {"smod", H::Op::BV_SMOD},
            {"and", H::Op::BV_AND},   {"or", H::Op::BV_OR},     {"xor", H::Op::BV_XOR},
            {"nand", H::Op::BV_NAND}, {"nor", H::Op::BV_NOR},   {"xnor", H::Op::BV_XNOR},
            {"sll", H::Op::BV_SHL},   {"srl", H::Op::BV_LSHR},  {"sra", H::Op::BV_ASHR},
            {"concat", H::Op::BV_CONCAT},
        };
        const auto bi = kBin.find(l.op);
        if (bi != kBin.end()) {
            H::ExprPtr a = arg(0), b = arg(1);
            if (!a || !b) { return nullptr; }
            return H::mkOp(bi->second, {a, b});
        }

        // The comparisons yield one bit, not a Bool, so each is wrapped back.
        static const std::unordered_map<std::string_view, H::Op> kCmp = {
            {"eq", H::Op::EQ},       {"ult", H::Op::BV_ULT},  {"ulte", H::Op::BV_ULE},
            {"ugt", H::Op::BV_UGT},  {"ugte", H::Op::BV_UGE}, {"slt", H::Op::BV_SLT},
            {"slte", H::Op::BV_SLE}, {"sgt", H::Op::BV_SGT},  {"sgte", H::Op::BV_SGE},
        };
        const auto ci = kCmp.find(l.op);
        if (ci != kCmp.end()) {
            H::ExprPtr a = arg(0), b = arg(1);
            if (!a || !b) { return nullptr; }
            return fromBool(H::mkOp(ci->second, {a, b}));
        }
        if (l.op == "neq") {
            H::ExprPtr a = arg(0), b = arg(1);
            if (!a || !b) { return nullptr; }
            return fromBool(H::mkOp(H::Op::NOT, {H::mkOp(H::Op::EQ, {a, b})}));
        }
        // BTOR2 has `implies` and `iff` as one-bit operators. Found by running
        // the official btor2tools examples: noninitstate.btor2 uses `implies`
        // to say a state's constraint holds only while `initially` does.
        if (l.op == "implies" || l.op == "iff") {
            H::ExprPtr a = arg(0), b2 = arg(1);
            if (!a || !b2) { return nullptr; }
            H::ExprPtr ba = asBool(a, l.lineno, diags);
            H::ExprPtr bb = asBool(b2, l.lineno, diags);
            if (!ba || !bb) { return nullptr; }
            H::ExprPtr r = l.op == "implies"
                ? H::mkOp(H::Op::IMPLIES, {ba, bb})
                : H::mkOp(H::Op::EQ, {ba, bb});
            return fromBool(r);
        }
        if (l.op == "not" || l.op == "neg") {
            H::ExprPtr a = arg(0);
            if (!a) { return nullptr; }
            return H::mkOp(l.op == "not" ? H::Op::BV_NOT : H::Op::BV_NEG, {a});
        }
        if (l.op == "ite") {
            H::ExprPtr c = arg(0), t = arg(1), e = arg(2);
            if (!c || !t || !e) { return nullptr; }
            H::ExprPtr condition = asBool(c, l.lineno, diags);
            if (!condition) { return nullptr; }
            return H::mkOp(H::Op::ITE, {condition, t, e});
        }
        if (l.op == "read") {
            H::ExprPtr a = arg(0), i = arg(1);
            if (!a || !i) { return nullptr; }
            return H::mkOp(H::Op::SELECT, {a, i});
        }
        if (l.op == "write") {
            H::ExprPtr a = arg(0), i = arg(1), v = arg(2);
            if (!a || !i || !v) { return nullptr; }
            return H::mkOp(H::Op::STORE, {a, i, v});
        }
        // The indexed operators. Their width comes from the line's trailing
        // numbers rather than from a sort, so each needs the HIR's own builder
        // -- mkOp refuses them, because a width that came from the wrong place
        // is a different circuit that still type-checks.
        //
        // `slice <sort> <arg> <upper> <lower>` is SMT-LIB's (_ extract hi lo),
        // with the bounds INCLUSIVE and given high-first. Reading them the
        // other way round silently extracts a different field.
        if (l.op == "slice") {
            H::ExprPtr a = arg(0);
            if (!a) { return nullptr; }
            if (l.args.size() < 4) {
                diags.error(ErrorCode::E_PARSE,
                            "'slice' needs a sort, an argument, an upper and a lower bit",
                            at(l.lineno));
                return nullptr;
            }
            const long long hi = l.args[2], lo = l.args[3];
            if (hi < lo || lo < 0) {
                diags.error(ErrorCode::E_PARSE,
                            "'slice' bounds are given high-first and inclusive; "
                            + std::to_string(hi) + " is below " + std::to_string(lo),
                            at(l.lineno));
                return nullptr;
            }
            // The source indices are signed 64-bit integers; narrowing them
            // before validation could turn an out-of-range slice into a
            // different, well-typed extraction (for example 2^32 becomes 0).
            if (static_cast<unsigned long long>(hi) > std::numeric_limits<unsigned>::max()) {
                diags.error(ErrorCode::E_PARSE,
                            "'slice' index exceeds the machine bit-vector width",
                            at(l.lineno));
                return nullptr;
            }
            return H::mkBvExtract(a, static_cast<unsigned>(hi), static_cast<unsigned>(lo));
        }
        if (l.op == "uext" || l.op == "sext") {
            H::ExprPtr a = arg(0);
            if (!a) { return nullptr; }
            if (l.args.size() < 3) {
                diags.error(ErrorCode::E_PARSE,
                            quotedOperator(l.op) + " needs a sort, an argument and a width",
                            at(l.lineno));
                return nullptr;
            }
            const long long by = l.args[2];
            if (by < 0) {
                diags.error(ErrorCode::E_PARSE,
                            quotedOperator(l.op) + " cannot extend by a negative width",
                            at(l.lineno));
                return nullptr;
            }
            const auto maximum_width = std::numeric_limits<unsigned>::max();
            if (static_cast<unsigned long long>(by) > maximum_width) {
                diags.error(ErrorCode::E_PARSE,
                            quotedOperator(l.op) + " extension amount exceeds the machine bit-vector width",
                            at(l.lineno));
                return nullptr;
            }
            if (a->sort.kind == H::SortKind::BITVEC
                && static_cast<unsigned long long>(by) > maximum_width - a->sort.width) {
                diags.error(ErrorCode::E_PARSE,
                            quotedOperator(l.op) + " extended result exceeds the machine bit-vector width",
                            at(l.lineno));
                return nullptr;
            }
            // A zero extension is the same bit-vector value, not another
            // HIR node. Keep this after reference/amount checks, and only for
            // bit-vectors: malformed array operands retain their old checked
            // path. validateAllTerms still compares every source ID's declared
            // result sort (including unused aliases) before the BMC unrolling.
            if (l.op == "uext" && by == 0 && a->sort.kind == H::SortKind::BITVEC) {
                return a;
            }
            // uext zero-extends and sext sign-extends: the same instruction
            // shape with different meaning on a negative value, and the file
            // says which.
            return H::mkBvExtend(l.op == "uext" ? H::Op::BV_ZERO_EXTEND
                                                : H::Op::BV_SIGN_EXTEND,
                                 a, static_cast<unsigned>(by));
        }
        if (l.op == "output" || l.op == "bad" || l.op == "constraint") {
            return arg(0);
        }
        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    quotedOperator(l.op) + " is not implemented; skipping it would drop part of "
                    "the circuit and change what the unrolling says",
                    at(l.lineno));
        return nullptr;
    }

    /** A Bool back to the one-bit vector BTOR2 works in. */
    H::ExprPtr fromBool(const H::ExprPtr& e) const {
        return H::mkOp(H::Op::ITE, {e, oneBitLiteral(true), oneBitLiteral(false)});
    }
    struct PairHash {
        std::size_t operator()(const std::pair<long long, unsigned>& p) const {
            return std::hash<long long>()(p.first) ^ (std::hash<unsigned>()(p.second) << 1);
        }
    };

    std::istream& input_;
    std::string file_;
    const char* phase_ = "initializing the parser";
    unsigned    depth_;
    std::deque<std::string> text_storage_;
    std::deque<std::vector<long long>> justice_arguments_;
    // Stable blocks avoid temporarily retaining both old and grown arrays of
    // source records while reading a multimillion-node circuit.
    std::deque<Line> lines_;
    std::unordered_map<long long, SortDef> sorts_;
    std::unordered_map<long long, H::Sort> node_sort_;
    std::unordered_map<long long, std::string> names_;
    std::vector<long long> states_, inputs_, outputs_;
    std::unordered_map<long long, long long> init_, next_;
    std::unordered_map<std::pair<long long, unsigned>, H::ExprPtr, PairHash> memo_;
    mutable H::ExprPtr one_bit_literals_[2];
    std::unordered_set<std::string> declared_;
    std::unordered_set<std::string> used_base_names_;
};

class Btor2Language : public Language {
public:
    Btor2Language() {
        coverage_.total = 10;
        coverage_.supported = 9;
        coverage_.missing = {
            "liveness (justice and fair)",
        };
    }

    std::string id() const override { return "btor2"; }
    std::string displayName() const override { return "BTOR2 (bounded model checking)"; }
    std::string version() const override { return "2"; }
    std::vector<std::string> extensions() const override { return {".btor2", ".btor"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) override {
        ParseOutcome out;
        SourceBuffer inline_buffer(unit.inline_source);
        std::istream inline_input(&inline_buffer);
        std::ifstream file_input;
        std::istream* input = &inline_input;
        if (unit.inline_source.empty()) {
            std::error_code ec;
            if (std::filesystem::is_directory(unit.main_path, ec)) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "'" + unit.main_path + "' is a directory");
                return out;
            }
            file_input.open(unit.main_path, std::ios::binary);
            if (!file_input) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "cannot open '" + unit.main_path + "'");
                return out;
            }
            input = &file_input;
        }

        // No default. §4.3 names silent defaults as this format's hazard, and a
        // depth chosen here would be one: every instance would be measured at a
        // bound nobody recorded choosing, and the bound is what the fidelity
        // entry is about.
        const auto it = opts.options.find("bmc_depth");
        if (it == opts.options.end()) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "no unrolling depth: pass bmc_depth=<k>. There is "
                                  "deliberately no default, because the depth is the "
                                  "bound the translation's fidelity is stated against "
                                  "and one chosen here would be a bound nobody recorded "
                                  "choosing");
            return out;
        }
        char* end = nullptr;
        errno = 0;
        const long long k = std::strtoll(it->second.c_str(), &end, 10);
        if (errno == ERANGE || end == it->second.c_str() || *end != '\0') {
            out.diagnostics.error(ErrorCode::E_PARSE,
                                  "bmc_depth must be a base-10 integer");
            return out;
        }
        if (k < 0) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "bmc_depth must not be negative");
            return out;
        }
        if (static_cast<unsigned long long>(k)
            >= static_cast<unsigned long long>(std::numeric_limits<unsigned>::max())) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "bmc_depth is too large for the unroller");
            return out;
        }

        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            {
                Btor2Parser p(*input, name, static_cast<unsigned>(k));
                out.model = p.parse(out.diagnostics, out.report);
            }
            // The owning HIR is independent of the reader. Release its source
            // records and term cache before allocating the semantic contract.
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "btor2", out.report.fidelity()));
            }
        } catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                                  "BTOR2 exhausted memory while building its semantic contract");
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("btor2 frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkBtor2Language() { return std::make_shared<Btor2Language>(); }

} // namespace SOMTParser::Lang
