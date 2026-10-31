// Exact full WCNF source/SMT correspondence. Hashes index complete keys only;
// acceptance compares full canonical clause vectors and exact decimal weights.
#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {
using Integer = std::int64_t;
using Clause = std::vector<Integer>;
void need(bool value, std::string_view message) {
    if (!value) throw std::runtime_error(std::string(message));
}
bool space(char c) { return c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\v' || c == '\f'; }
std::string natural(std::string_view value, bool positive = false) {
    need(!value.empty(), "empty unsigned decimal");
    for (unsigned char c : value) need(c >= '0' && c <= '9', "invalid unsigned decimal");
    auto first = value.find_first_not_of('0');
    std::string result = first == value.npos ? "0" : std::string(value.substr(first));
    need(!positive || result != "0", "expected a positive decimal");
    return result;
}
Integer index(std::string_view value, bool positive = false) {
    need(!value.empty(), "empty variable index");
    std::uint64_t number = 0;
    for (unsigned char c : value) {
        need(c >= '0' && c <= '9', "invalid variable index");
        unsigned digit = c - '0';
        need(number <= (std::uint64_t(std::numeric_limits<Integer>::max()) - digit) / 10,
             "variable index exceeds signed 64-bit range");
        number = number * 10 + digit;
    }
    need(!positive || number > 0, "expected positive variable index");
    return static_cast<Integer>(number);
}
bool canonical(Clause& values) {
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
    for (Integer value : values) {
        if (value >= 0) break;
        if (std::binary_search(values.begin(), values.end(), -value)) return false;
    }
    return true;
}
struct ClauseHash {
    std::size_t operator()(const Clause& values) const noexcept {
        std::size_t hash = values.size();
        for (Integer value : values) {
            std::size_t x = std::hash<Integer>{}(value);
            hash ^= x + std::size_t(0x9e3779b97f4a7c15ULL) + (hash << 6) + (hash >> 2);
        }
        return hash;
    }
};
struct SoftKey {
    Clause clause;
    std::string weight;
    bool operator==(const SoftKey& other) const { return clause == other.clause && weight == other.weight; }
};
struct SoftHash {
    std::size_t operator()(const SoftKey& value) const noexcept {
        return ClauseHash{}(value.clause) ^ (std::hash<std::string>{}(value.weight) << 1);
    }
};
struct Count { std::uint64_t source = 0, target = 0; };
void increment(std::uint64_t& n) {
    need(n < std::numeric_limits<std::uint64_t>::max(), "occurrence count overflow");
    ++n;
}
struct Relation {
    std::unordered_map<Clause, bool, ClauseHash> hard;
    std::unordered_map<SoftKey, Count, SoftHash> soft;
    Integer variables = -1, largest = 0, declaredClauses = -1;
    std::uint64_t sourceClauses = 0, sourceHard = 0, sourceSoft = 0, assertions = 0;
    std::uint64_t hardSeen = 0, softSeen = 0, softNontrivial = 0;
};
std::vector<std::string_view> words(const std::string& line) {
    std::vector<std::string_view> result;
    std::size_t position = 0;
    while (position < line.size()) {
        while (position < line.size() && space(line[position])) ++position;
        auto begin = position;
        while (position < line.size() && !space(line[position])) ++position;
        if (position != begin) result.emplace_back(line.data() + begin, position - begin);
    }
    return result;
}
void source(std::istream& input, Relation& relation) {
    bool unweighted = false;
    std::string top, line;
    while (std::getline(input, line)) {
        auto tokens = words(line);
        if (tokens.empty() || tokens.front().front() == 'c') continue;
        if (tokens.front() == "p") {
            need(relation.variables < 0 && relation.sourceClauses == 0, "misplaced source header");
            need((tokens.size() == 4 || tokens.size() == 5) &&
                 (tokens[1] == "cnf" || tokens[1] == "wcnf"), "invalid source header");
            unweighted = tokens[1] == "cnf";
            need(!unweighted || tokens.size() == 4, "CNF source has a top weight");
            relation.variables = index(tokens[2]);
            relation.declaredClauses = index(tokens[3]);
            if (tokens.size() == 5) top = natural(tokens[4], true);
            continue;
        }
        bool hard = tokens.front() == "h";
        std::size_t first = 1;
        std::string weight;
        if (!hard) {
            if (unweighted) { weight = "1"; first = 0; }
            else weight = natural(tokens.front(), true);
            hard = !top.empty() && (weight.size() > top.size() || (weight.size() == top.size() && weight >= top));
        }
        need(tokens.size() > first && tokens.back() == "0", "source clause lacks final zero");
        Clause values;
        for (std::size_t i = first; i + 1 < tokens.size(); ++i) {
            auto token = tokens[i];
            bool negative = token.front() == '-';
            Integer variable = index(negative ? token.substr(1) : token, true);
            relation.largest = std::max(relation.largest, variable);
            values.push_back(negative ? -variable : variable);
        }
        increment(relation.sourceClauses);
        increment(hard ? relation.sourceHard : relation.sourceSoft);
        if (!canonical(values)) continue; // A tautology is true; its violated weight is zero.
        if (hard) relation.hard.emplace(std::move(values), false);
        else {
            increment(relation.soft[SoftKey{std::move(values), std::move(weight)}].source);
            increment(relation.softNontrivial);
        }
    }
    need(input.eof() && !input.bad(), "source I/O error");
    if (relation.variables < 0) {
        need(relation.sourceClauses > 0, "empty headerless source");
        relation.variables = relation.largest;
    } else {
        need(relation.largest <= relation.variables, "source variable outside header");
        need(relation.sourceClauses == std::uint64_t(relation.declaredClauses), "source clause count mismatch");
    }
}
class Tokens {
    std::istream& input_;
    std::array<char, 65536> buffer_{};
    std::size_t at_ = 0, size_ = 0;
    int held_ = -2;
    std::string peeked_;
    bool hasPeek_ = false;
    int get() {
        if (held_ != -2) { int c = held_; held_ = -2; return c; }
        if (at_ == size_) {
            input_.read(buffer_.data(), buffer_.size());
            size_ = static_cast<std::size_t>(input_.gcount()); at_ = 0;
            if (!size_) { need(input_.eof() && !input_.bad(), "target I/O error"); return -1; }
        }
        unsigned char c = buffer_[at_++];
        need(c != 0, "NUL in target");
        return c;
    }
    std::string next() {
        int c;
        do {
            c = get();
            if (c == ';') { while (c != -1 && c != '\n' && c != '\r') c = get(); }
        } while (c != -1 && space(static_cast<char>(c)));
        if (c == -1) return {};
        if (c == '(' || c == ')') return std::string(1, static_cast<char>(c));
        need(c != '"' && c != '|', "quoted target syntax outside checked grammar");
        std::string token(1, static_cast<char>(c));
        while ((c = get()) != -1 && !space(static_cast<char>(c)) && c != '(' && c != ')' && c != ';') {
            need(c != '"' && c != '|', "quoted target syntax outside checked grammar");
            token.push_back(static_cast<char>(c));
        }
        held_ = c;
        return token;
    }
public:
    explicit Tokens(std::istream& input) : input_(input) {}
    std::string take() {
        if (!hasPeek_) return next();
        hasPeek_ = false; return std::move(peeked_);
    }
    const std::string& peek() { if (!hasPeek_) { peeked_ = next(); hasPeek_ = true; } return peeked_; }
    void expect(const char* value) {
        if (take() != value) throw std::runtime_error(std::string("expected target token: ") + value);
    }
};
class Target {
    Tokens tokens_;
    Relation& relation_;
    Integer declared_ = 0;
    Integer variable(const std::string& token) {
        need(token.size() > 1 && token[0] == 'x' && token[1] != '0', "invalid canonical target variable");
        Integer value = index(std::string_view(token).substr(1), true);
        need(value <= declared_, "undeclared target variable");
        return value;
    }
    Integer literal() {
        auto token = tokens_.take();
        if (token != "(") return variable(token);
        tokens_.expect("not");
        auto value = -variable(tokens_.take());
        tokens_.expect(")");
        return value;
    }
    // Iterative OR traversal accepts arbitrary nesting without a C++ stack bound.
    bool clauseRaw(Clause& values) {
        std::size_t depth = 0;
        bool tautology = false;
        do {
            auto token = tokens_.take();
            if (token == "(") {
                auto op = tokens_.take();
                if (op == "or") {
                    need(tokens_.peek() != ")", "zero-argument or"); ++depth; continue;
                }
                need(op == "not", "unsupported clause operator");
                values.push_back(-variable(tokens_.take())); tokens_.expect(")");
            } else if (token == "true") tautology = true;
            else if (token != "false") values.push_back(variable(token));
            while (depth && tokens_.peek() == ")") { tokens_.take(); --depth; }
        } while (depth);
        return !tautology;
    }
    bool clause(Clause& values) {
        bool nontrivial = clauseRaw(values);
        return canonical(values) && nontrivial;
    }
    void seenHard(Clause values) {
        if (!canonical(values)) return;
        auto found = relation_.hard.find(values);
        need(found != relation_.hard.end(), "extra or changed target hard clause");
        if (!found->second) { found->second = true; increment(relation_.hardSeen); }
    }
    Integer indicator() {
        if (tokens_.peek() == "0") { tokens_.take(); return 0; }
        tokens_.expect("("); tokens_.expect("ite");
        Integer result = literal();
        tokens_.expect("1"); tokens_.expect("0"); tokens_.expect(")");
        return result;
    }
    void amo() {
        // Caller consumed "(<=". Parse either one indicator or an additive list.
        std::vector<Integer> indicators;
        if (tokens_.peek() == "0") tokens_.take();
        else {
            tokens_.expect("(");
            auto op = tokens_.take();
            if (op == "+") {
                need(tokens_.peek() != ")", "empty AMO sum");
                while (tokens_.peek() != ")") {
                    Integer value = indicator();
                    if (value) indicators.push_back(value);
                }
                tokens_.take();
            } else {
                need(op == "ite", "unsupported AMO arithmetic");
                indicators.push_back(literal());
                tokens_.expect("1"); tokens_.expect("0"); tokens_.expect(")");
            }
        }
        tokens_.expect("1"); tokens_.expect(")");
        for (std::size_t i = 0; i < indicators.size(); ++i)
            for (std::size_t j = i + 1; j < indicators.size(); ++j)
                seenHard(Clause{-indicators[i], -indicators[j]});
    }
    void hard() {
        // Hard conjunctions are streamed, not retained as one giant syntax tree.
        std::size_t depth = 0;
        do {
            if (tokens_.peek() == "(") {
                tokens_.take();
                auto op = tokens_.take();
                if (op == "and") {
                    need(tokens_.peek() != ")", "zero-argument and"); ++depth; continue;
                }
                if (op == "<=") amo();
                else if (op == "not") {
                    seenHard(Clause{-variable(tokens_.take())}); tokens_.expect(")");
                } else {
                    need(op == "or", "unsupported hard relation");
                    need(tokens_.peek() != ")", "zero-argument or");
                    Clause values; bool nontrivial = true;
                    while (tokens_.peek() != ")") if (!clauseRaw(values)) nontrivial = false;
                    tokens_.take();
                    if (nontrivial) seenHard(std::move(values));
                }
            } else {
                Clause values;
                if (clause(values)) seenHard(std::move(values));
            }
            while (depth && tokens_.peek() == ")") { tokens_.take(); --depth; }
        } while (depth);
    }
public:
    Target(std::istream& input, Relation& relation) : tokens_(input), relation_(relation) {}
    void run() {
        enum Phase { Metadata, Declarations, Assertions, Queries } phase = Metadata;
        bool logic = false, queried = false, exited = false;
        while (!tokens_.peek().empty()) {
            need(!exited, "content after target exit"); tokens_.expect("(");
            auto command = tokens_.take();
            if (command == "set-logic") {
                need(phase == Metadata && !logic, "duplicate or late logic");
                tokens_.expect("ALL"); logic = true;
            } else if (command == "declare-const" || command == "declare-fun") {
                need(phase <= Declarations, "late target declaration"); phase = Declarations;
                need(declared_ < std::numeric_limits<Integer>::max(), "declaration count overflow");
                ++declared_;
                need(variable(tokens_.take()) == declared_, "nonconsecutive target declarations");
                if (command == "declare-fun") { tokens_.expect("("); tokens_.expect(")"); }
                tokens_.expect("Bool");
            } else if (command == "assert" || command == "assert-soft") {
                need(phase != Queries, "assertion after query"); phase = Assertions;
                increment(relation_.assertions);
                if (command == "assert") hard();
                else {
                    Clause values; bool nontrivial = clause(values);
                    tokens_.expect(":weight"); auto weight = natural(tokens_.take(), true);
                    if (nontrivial) {
                        auto found = relation_.soft.find(SoftKey{std::move(values), std::move(weight)});
                        need(found != relation_.soft.end(), "extra or changed target soft clause/weight");
                        increment(found->second.target); increment(relation_.softSeen);
                        need(found->second.target <= found->second.source, "extra soft clause occurrence");
                    }
                }
            } else if (command == "check-sat" || command == "exit") {
                phase = Queries;
                if (command == "check-sat") { need(!queried, "duplicate query"); queried = true; }
                else exited = true;
            } else throw std::runtime_error("unsupported target command: " + command);
            tokens_.expect(")");
        }
        need(declared_ == relation_.variables, "source/target variable domains differ");
        need(relation_.hardSeen == relation_.hard.size(), "missing source hard clause");
        // Every per-key target count is bounded above by its source count.
        // Equality of their totals therefore establishes equality for every key.
        need(relation_.softSeen == relation_.softNontrivial, "missing source soft occurrence");
    }
};
std::string jsonString(const std::string& value) {
    std::string out = "\"";
    for (unsigned char c : value) {
        if (c == '"' || c == '\\') { out += '\\'; out += static_cast<char>(c); }
        else if (c < 32) out += "?";
        else out += static_cast<char>(c);
    }
    return out + '"';
}
} // namespace

int main(int argc, char** argv) {
    std::ios::sync_with_stdio(false);
    try {
        need(argc == 3, "usage: somt-wcnf-certificate SOURCE_PLAIN TARGET_PLAIN (pipes allowed)");
        std::ifstream sourceFile(argv[1], std::ios::binary), targetFile(argv[2], std::ios::binary);
        need(bool(sourceFile) && bool(targetFile), "cannot open complete input streams");
        Relation relation;
        source(sourceFile, relation);
        Target(targetFile, relation).run();
        std::cout << "{\"status\":\"verified\",\"feasibility_equivalent\":true,"
                  << "\"pointwise_violation_cost_equal\":true,\"complete_source\":true,\"complete_target\":true,"
                  << "\"variables\":" << relation.variables << ",\"source_clauses\":" << relation.sourceClauses
                  << ",\"source_hard\":" << relation.sourceHard << ",\"source_soft\":" << relation.sourceSoft
                  << ",\"unique_hard_clauses\":" << relation.hard.size()
                  << ",\"soft_clause_occurrences\":" << relation.softNontrivial
                  << ",\"target_assertions\":" << relation.assertions
                  << ",\"solver_queries\":0,\"method\":\"complete exact canonical hard-set and weighted-soft-multiset correspondence; full-key equality, exact AMO expansion\"}\n";
        return 0;
    } catch (const std::exception& error) {
        std::cout << "{\"status\":\"unverified\",\"error\":" << jsonString(error.what()) << "}\n";
        return 1;
    }
}
