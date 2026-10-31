// Whole-module typechecking bridge, not a feasibility or objective certificate.
// All hard terms and every token of each soft Boolean term are retained. Soft
// terms are let-bound in tautologies for a parser without assert-soft support.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <string_view>

namespace {
void require(bool value, std::string_view message) {
    if (!value) throw std::runtime_error(std::string(message));
}
bool space(int c) { return c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\v' || c == '\f'; }
class Tokens {
    std::istream& input_;
    std::array<char, 65536> buffer_{};
    std::size_t at_ = 0, size_ = 0;
    int held_ = -2;
    int get() {
        if (held_ != -2) { int c = held_; held_ = -2; return c; }
        if (at_ == size_) {
            input_.read(buffer_.data(), buffer_.size());
            size_ = static_cast<std::size_t>(input_.gcount()); at_ = 0;
            if (!size_) { require(input_.eof() && !input_.bad(), "input I/O error"); return -1; }
        }
        unsigned char c = buffer_[at_++];
        require(c != 0, "NUL in original input");
        return c;
    }
public:
    explicit Tokens(std::istream& input) : input_(input) {}
    std::string take() {
        int c;
        do {
            c = get();
            if (c == ';') while (c != -1 && c != '\n' && c != '\r') c = get();
        } while (c != -1 && space(c));
        if (c == -1) return {};
        if (c == '(' || c == ')') return std::string(1, static_cast<char>(c));
        std::string token(1, static_cast<char>(c));
        if (c == '|') {
            while ((c = get()) != -1) {
                require(c != '\\', "backslash in quoted symbol");
                token.push_back(static_cast<char>(c));
                if (c == '|') return token;
            }
            throw std::runtime_error("unterminated quoted symbol");
        }
        if (c == '"') {
            while ((c = get()) != -1) {
                token.push_back(static_cast<char>(c));
                if (c == '"') {
                    c = get();
                    if (c == '"') token.push_back('"');
                    else { held_ = c; return token; }
                }
            }
            throw std::runtime_error("unterminated string");
        }
        while ((c = get()) != -1 && !space(c) && c != '(' && c != ')' && c != ';' && c != '"' && c != '|') {
            token.push_back(static_cast<char>(c));
        }
        held_ = c;
        return token;
    }
    void expect(std::string_view wanted) { require(take() == wanted, "unexpected command token/arity"); }
};
void emitToken(const std::string& token) {
    require(!token.empty(), "unexpected EOF in term");
    std::cout.write(token.data(), static_cast<std::streamsize>(token.size()));
    std::cout.put(' ');
}
void term(Tokens& tokens) {
    auto token = tokens.take();
    require(!token.empty() && token != ")", "missing term");
    std::uint64_t depth = token == "(";
    emitToken(token);
    while (depth) {
        token = tokens.take();
        require(!token.empty(), "unterminated term");
        if (token == "(") {
            require(depth < std::numeric_limits<std::uint64_t>::max(), "term depth overflow");
            ++depth;
        } else if (token == ")") --depth;
        emitToken(token);
    }
}
void weight(const std::string& value) {
    require(!value.empty(), "missing soft weight");
    bool positive = false;
    for (unsigned char c : value) {
        require(c >= '0' && c <= '9', "noninteger soft weight");
        positive = positive || c != '0';
    }
    require(positive, "nonpositive soft weight");
}
void increment(std::uint64_t& count) {
    require(count < std::numeric_limits<std::uint64_t>::max(), "command count overflow");
    ++count;
}
std::string jsonString(const std::string& value) {
    std::string out = "\"";
    for (unsigned char c : value) {
        if (c == '"' || c == '\\') { out += '\\'; out += static_cast<char>(c); }
        else if (c < 32) out += '?';
        else out += static_cast<char>(c);
    }
    return out + '"';
}
void bridge(std::istream& input) {
    Tokens tokens(input);
    enum Phase { Prefix, Body, Queries } phase = Prefix;
    bool logic = false, queried = false, exited = false;
    std::uint64_t commands = 0, declarations = 0, hard = 0, soft = 0;
    for (auto first = tokens.take(); !first.empty(); first = tokens.take()) {
        require(!exited && first == "(", "content outside command or after exit");
        auto head = tokens.take();
        if (head == "set-logic") {
            require(!logic && phase == Prefix && declarations == 0, "duplicate or late logic");
            tokens.expect("ALL"); tokens.expect(")");
            std::cout << "(set-logic ALL)\n"; logic = true;
        } else if (head == "declare-const" || head == "declare-fun") {
            require(phase == Prefix, "late declaration");
            auto name = tokens.take();
            require(!name.empty() && name != "(" && name != ")" && name[0] != '"', "invalid declaration name");
            if (head == "declare-fun") { tokens.expect("("); tokens.expect(")"); }
            tokens.expect("Bool"); tokens.expect(")");
            std::cout << '(' << head << ' ' << name << (head == "declare-fun" ? " () Bool)\n" : " Bool)\n");
            increment(declarations);
        } else if (head == "assert") {
            require(phase != Queries, "assertion after query"); phase = Body;
            std::cout << "(assert "; term(tokens); tokens.expect(")"); std::cout << ")\n";
            increment(hard);
        } else if (head == "assert-soft") {
            require(phase != Queries, "soft assertion after query"); phase = Body;
            // let is simultaneous: this value is evaluated in the original scope.
            std::cout << "(assert (let ((|somt.soft.check| "; term(tokens);
            tokens.expect(":weight"); weight(tokens.take()); tokens.expect(")");
            std::cout << ")) (or |somt.soft.check| (not |somt.soft.check|))))\n";
            increment(soft);
        } else if (head == "check-sat" || head == "exit") {
            tokens.expect(")"); phase = Queries;
            if (head == "check-sat") { require(!queried, "duplicate query"); queried = true; }
            else { require(queried, "exit before query"); exited = true; }
            std::cout << '(' << head << ")\n";
        } else throw std::runtime_error("unsupported original command: " + head);
        increment(commands);
        require(bool(std::cout), "bridged output I/O error");
    }
    require(queried && exited, "incomplete original query tail");
    std::cout.flush(); require(bool(std::cout), "bridged output flush error");
    std::cerr << "{\"status\":\"bridged\",\"original_eof\":true,\"commands\":" << commands
              << ",\"declarations\":" << declarations << ",\"hard_assertions\":" << hard
              << ",\"soft_assertions\":" << soft
              << ",\"parser_scope\":\"CVC5 bridged whole-module typecheck\",\"unchanged_original_script_parse\":false,"
              << "\"original_term_tokens_preserved\":true,\"solver_search\":false,"
              << "\"relation_and_cost_check\":\"requires complete exact original-stream certificate\"}\n";
}
} // namespace
int main(int argc, char** argv) {
    std::ios::sync_with_stdio(false);
    try {
        require(argc == 2, "usage: somt-wcnf-load-bridge ORIGINAL_SMT_PLAIN (pipe allowed)");
        std::ifstream input(argv[1], std::ios::binary);
        require(bool(input), "cannot open original input");
        bridge(input);
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "{\"status\":\"rejected\",\"error\":" << jsonString(error.what()) << "}\n";
        return 1;
    }
}
