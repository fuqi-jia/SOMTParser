#pragma once

#include <cctype>
#include <stdexcept>
#include <string>
#include <vector>
#include <utility>

namespace SOMTParser::Lang::Cvc5Sets {

// A syntax tree is necessary: text replacement also changes quoted symbols,
// strings, comments and declarations. The engine still performs all typing.
struct Term {
    std::string atom;
    std::vector<Term> args;
    bool list = false;
    bool is(const std::string& value) const { return !list && atom == value; }
    std::string text() const {
        if (!list) { return atom; }
        std::string result = "(";
        for (std::size_t i = 0; i < args.size(); ++i) {
            if (i) { result += ' '; }
            result += args[i].text();
        }
        return result + ")";
    }
};

inline Term call(const std::string& op, std::vector<Term> args) {
    args.insert(args.begin(), Term{op, {}, false});
    return Term{"", std::move(args), true};
}

class Reader {
public:
    explicit Reader(const std::string& source) : source_(source) {}
    std::vector<Term> read() {
        std::vector<Term> result;
        space();
        while (pos_ < source_.size()) { result.push_back(term(0)); space(); }
        return result;
    }
private:
    void space() {
        while (pos_ < source_.size()) {
            if (std::isspace(static_cast<unsigned char>(source_[pos_]))) { ++pos_; }
            else if (source_[pos_] == ';') {
                while (pos_ < source_.size() && source_[pos_] != '\n') { ++pos_; }
            } else { break; }
        }
    }
    Term term(unsigned depth) {
        space();
        if (depth > 256 || ++nodes_ > 200000) {
            throw std::runtime_error("cvc5 set normalization syntax budget exceeded");
        }
        if (pos_ == source_.size() || source_[pos_] == ')') {
            throw std::runtime_error("unexpected end of cvc5 set expression");
        }
        if (source_[pos_] == '(') {
            ++pos_;
            Term result{"", {}, true};
            space();
            while (pos_ < source_.size() && source_[pos_] != ')') {
                result.args.push_back(term(depth + 1)); space();
            }
            if (pos_ == source_.size()) { throw std::runtime_error("unclosed expression"); }
            ++pos_; return result;
        }
        const auto begin = pos_;
        const char quote = source_[pos_];
        if (quote == '|' || quote == '"') {
            ++pos_;
            while (pos_ < source_.size()) {
                if (source_[pos_++] == quote) {
                    if (quote == '"' && pos_ < source_.size() && source_[pos_] == '"') {
                        ++pos_; continue;
                    }
                    return Term{source_.substr(begin, pos_ - begin), {}, false};
                }
            }
            throw std::runtime_error("unclosed quoted token");
        }
        while (pos_ < source_.size() && !std::isspace(static_cast<unsigned char>(source_[pos_]))
               && source_[pos_] != '(' && source_[pos_] != ')' && source_[pos_] != ';') { ++pos_; }
        return Term{source_.substr(begin, pos_ - begin), {}, false};
    }
    const std::string& source_;
    std::size_t pos_ = 0, nodes_ = 0;
};

inline void normalizeTerm(Term& t, std::size_t& rewrites) {
    if (t.is("set.empty")) {
        // cvc5 1.4 defaults an un-ascribed empty set to Set Bool. It does
        // NOT infer Set Int/Real from a sibling; preserve that type rule.
        t = call("as", {Term{"set.empty", {}, false}, call("Set", {Term{"Bool", {}, false}})});
        ++rewrites; return;
    }
    if (!t.list || t.args.empty()) { return; }
    // Do not descend into ascriptions or binder declarations as expressions.
    const std::string op = t.args.front().atom;
    if (op == "as") { return; }
    if ((op == "forall" || op == "exists") && t.args.size() == 3) {
        normalizeTerm(t.args[2], rewrites); return;
    }
    if (op == "let" && t.args.size() == 3 && t.args[1].list) {
        for (auto& b : t.args[1].args) {
            if (b.list && b.args.size() == 2) { normalizeTerm(b.args[1], rewrites); }
        }
        normalizeTerm(t.args[2], rewrites); return;
    }
    for (std::size_t i = 1; i < t.args.size(); ++i) { normalizeTerm(t.args[i], rewrites); }
    if (op == "set.is_empty" && t.args.size() == 2) {
        // cvc5 sets are finite. Cardinality zero is exactly emptiness and
        // avoids guessing the element sort or duplicating the argument.
        t = call("=", {call("set.card", {t.args[1]}), Term{"0", {}, false}});
        ++rewrites; return;
    }
}

inline std::string normalize(const std::string& source, std::size_t& rewrites) {
    auto commands = Reader(source).read();
    for (auto& c : commands) {
        if (!c.list || c.args.empty()) { continue; }
        if (c.args[0].is("assert") && c.args.size() == 2) {
            normalizeTerm(c.args[1], rewrites);
        } else if ((c.args[0].is("define-fun") || c.args[0].is("define-fun-rec"))
                   && c.args.size() == 5) {
            normalizeTerm(c.args[4], rewrites);
        } else if (c.args[0].is("check-sat-assuming") && c.args.size() == 2 && c.args[1].list) {
            for (auto& a : c.args[1].args) { normalizeTerm(a, rewrites); }
        }
    }
    if (!rewrites) { return source; }
    std::string result;
    for (const auto& c : commands) { result += c.text() + '\n'; }
    return result;
}

} // namespace SOMTParser::Lang::Cvc5Sets
