#include "thf_expression_parser.h"

#include <cctype>
#include <algorithm>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <new>
#include <sstream>
#include <unordered_set>
#include <utility>

namespace SOMTParser::Lang::ThfPrototype {
namespace H = SOMTParser::Uir::Hir;

namespace {
bool sameDeclaredType(const Type& left, const Type& right) {
    if (left.kind != right.kind || left.name != right.name) { return false; }
    if (left.kind != Type::Kind::ARROW) { return true; }
    return left.domain && right.domain && left.codomain && right.codomain
        && sameDeclaredType(*left.domain, *right.domain)
        && sameDeclaredType(*left.codomain, *right.codomain);
}

std::string describeType(const Type& type) {
    switch (type.kind) {
    case Type::Kind::BOOL: return "$o";
    case Type::Kind::INT: return "$int";
    case Type::Kind::REAL: return "$real";
    case Type::Kind::INDIVIDUAL: return type.name;
    case Type::Kind::ARROW:
        if (!type.domain || !type.codomain) { return "<malformed-arrow>"; }
        return "(" + describeType(*type.domain) + ">" + describeType(*type.codomain) + ")";
    }
    return "<unknown-type>";
}
}

ThfParseError::ThfParseError(std::string message, SourceSpan source, Kind kind)
    : std::runtime_error(std::move(message)), source_(std::move(source)), kind_(kind) {}

struct ThfExpressionParser::SymbolValues {
    explicit SymbolValues(std::shared_ptr<const ThfSignature> completed_signature)
        : signature(std::move(completed_signature)) {}

    std::shared_ptr<const ThfSignature> signature;
    std::unordered_map<std::string, FunctionTermPtr> values;
};

ThfExpressionParser::ThfExpressionParser(std::string source, std::string file,
                                         std::uint32_t first_line,
                                         std::uint32_t first_column,
                                         ThfSignature signature,
                                         FunctionHirBuilder& builder)
    : ThfExpressionParser(std::move(source), std::move(file), first_line,
                          first_column, builder,
                          std::make_shared<const ThfSignature>(std::move(signature))) {}

ThfExpressionParser::ThfExpressionParser(std::string source, std::string file,
                                         std::uint32_t first_line,
                                         std::uint32_t first_column,
                                         FunctionHirBuilder& builder,
                                         std::shared_ptr<const ThfSignature> signature)
    : ThfExpressionParser(std::move(source), std::move(file), first_line, first_column,
                          builder, std::make_shared<SymbolValues>(std::move(signature)),
                          ShareSymbolValues{}) {}

ThfExpressionParser::ThfExpressionParser(std::string source, std::string file,
                                         std::uint32_t first_line,
                                         std::uint32_t first_column,
                                         FunctionHirBuilder& builder,
                                         std::shared_ptr<SymbolValues> symbol_values,
                                         ShareSymbolValues)
    : source_text_(std::move(source)), file_(std::move(file)), line_(first_line),
      column_(first_column), signature_(symbol_values->signature),
      symbol_values_(std::move(symbol_values)), builder_(builder) {
    if (!signature_) { throw std::invalid_argument("THF parser needs a signature"); }
    for (;;) {
        Token token = lex();
        tokens_.push_back(token);
        if (token.kind == Token::Kind::END) { break; }
    }
}

ThfExpressionParser::Token ThfExpressionParser::lex() {
    auto advance = [&]() {
        const char c = source_text_[offset_++];
        if (c == '\n') { ++line_; column_ = 1; }
        else { ++column_; }
        return c;
    };
    while (offset_ < source_text_.size()) {
        const unsigned char c = static_cast<unsigned char>(source_text_[offset_]);
        if (std::isspace(c)) { advance(); continue; }
        if (source_text_[offset_] == '%') {
            while (offset_ < source_text_.size() && source_text_[offset_] != '\n') {
                advance();
            }
            continue;
        }
        break;
    }

    Token out;
    out.source = SourceSpan{file_, line_, column_};
    if (offset_ >= source_text_.size()) { return out; }
    const unsigned char c = static_cast<unsigned char>(source_text_[offset_]);
    if (std::isalpha(c) || source_text_[offset_] == '$' || source_text_[offset_] == '_') {
        const std::size_t begin = offset_;
        out.variable = std::isupper(c) != 0;
        while (offset_ < source_text_.size()) {
            const unsigned char d = static_cast<unsigned char>(source_text_[offset_]);
            if (!std::isalnum(d) && source_text_[offset_] != '$'
                && source_text_[offset_] != '_') { break; }
            advance();
        }
        out.kind = Token::Kind::WORD;
        out.text = source_text_.substr(begin, offset_ - begin);
        return out;
    }
    if (std::isdigit(c)) {
        const std::size_t begin = offset_;
        while (offset_ < source_text_.size()
               && std::isdigit(static_cast<unsigned char>(source_text_[offset_]))) {
            advance();
        }
        out.kind = Token::Kind::NUMBER;
        out.text = source_text_.substr(begin, offset_ - begin);
        return out;
    }
    out.kind = Token::Kind::PUNCT;
    static const char* const operators[] = {"<=>", "<~>", "~&", "~|", "=>", "<=", "!=", nullptr};
    for (const char* op : operators) {
        if (!op) { break; }
        const std::string spelling(op);
        if (source_text_.compare(offset_, spelling.size(), spelling) == 0) {
            for (std::size_t i = 0; i < spelling.size(); ++i) { advance(); }
            out.text = spelling;
            return out;
        }
    }
    out.text.push_back(advance());
    return out;
}

const ThfExpressionParser::Token& ThfExpressionParser::peek() const {
    return tokens_.at(token_index_);
}

bool ThfExpressionParser::eat(const char* punct) {
    if (peek().kind != Token::Kind::PUNCT || peek().text != punct) { return false; }
    ++token_index_;
    return true;
}

void ThfExpressionParser::expect(const char* punct) {
    if (!eat(punct)) { fail(std::string("expected '") + punct + "'", peek().source); }
}

[[noreturn]] void ThfExpressionParser::fail(const std::string& message,
                                            const SourceSpan& at) const {
    throw ThfParseError(message, at);
}

FunctionTermPtr ThfExpressionParser::parse() {
    FunctionTermPtr result = formula();
    if (peek().kind != Token::Kind::END) {
        fail("unexpected trailing THF token '" + peek().text + "'", peek().source);
    }
    return result;
}

FunctionTermPtr ThfExpressionParser::formula() {
    return implication();
}

FunctionTermPtr ThfExpressionParser::implication() {
    FunctionTermPtr lhs = disjunction();
    if (peek().kind != Token::Kind::PUNCT) { return lhs; }
    const std::string op = peek().text;
    if (op == "=>" || op == "<=") {
        const SourceSpan at = peek().source;
        ++token_index_;
        FunctionTermPtr rhs = implication();
        if (op == "<=") { std::swap(lhs, rhs); }
        return builder_.withSource(builder_.logicalBinary(
            FunctionTerm::Kind::IMPLIES, std::move(lhs), std::move(rhs)), at);
    }
    if (op == "<=>") {
        const SourceSpan at = peek().source;
        ++token_index_;
        FunctionTermPtr rhs = disjunction();
        FunctionTermPtr lr = builder_.logicalBinary(FunctionTerm::Kind::IMPLIES, lhs, rhs);
        FunctionTermPtr rl = builder_.logicalBinary(FunctionTerm::Kind::IMPLIES, rhs, lhs);
        return builder_.withSource(builder_.logicalBinary(
            FunctionTerm::Kind::AND, std::move(lr), std::move(rl)), at);
    }
    if (op == "<~>") {
        const SourceSpan at = peek().source;
        ++token_index_;
        FunctionTermPtr rhs = disjunction();
        FunctionTermPtr both = builder_.logicalBinary(FunctionTerm::Kind::AND, lhs, rhs);
        FunctionTermPtr neither = builder_.logicalBinary(FunctionTerm::Kind::AND,
            builder_.logicalNot(lhs), builder_.logicalNot(rhs));
        return builder_.withSource(builder_.logicalNot(builder_.logicalBinary(
            FunctionTerm::Kind::OR, std::move(both), std::move(neither))), at);
    }
    return lhs;
}

FunctionTermPtr ThfExpressionParser::disjunction() {
    FunctionTermPtr result = conjunction();
    while (peek().kind == Token::Kind::PUNCT
           && (peek().text == "|" || peek().text == "~|")) {
        const Token op = peek();
        ++token_index_;
        FunctionTermPtr combined = builder_.logicalBinary(FunctionTerm::Kind::OR,
            std::move(result), conjunction());
        if (op.text == "~|") { combined = builder_.logicalNot(std::move(combined)); }
        result = builder_.withSource(std::move(combined), op.source);
    }
    return result;
}

FunctionTermPtr ThfExpressionParser::conjunction() {
    FunctionTermPtr result = unary();
    while (peek().kind == Token::Kind::PUNCT
           && (peek().text == "&" || peek().text == "~&")) {
        const Token op = peek();
        ++token_index_;
        FunctionTermPtr combined = builder_.logicalBinary(FunctionTerm::Kind::AND,
            std::move(result), unary());
        if (op.text == "~&") { combined = builder_.logicalNot(std::move(combined)); }
        result = builder_.withSource(std::move(combined), op.source);
    }
    return result;
}

FunctionTermPtr ThfExpressionParser::unary() {
    if (eat("~")) {
        const SourceSpan at = tokens_[token_index_ - 1].source;
        // A prefix unary is a unit formula in THF. Its operand ends at the
        // unitary boundary; parsing another full unary expression here would
        // let an enclosing `@` escape into the negation's scope.
        return builder_.withSource(builder_.logicalNot(unitary()), at);
    }
    if (peek().kind == Token::Kind::PUNCT
        && (peek().text == "!" || peek().text == "?")) {
        return quantified();
    }
    return equality();
}

FunctionTermPtr ThfExpressionParser::unitary() {
    if (peek().kind == Token::Kind::PUNCT
        && (peek().text == "!" || peek().text == "?")) {
        return quantified();
    }
    if (peek().kind == Token::Kind::PUNCT && peek().text == "^") {
        return lambda();
    }
    if (peek().kind == Token::Kind::PUNCT && peek().text == "~") {
        const SourceSpan at = peek().source;
        ++token_index_;
        return builder_.withSource(builder_.logicalNot(unitary()), at);
    }
    // Parentheses are the THF syntax for extending a unitary expression over
    // a compound formula. Otherwise stop before a surrounding @ or connective.
    if (peek().kind == Token::Kind::PUNCT && peek().text == "(") {
        return primary();
    }
    return primary();
}

FunctionTermPtr ThfExpressionParser::quantified() {
    const Token quant = peek();
    ++token_index_;
    expect("[");
    std::vector<FunctionBinder> binders;
    for (;;) {
        const Token name = peek();
        if (name.kind != Token::Kind::WORD || !name.variable) {
            fail("THF quantifier binder must be an uppercase variable", name.source);
        }
        ++token_index_;
        expect(":");
        Type type = parseType();
        FunctionBinder binder = builder_.binder(name.text, std::move(type), name.source);
        bound_[name.text].push_back(binder);
        binders.push_back(std::move(binder));
        if (!eat(",")) { break; }
    }
    expect("]");
    expect(":");
    FunctionTermPtr body = unitary();
    for (auto it = binders.rbegin(); it != binders.rend(); ++it) {
        body = builder_.quantify(quant.text == "!", *it, std::move(body));
        body = builder_.withSource(std::move(body), quant.source);
    }
    for (const FunctionBinder& binder : binders) {
        auto found = bound_.find(binder.name);
        if (found == bound_.end() || found->second.empty()
            || found->second.back().id != binder.id) {
            fail("internal THF binder-scope stack mismatch", binder.source);
        }
        found->second.pop_back();
        if (found->second.empty()) { bound_.erase(found); }
    }
    return body;
}

FunctionTermPtr ThfExpressionParser::lambda() {
    const Token lambda_token = peek();
    ++token_index_;
    expect("[");
    std::vector<FunctionBinder> binders;
    for (;;) {
        const Token name = peek();
        if (name.kind != Token::Kind::WORD || !name.variable) {
            fail("THF lambda binder must be an uppercase variable", name.source);
        }
        ++token_index_;
        expect(":");
        Type type = parseType();
        FunctionBinder binder = builder_.binder(name.text, std::move(type), name.source);
        bound_[name.text].push_back(binder);
        binders.push_back(std::move(binder));
        if (!eat(",")) { break; }
    }
    expect("]");
    expect(":");
    // THF makes lambda scope explicit through its unitary body. An @ following
    // an unparenthesized body belongs to the surrounding left-associative
    // application, e.g. `map @ ^[X] : X @ Y` is `(map @ (^[X]:X)) @ Y`.
    FunctionTermPtr body = unitary();
    for (auto it = binders.rbegin(); it != binders.rend(); ++it) {
        body = builder_.lambda(*it, std::move(body));
        body = builder_.withSource(std::move(body), lambda_token.source);
    }
    for (const FunctionBinder& binder : binders) {
        auto found = bound_.find(binder.name);
        if (found == bound_.end() || found->second.empty()
            || found->second.back().id != binder.id) {
            fail("internal THF binder-scope stack mismatch", binder.source);
        }
        found->second.pop_back();
        if (found->second.empty()) { bound_.erase(found); }
    }
    return body;
}

FunctionTermPtr ThfExpressionParser::equality() {
    FunctionTermPtr lhs = application();
    const bool negated = eat("!=");
    const bool plain = !negated && eat("=");
    if (!negated && !plain) { return lhs; }
    const SourceSpan eq_source = tokens_[token_index_ - 1].source;
    // The right side remains an application (e.g. `P = f @ X`), but starts
    // from a unitary so a Boolean prefix formula such as `P = ~ Q` is legal.
    FunctionTermPtr rhs = application();
    FunctionTermPtr result = builder_.equal(std::move(lhs), std::move(rhs));
    if (negated) { result = builder_.logicalNot(std::move(result)); }
    return builder_.withSource(std::move(result), eq_source);
}

FunctionTermPtr ThfExpressionParser::application() {
    FunctionTermPtr result = unitary();
    while (eat("@")) {
        const SourceSpan at = tokens_[token_index_ - 1].source;
        FunctionTermPtr argument = unitary();
        const std::string function_type = describeType(result->type);
        const std::string argument_type = describeType(argument->type);
        try {
            result = builder_.withSource(
                builder_.apply(std::move(result), std::move(argument)), at);
        } catch (const std::bad_alloc&) {
            throw;
        } catch (const std::exception& error) {
            fail(std::string(error.what()) + " (function " + function_type
                 + ", argument " + argument_type + ")", at);
        }
    }
    return result;
}

FunctionTermPtr ThfExpressionParser::primary() {
    if (peek().kind == Token::Kind::PUNCT && peek().text == "^") { return lambda(); }
    // THF permits logical connectives as typed terms. Parentheses distinguish
    // a connective value, such as `(=>)`, from the corresponding formula
    // connective between two operands.
    if (peek().kind == Token::Kind::PUNCT && peek().text == "("
        && token_index_ + 2 < tokens_.size()
        && tokens_[token_index_ + 1].kind == Token::Kind::PUNCT
        && tokens_[token_index_ + 2].kind == Token::Kind::PUNCT
        && tokens_[token_index_ + 2].text == ")") {
        const Token connective = tokens_[token_index_ + 1];
        if (connective.text == "~" || connective.text == "&" || connective.text == "|"
            || connective.text == "~&" || connective.text == "~|"
            || connective.text == "=>" || connective.text == "<="
            || connective.text == "<=>" || connective.text == "<~>") {
            token_index_ += 3;
            return connectiveValue(connective);
        }
    }
    if (eat("(")) {
        FunctionTermPtr nested = formula();
        expect(")");
        return nested;
    }
    const Token token = peek();
    if (token.kind != Token::Kind::WORD) {
        fail("expected a THF symbol, variable, lambda, or parenthesized formula", token.source);
    }
    ++token_index_;
    if (token.variable) {
        const auto found = bound_.find(token.text);
        if (found == bound_.end() || found->second.empty()) {
            fail("unbound THF variable '" + token.text + "'", token.source);
        }
        return builder_.withSource(builder_.bound(found->second.back()), token.source);
    }
    if (token.text == "$true") { return builder_.withSource(builder_.value(H::mkBool(true)), token.source); }
    if (token.text == "$false") { return builder_.withSource(builder_.value(H::mkBool(false)), token.source); }
    const auto found = signature_->find(token.text);
    if (found == signature_->end()) {
        fail("THF symbol has no declared type: '" + token.text + "'", token.source);
    }
    const auto cached = symbol_values_->values.find(token.text);
    if (cached != symbol_values_->values.end()) {
        return builder_.withSource(cached->second, token.source);
    }
    // The value's recursive Sort and Type depend only on this completed
    // signature. Share them across formulas, then locate a fresh outer node
    // for every source occurrence; no binder or compound formula AST is cached.
    FunctionTermPtr value = builder_.withSource(builder_.value(H::mkIdent(token.text, [&]() {
            const Type& t = found->second;
            if (t.kind == Type::Kind::BOOL) { return H::Sort::boolean(); }
            if (t.kind == Type::Kind::INT) { return H::Sort::integer(); }
            if (t.kind == Type::Kind::REAL) { return H::Sort::real(); }
            if (t.kind == Type::Kind::INDIVIDUAL) { return H::Sort::uninterpreted(t.name); }
            if (!t.domain || !t.codomain) {
                fail("malformed function symbol type", token.source);
            }
            auto make_sort = [&](auto&& self, const Type& type) -> H::Sort {
                if (type.kind == Type::Kind::BOOL) { return H::Sort::boolean(); }
                if (type.kind == Type::Kind::INT) { return H::Sort::integer(); }
                if (type.kind == Type::Kind::REAL) { return H::Sort::real(); }
                if (type.kind == Type::Kind::INDIVIDUAL) {
                    return H::Sort::uninterpreted(type.name);
                }
                if (!type.domain || !type.codomain) {
                    fail("malformed function symbol type", token.source);
                }
                return H::Sort::array(self(self, *type.domain), self(self, *type.codomain));
            };
            return make_sort(make_sort, t);
        }())), token.source);
    symbol_values_->values.emplace(token.text, value);
    return value;
}

FunctionTermPtr ThfExpressionParser::connectiveValue(const Token& token) {
    const Type boolean = Type::boolean();
    if (token.text == "~") {
        const auto operand = builder_.binder("__thf_not_operand", boolean, token.source);
        return builder_.withSource(builder_.lambda(operand,
            builder_.logicalNot(builder_.bound(operand))), token.source);
    }

    const auto left = builder_.binder("__thf_connective_left", boolean, token.source);
    const auto right = builder_.binder("__thf_connective_right", boolean, token.source);
    FunctionTermPtr lhs = builder_.bound(left);
    FunctionTermPtr rhs = builder_.bound(right);
    FunctionTermPtr body;
    if (token.text == "&" || token.text == "~&") {
        body = builder_.logicalBinary(FunctionTerm::Kind::AND, lhs, rhs);
        if (token.text == "~&") { body = builder_.logicalNot(std::move(body)); }
    } else if (token.text == "|" || token.text == "~|") {
        body = builder_.logicalBinary(FunctionTerm::Kind::OR, lhs, rhs);
        if (token.text == "~|") { body = builder_.logicalNot(std::move(body)); }
    } else if (token.text == "=>") {
        body = builder_.logicalBinary(FunctionTerm::Kind::IMPLIES, lhs, rhs);
    } else if (token.text == "<=") {
        body = builder_.logicalBinary(FunctionTerm::Kind::IMPLIES, rhs, lhs);
    } else if (token.text == "<=>" || token.text == "<~>") {
        FunctionTermPtr forward = builder_.logicalBinary(FunctionTerm::Kind::IMPLIES, lhs, rhs);
        FunctionTermPtr reverse = builder_.logicalBinary(FunctionTerm::Kind::IMPLIES, rhs, lhs);
        body = builder_.logicalBinary(FunctionTerm::Kind::AND,
                                      std::move(forward), std::move(reverse));
        if (token.text == "<~>") { body = builder_.logicalNot(std::move(body)); }
    } else {
        fail("unsupported THF connective term '" + token.text + "'", token.source);
    }
    return builder_.withSource(builder_.lambda(left,
        builder_.lambda(right, std::move(body))), token.source);
}

Type ThfExpressionParser::parseType() {
    Type domain = parseTypeAtom();
    if (!eat(">")) { return domain; }
    return Type::arrow(std::move(domain), parseType());
}

Type ThfExpressionParser::parseTypeAtom() {
    if (eat("(")) {
        Type nested = parseType();
        expect(")");
        return nested;
    }
    const Token token = peek();
    if (token.kind != Token::Kind::WORD || token.variable) {
        fail("expected a THF simple type", token.source);
    }
    ++token_index_;
    if (token.text == "$o") { return Type::boolean(); }
    if (token.text == "$int") { return Type::integer(); }
    if (token.text == "$real") { return Type::real(); }
    if (token.text == "$i") { return Type::individual("$i"); }
    return Type::individual(token.text);
}

Type ThfExpressionParser::parseTypeText(std::string source, std::string file,
                                        std::uint32_t first_line,
                                        std::uint32_t first_column,
                                        FunctionHirBuilder& builder) {
    ThfExpressionParser parser(std::move(source), std::move(file), first_line,
                               first_column, ThfSignature{}, builder);
    Type type = parser.parseType();
    if (parser.peek().kind != Token::Kind::END) {
        parser.fail("unexpected trailing token in THF type", parser.peek().source);
    }
    return type;
}

namespace {
std::string trim(std::string value) {
    const auto first = value.find_first_not_of(" \t\r\n");
    if (first == std::string::npos) { return {}; }
    const auto last = value.find_last_not_of(" \t\r\n");
    return value.substr(first, last - first + 1);
}

bool isWrappedBy(const std::string& value, char open, char close) {
    if (value.size() < 2 || value.front() != open || value.back() != close) { return false; }
    int depth = 0;
    for (std::size_t i = 0; i < value.size(); ++i) {
        if (value[i] == open) { ++depth; }
        else if (value[i] == close && --depth == 0 && i + 1 != value.size()) { return false; }
    }
    return depth == 0;
}

std::vector<std::pair<std::string, std::size_t>> splitArguments(const std::string& text) {
    std::vector<std::pair<std::string, std::size_t>> out;
    int parens = 0, brackets = 0, braces = 0;
    char quote = 0;
    bool escaped = false, comment = false;
    std::size_t start = 0;
    for (std::size_t i = 0; i < text.size(); ++i) {
        const char c = text[i];
        if (comment) {
            if (c == '\n') { comment = false; }
            continue;
        }
        if (quote) {
            if (escaped) { escaped = false; }
            else if (c == '\\') { escaped = true; }
            else if (c == quote) { quote = 0; }
            continue;
        }
        if (c == '%') { comment = true; continue; }
        if (c == '\'' || c == '"') { quote = c; continue; }
        if (c == '(') { ++parens; }
        else if (c == ')') { --parens; }
        else if (c == '[') { ++brackets; }
        else if (c == ']') { --brackets; }
        else if (c == '{') { ++braces; }
        else if (c == '}') { --braces; }
        else if (c == ',' && parens == 0 && brackets == 0 && braces == 0) {
            out.emplace_back(text.substr(start, i - start), start);
            start = i + 1;
        }
    }
    out.emplace_back(text.substr(start), start);
    return out;
}

SourceSpan sourceAt(const std::string& text, const std::string& file, std::size_t offset) {
    SourceSpan span{file, 1, 1};
    const std::size_t end = std::min(offset, text.size());
    for (std::size_t i = 0; i < end; ++i) {
        if (text[i] == '\n') { ++span.line; span.column = 1; }
        else { ++span.column; }
    }
    return span;
}

SourceSpan advanceSource(SourceSpan span, const std::string& text, std::size_t offset) {
    for (std::size_t i = 0; i < std::min(offset, text.size()); ++i) {
        if (text[i] == '\n') { ++span.line; span.column = 1; }
        else { ++span.column; }
    }
    return span;
}

std::string atomicName(const std::string& text, const SourceSpan& at,
                       bool allow_integer = false) {
    const std::string value = trim(text);
    if (!value.empty() && (std::islower(static_cast<unsigned char>(value.front()))
        || (allow_integer && std::isdigit(static_cast<unsigned char>(value.front()))))) {
        const bool integer = std::isdigit(static_cast<unsigned char>(value.front()));
        if (std::all_of(value.begin(), value.end(), [integer](unsigned char c) {
                return integer ? std::isdigit(c) != 0 : std::isalnum(c) != 0 || c == '_';
            })) { return value; }
    }
    if (value.size() >= 3 && value.front() == '\'' && value.back() == '\'') {
        std::string result;
        for (std::size_t i = 1; i + 1 < value.size(); ++i) {
            char c = value[i];
            if (c == '\\') {
                if (++i + 1 >= value.size() || (value[i] != '\\' && value[i] != '\'')) {
                    throw ThfParseError("invalid escape in TPTP atomic word", at);
                }
                c = value[i];
            } else if (c == '\'' || c == '\n' || c == '\r') {
                throw ThfParseError("invalid quoted TPTP atomic word", at);
            }
            result += c;
        }
        if (!result.empty()) { return result; }
    }
    throw ThfParseError("expected a TPTP atomic word or formula name", at);
}

// Retain byte/line positions while removing both TPTP comment forms. A block
// comment may occur between include arguments or inside a formula body.
std::string withoutComments(std::string text, const std::string& file) {
    char quote = 0;
    bool escaped = false;
    for (std::size_t i = 0; i < text.size(); ++i) {
        const char c = text[i];
        if (quote) {
            if (escaped) { escaped = false; }
            else if (c == '\\') { escaped = true; }
            else if (c == quote) { quote = 0; }
        } else if (c == '\'' || c == '"') { quote = c; }
        else if (c == '%') {
            while (i < text.size() && text[i] != '\n') { text[i++] = ' '; }
            if (i == text.size()) { break; }
        } else if (c == '/' && i + 1 < text.size() && text[i + 1] == '*') {
            const auto begin = i;
            text[i++] = ' ';
            text[i++] = ' ';
            while (i + 1 < text.size() && !(text[i] == '*' && text[i + 1] == '/')) {
                if (text[i] != '\n' && text[i] != '\r') { text[i] = ' '; }
                ++i;
            }
            if (i + 1 == text.size() || i >= text.size()) {
                throw ThfParseError("unterminated block comment", sourceAt(text, file, begin));
            }
            text[i] = text[i + 1] = ' ';
            ++i;
        }
    }
    return text;
}

struct ParsedTypeDeclaration {
    std::string name;
    std::string type;
    std::size_t type_offset = 0;
};

ParsedTypeDeclaration splitTypeDeclaration(const std::string& body) {
    const std::size_t body_start = body.find_first_not_of(" \t\r\n");
    if (body_start == std::string::npos) {
        throw std::invalid_argument("empty THF type declaration");
    }
    const std::string value = trim(body);
    const bool wrapped = isWrappedBy(value, '(', ')');
    const std::string inner = wrapped ? value.substr(1, value.size() - 2) : value;
    const auto parts = splitArguments(inner);
    if (parts.size() != 1) { throw std::invalid_argument("malformed THF type declaration"); }
    const std::string& declaration = parts.front().first;
    int parens = 0;
    for (std::size_t i = 0; i < declaration.size(); ++i) {
        if (declaration[i] == '(') { ++parens; }
        else if (declaration[i] == ')') { --parens; }
        else if (declaration[i] == ':' && parens == 0) {
            const std::string raw_type = declaration.substr(i + 1);
            const std::size_t leading = raw_type.find_first_not_of(" \t\r\n");
            if (leading == std::string::npos) {
                throw std::invalid_argument("empty THF type expression");
            }
            const std::size_t value_offset = body_start + (wrapped ? 1 : 0)
                + parts.front().second + i + 1 + leading;
            return ParsedTypeDeclaration{trim(declaration.substr(0, i)), trim(raw_type),
                                         value_offset};
        }
    }
    throw std::invalid_argument("THF type declaration is missing ':'");
}
}

ThfFileParser::ThfFileParser(std::string source, std::string file,
                             FunctionHirBuilder& builder)
    : source_(std::move(source)), file_(std::move(file)), builder_(builder) {}

std::vector<ThfFileParser::Statement> ThfFileParser::scanStatements(
        const std::string& source, const std::string& file_, unsigned depth) const {
    if (depth > 16) {
        throw ThfParseError("include nesting is too deep", SourceSpan{file_, 1, 1});
    }
    const std::string source_ = withoutComments(source, file_);
    // Statement and formula positions are requested in source order. Advance
    // once through each byte instead of rescanning the complete prefix for
    // every declaration in large included libraries. Keep a reset for errors
    // which refer back to an earlier offset.
    std::size_t located_offset = 0;
    SourceSpan located{file_, 1, 1};
    const auto locate = [&](std::size_t offset) {
        const std::size_t end = std::min(offset, source_.size());
        if (end < located_offset) {
            located_offset = 0;
            located.line = 1;
            located.column = 1;
        }
        while (located_offset < end) {
            if (source_[located_offset++] == '\n') {
                ++located.line;
                located.column = 1;
            } else { ++located.column; }
        }
        return located;
    };
    std::vector<Statement> statements;
    std::size_t i = 0;
    while (i < source_.size()) {
        if (source_[i] == '%') {
            while (i < source_.size() && source_[i] != '\n') { ++i; }
            continue;
        }
        if (!std::isalpha(static_cast<unsigned char>(source_[i])) && source_[i] != '_') {
            ++i;
            continue;
        }
        const std::size_t identifier_begin = i;
        while (i < source_.size()
               && (std::isalnum(static_cast<unsigned char>(source_[i]))
                   || source_[i] == '_')) { ++i; }
        const std::string top_level_name = source_.substr(identifier_begin,
                                                          i - identifier_begin);
        std::size_t open = i;
        while (open < source_.size() && std::isspace(static_cast<unsigned char>(source_[open]))) {
            ++open;
        }
        if (top_level_name != "thf" && top_level_name != "include"
            && top_level_name != "fof" && top_level_name != "tff"
            && top_level_name != "txf" && top_level_name != "cnf") { continue; }
        if (open >= source_.size() || source_[open] != '(') { ++i; continue; }
        const std::size_t content_begin = open + 1;
        int paren_depth = 1;
        char quote = 0;
        bool escaped = false, comment = false;
        std::size_t close = content_begin;
        for (; close < source_.size(); ++close) {
            const char c = source_[close];
            if (comment) {
                if (c == '\n') { comment = false; }
                continue;
            }
            if (quote) {
                if (escaped) { escaped = false; }
                else if (c == '\\') { escaped = true; }
                else if (c == quote) { quote = 0; }
                continue;
            }
            if (c == '%') { comment = true; continue; }
            if (c == '\'' || c == '"') { quote = c; continue; }
            if (c == '(') { ++paren_depth; }
            else if (c == ')' && --paren_depth == 0) { break; }
        }
        if (close == source_.size() || paren_depth != 0) {
            throw ThfParseError("unterminated THF annotated formula", locate(i));
        }
        const auto args = splitArguments(source_.substr(content_begin, close - content_begin));
        const auto item_source = locate(identifier_begin);
        if (top_level_name == "include") {
            if (args.empty() || args.size() > 3) {
                throw ThfParseError("include is include(file[, selection[, namespace]])", item_source);
            }
            if (args.size() == 3) {
                throw ThfParseError("TPTP include namespaces are not supported", item_source,
                                    ThfParseError::Kind::UNSUPPORTED);
            }
            const std::string path = atomicName(args[0].first, item_source);
            std::optional<std::unordered_set<std::string>> selected;
            if (args.size() == 2) {
                const std::string names = trim(args[1].first);
                if (names != "all" && names != "*") {
                    if (names.size() < 2 || names.front() != '[' || names.back() != ']') {
                        throw ThfParseError("include selection needs a formula-name list or *", item_source);
                    }
                    selected.emplace();
                    const std::string body = names.substr(1, names.size() - 2);
                    if (!trim(body).empty()) {
                        for (const auto& part : splitArguments(body)) {
                            const std::string name = atomicName(part.first, item_source, true);
                            if (!selected->insert(name).second) {
                                throw ThfParseError("duplicate include selection name '" + name + "'", item_source);
                            }
                        }
                    }
                }
            }
            namespace fs = std::filesystem;
            std::vector<fs::path> tries{fs::path(file_).parent_path() / path, fs::path(path)};
            if (const char* root = std::getenv("TPTP")) { tries.push_back(fs::path(root) / path); }
            bool found = false;
            std::vector<Statement> included;
            for (const auto& candidate : tries) {
                std::ifstream input(candidate, std::ios::binary);
                if (!input) { continue; }
                std::ostringstream contents;
                contents << input.rdbuf();
                included = scanStatements(contents.str(), candidate.string(), depth + 1);
                found = true;
                break;
            }
            if (!found) {
                throw ThfParseError("cannot resolve include('" + path
                    + "'): included axioms are part of the problem and cannot be skipped",
                    item_source, ThfParseError::Kind::IO);
            }
            std::unordered_set<std::string> seen;
            for (auto& statement : included) {
                if (selected && selected->count(statement.name) == 0) { continue; }
                if (selected && !seen.insert(statement.name).second) {
                    throw ThfParseError("selected formula '" + statement.name
                        + "' occurs more than once in included subtree", item_source);
                }
                statements.push_back(std::move(statement));
            }
            if (selected && seen.size() != selected->size()) {
                throw ThfParseError("selected formula was not found exactly once in included subtree",
                                    item_source);
            }
        } else {
        if (args.size() < 3) {
            throw ThfParseError("THF statement needs name, role, and formula",
                                locate(i));
        }
        const std::string name = atomicName(args[0].first, item_source, true);
        const std::string role = trim(args[1].first);
        const std::size_t body_offset = content_begin + args[2].second;
        statements.push_back(Statement{top_level_name, name, role, args[2].first,
                                       locate(body_offset)});
        }
        i = close + 1;
        while (i < source_.size() && std::isspace(static_cast<unsigned char>(source_[i]))) { ++i; }
        if (i >= source_.size() || source_[i] != '.') {
            throw ThfParseError("THF statement must end with '.'", locate(i));
        }
        ++i;
    }
    return statements;
}

const std::vector<ThfFileParser::Statement>& ThfFileParser::statements() {
    if (!statements_) { statements_ = scanStatements(source_, file_, 0); }
    return *statements_;
}

bool ThfFileParser::hasThfStatements() {
    const auto& items = statements();
    return std::any_of(items.begin(), items.end(), [](const Statement& item) {
        return item.language == "thf";
    });
}

ThfFile ThfFileParser::parse() {
    ThfFile result;
    std::unordered_set<std::string> type_symbols;
    const auto& items = statements();
    for (const Statement& statement : items) {
        if (statement.language != "thf") {
            throw ThfParseError("mixed or non-THF TPTP statements are not supported", statement.body_source);
        }
        if (statement.role != "type") { continue; }
        try {
            const auto declaration = splitTypeDeclaration(statement.body);
            if (declaration.name.empty()) {
                throw std::invalid_argument("empty THF type symbol");
            }
            if (declaration.type == "$tType") {
                if (result.signature.count(declaration.name)) {
                    throw std::invalid_argument("conflicting THF type declaration for "
                                                + declaration.name);
                }
                if (!type_symbols.insert(declaration.name).second) { continue; }
                result.type_declarations.push_back(ThfTypeDeclaration{
                    declaration.name, Type::individual(declaration.name), true,
                    statement.body_source});
                continue;
            }
            const auto type_source = advanceSource(statement.body_source,
                                                   statement.body, declaration.type_offset);
            Type type = ThfExpressionParser::parseTypeText(declaration.type,
                type_source.file, type_source.line, type_source.column, builder_);
            if (type_symbols.count(declaration.name)) {
                throw std::invalid_argument("conflicting THF type declaration for "
                                            + declaration.name);
            }
            const auto inserted = result.signature.emplace(declaration.name, type);
            if (!inserted.second) {
                // Included axiom files may repeat a shared signature. TPTP
                // permits equal redeclarations; a different type is an error.
                if (!sameDeclaredType(inserted.first->second, type)) {
                    throw std::invalid_argument("conflicting THF type declaration for "
                                                + declaration.name);
                }
                continue;
            }
            result.type_declarations.push_back(ThfTypeDeclaration{
                declaration.name, std::move(type), false, statement.body_source});
        } catch (const ThfParseError&) {
            throw;
        } catch (const std::bad_alloc&) {
            throw;
        } catch (const std::exception& error) {
            throw ThfParseError(error.what(), statement.body_source);
        }
    }
    // The declaration pass is complete, so all formula parsers can share one
    // immutable signature. Restore its map to the returned file after parsing;
    // neither direction copies all declarations for each source formula.
    auto shared_signature = std::make_shared<ThfSignature>();
    shared_signature->swap(result.signature);
    auto shared_values = std::make_shared<ThfExpressionParser::SymbolValues>(shared_signature);
    for (const Statement& statement : items) {
        if (statement.role == "type") { continue; }
        try {
            ThfExpressionParser parser(statement.body, statement.body_source.file, statement.body_source.line,
                statement.body_source.column, builder_, shared_values,
                ThfExpressionParser::ShareSymbolValues{});
            FunctionTermPtr term = parser.parse();
            if (term->type.kind != Type::Kind::BOOL || !builder_.wellScoped(term)) {
                throw std::invalid_argument("THF formula is ill-typed or not well scoped");
            }
            result.formulas.push_back(ThfAnnotatedFormula{
                statement.name, statement.role, statement.body_source, std::move(term)});
        } catch (const ThfParseError&) {
            throw;
        } catch (const std::bad_alloc&) {
            throw;
        } catch (const std::exception& error) {
            throw ThfParseError(error.what(), statement.body_source);
        }
    }
    if (items.empty()) {
        throw ThfParseError("no THF statements found", SourceSpan{file_, 1, 1});
    }
    result.signature = std::move(*shared_signature);
    return result;
}

} // namespace SOMTParser::Lang::ThfPrototype
