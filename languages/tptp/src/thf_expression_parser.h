#pragma once

#include "explicit_function_hir.h"

#include <stdexcept>
#include <optional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace SOMTParser::Lang::ThfPrototype {

using ThfSignature = std::unordered_map<std::string, Type>;

class ThfParseError : public std::runtime_error {
public:
    enum class Kind { SYNTAX, IO, UNSUPPORTED };
    ThfParseError(std::string message, SourceSpan source, Kind kind = Kind::SYNTAX);
    const SourceSpan& source() const noexcept { return source_; }
    Kind kind() const noexcept { return kind_; }
private:
    SourceSpan source_;
    Kind kind_;
};

/**
 * Parser for a typed THF expression kernel: quantifiers, typed binders,
 * lambda, curried @ application, parentheses, and equality. It preserves
 * exact file/line/column spans for the consumed text. This is deliberately an
 * expression parser, not a full TPTP annotated-formula frontend.
 */
class ThfExpressionParser {
public:
    ThfExpressionParser(std::string source, std::string file, std::uint32_t first_line,
                        std::uint32_t first_column, ThfSignature signature,
                        FunctionHirBuilder& builder);
    ThfExpressionParser(std::string source, std::string file, std::uint32_t first_line,
                        std::uint32_t first_column, FunctionHirBuilder& builder,
                        std::shared_ptr<const ThfSignature> signature);
    FunctionTermPtr parse();
    static Type parseTypeText(std::string source, std::string file,
                              std::uint32_t first_line,
                              std::uint32_t first_column,
                              FunctionHirBuilder& builder);

private:
    // A file's formula readers share only immutable global value prototypes.
    // Local binders and occurrence source spans remain per expression reader.
    struct SymbolValues;
    struct ShareSymbolValues {};
    friend class ThfFileParser;
    ThfExpressionParser(std::string source, std::string file, std::uint32_t first_line,
                        std::uint32_t first_column, FunctionHirBuilder& builder,
                        std::shared_ptr<SymbolValues> symbol_values, ShareSymbolValues);

    struct Token {
        enum class Kind { WORD, NUMBER, PUNCT, END } kind = Kind::END;
        std::string text;
        SourceSpan source;
        bool variable = false;
    };

    Token lex();
    const Token& peek() const;
    bool eat(const char* punct);
    void expect(const char* punct);
    FunctionTermPtr formula();
    FunctionTermPtr implication();
    FunctionTermPtr disjunction();
    FunctionTermPtr conjunction();
    FunctionTermPtr unary();
    // A THF unitary has an explicit boundary: atoms, binders, unary forms,
    // or a parenthesized logic formula. In particular, an unparenthesized
    // trailing @ application is outside a lambda's body.
    FunctionTermPtr unitary();
    FunctionTermPtr quantified();
    FunctionTermPtr lambda();
    FunctionTermPtr equality();
    FunctionTermPtr application();
    FunctionTermPtr primary();
    FunctionTermPtr connectiveValue(const Token& token);
    Type parseType();
    Type parseTypeAtom();
    [[noreturn]] void fail(const std::string& message, const SourceSpan& at) const;

    std::string source_text_;
    std::string file_;
    std::size_t offset_ = 0;
    std::uint32_t line_ = 1;
    std::uint32_t column_ = 1;
    std::vector<Token> tokens_;
    std::size_t token_index_ = 0;
    std::shared_ptr<const ThfSignature> signature_;
    std::shared_ptr<SymbolValues> symbol_values_;
    FunctionHirBuilder& builder_;
    std::unordered_map<std::string, std::vector<FunctionBinder>> bound_;
};

struct ThfAnnotatedFormula {
    std::string name;
    std::string role;
    SourceSpan source;
    FunctionTermPtr term;
};

struct ThfTypeDeclaration {
    std::string name;
    Type type;
    bool declares_type_symbol = false;
    SourceSpan source;
};

struct ThfFile {
    std::vector<ThfTypeDeclaration> type_declarations;
    std::vector<ThfAnnotatedFormula> formulas;
    ThfSignature signature;
};

/**
 * Two-pass reader for TPTP annotated THF statements in a monomorphic file.
 * It accepts `thf(name,type,...)` declarations followed by formula roles,
 * retaining statement and expression source positions across selected,
 * recursive includes. Polymorphic type variables are rejected explicitly.
 */
class ThfFileParser {
public:
    ThfFileParser(std::string source, std::string file,
                  FunctionHirBuilder& builder);
    ThfFile parse();
    bool hasThfStatements();

private:
    struct Statement {
        std::string language;
        std::string name;
        std::string role;
        std::string body;
        SourceSpan body_source;
    };
    const std::vector<Statement>& statements();
    std::vector<Statement> scanStatements(const std::string& source,
                                         const std::string& file, unsigned depth) const;
    std::optional<std::vector<Statement>> statements_;
    std::string source_;
    std::string file_;
    FunctionHirBuilder& builder_;
};

} // namespace SOMTParser::Lang::ThfPrototype
