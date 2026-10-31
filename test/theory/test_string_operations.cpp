#include <iostream>
#include <string>
#include <vector>
#include <utility>
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

// Test string constants
void test_string_constants(SOMTParser::ParserPtr& parser) {
    for (const auto& value : std::vector<std::pair<std::string, std::string>>{
             {"é", R"("\u{e9}")"},
             {"😀", R"("\u{1f600}")"},
             {"中", R"("\u{4e2d}")"},
             {"a\"\\é", R"("a""\u{5c}\u{e9}")"}}) {
        const auto literal = parser->mkConstStr(value.first);
        VERIFY(literal->getStringLiteral() == value.first);
        VERIFY(parser->toString(literal) == value.second);
        const auto parsed = parser->mkExpr(value.second);
        VERIFY(parsed && !parsed->isErr());
        VERIFY(parsed->getStringLiteral() == value.first);
    }
    std::vector<std::string> expressions = {
        "\"\"",                       // Empty string
        "\"Hello, World!\"",          // Simple string
        "\"String with \"\"quotes\"\"\"", // String with escaped quotes
        "\"String with \\\\backslash\"",  // String with escaped backslash
        "\"Multi-line\nstring\""      // Multi-line string
    };
    
/*
z3:
(
  (define-fun x2 () String
    "String with ""quotes""")
  (define-fun x3 () String
    "String with \\backslash")
  (define-fun x () String
    "")
  (define-fun x4 () String
    "Multi-line\nstring")
  (define-fun x1 () String
    "Hello, World!")
)
cvc5:
(
(define-fun x () String "")
(define-fun x1 () String "Hello, World!")
(define-fun x2 () String "String with ""quotes""")
(define-fun x3 () String "String with \u{5c}\u{5c}backslash")
(define-fun x4 () String "Multi-line\u{5c}nstring")
)
*/
    
    std::cout << "=== Testing String Constants ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && !result->isErr());
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

// Test string operations
void test_string_operations(SOMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(str.len \"Hello\")",
        "(str.++ \"Hello, \" \"World!\")",
        "(str.at \"Hello\" 1)",
        "(str.substr \"Hello, World!\" 7 5)",
        "(str.indexof \"Hello, World!\" \"World\" 0)",
        "(str.replace \"Hello, World!\" \"World\" \"Universe\")",
        "(str.prefixof \"Hello\" \"Hello, World!\")",
        "(str.suffixof \"World!\" \"Hello, World!\")",
        "(str.contains \"Hello, World!\" \"World\")"
    };
    
    std::cout << "=== Testing String Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && !result->isErr());
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

// Test string comparison operations
void test_string_comparisons(SOMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(= \"Hello\" \"Hello\")",
        "(= \"Hello\" \"World\")",
        "(str.< \"Hello\" \"World\")",
        "(str.<= \"Hello\" \"Hello\")",
        "(str.> \"World\" \"Hello\")",
        "(str.>= \"World\" \"World\")"
    };
    
    std::cout << "=== Testing String Comparison Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && !result->isErr());
        VERIFY(result->isTrue() || result->isFalse());
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

// Test regular expression operations
void test_regex_operations(SOMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(str.in_re \"abc\" (re.* (re.range \"a\" \"z\")))",
        "(str.in_re \"123\" (re.+ (re.range \"0\" \"9\")))",
        "(str.in_re \"abc\" (re.union (re.* (re.range \"a\" \"z\")) (re.* (re.range \"0\" \"9\"))))",
        "(str.in_re \"\" re.allchar)",
        "(str.in_re \"abc\" (re.++ (re.range \"a\" \"a\") (re.range \"b\" \"b\") (re.range \"c\" \"c\")))"
    };
    
    std::cout << "=== Testing Regular Expression Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && !result->isErr());
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

// ─── Issue #4: Regex evaluate ────────────────────────────────────────────────
// These tests verify that the 10 NT_REG_* kinds previously returning
// not_implemented_warning() are now handled by evaluateSimpleOp and
// correctly propagate through evaluate().
void test_regex_evaluate(SOMTParser::ParserPtr& parser) {
    using namespace SOMTParser;
    ModelPtr model = newModel();

    std::cout << "=== Issue #4: Regex evaluate (constant folding via RegexUtils) ===" << std::endl;

    // Helper macros — assert is disabled by -DNDEBUG, so we use explicit checks.
#define EXPECT_TRUE(expr, label) \
    do { \
        auto _e = parser->mkExpr(expr); \
        if (!_e || _e->isErr()) { \
            std::cerr << "FAIL [" label "]: mkExpr returned error: " << ((_e) ? parser->toString(_e) : "null") << "\n"; \
            exit(1); \
        } \
        /* After constant folding, mkExpr already returns true/false. */ \
        /* evaluate() is a belt-and-suspenders call in case the fold path differs. */ \
        auto _ev = parser->evaluate(_e, model); \
        auto _node = (_ev && !_ev->isErr()) ? _ev : _e; \
        if (!_node->isTrue()) { \
            std::cerr << "FAIL [" label "]: expected true, got: " << parser->toString(_node) << "\n"; \
            exit(1); \
        } \
        std::cout << "  [PASS] " label ": " << parser->toString(_node) << "\n"; \
    } while (0)

#define EXPECT_FALSE(expr, label) \
    do { \
        auto _e = parser->mkExpr(expr); \
        if (!_e || _e->isErr()) { \
            std::cerr << "FAIL [" label "]: mkExpr returned error: " << ((_e) ? parser->toString(_e) : "null") << "\n"; \
            exit(1); \
        } \
        auto _ev = parser->evaluate(_e, model); \
        auto _node = (_ev && !_ev->isErr()) ? _ev : _e; \
        if (!_node->isFalse()) { \
            std::cerr << "FAIL [" label "]: expected false, got: " << parser->toString(_node) << "\n"; \
            exit(1); \
        } \
        std::cout << "  [PASS] " label ": " << parser->toString(_node) << "\n"; \
    } while (0)

    // ── Positive tests ────────────────────────────────────────────────

    // re.* : empty string is always in Kleene star
    EXPECT_TRUE(R"((str.in_re "" (re.* (re.range "a" "z"))))", "re.* empty");

    // re.* : any sequence of [a-z] characters
    EXPECT_TRUE(R"((str.in_re "abc" (re.* (re.range "a" "z"))))", "re.* abc");

    // re.+ : at least one character
    EXPECT_TRUE(R"((str.in_re "a" (re.+ (re.range "a" "z"))))", "re.+ single");

    // re.opt : zero occurrences
    EXPECT_TRUE(R"((str.in_re "" (re.opt (re.range "a" "z"))))", "re.opt empty");

    // re.opt : one occurrence
    EXPECT_TRUE(R"((str.in_re "a" (re.opt (re.range "a" "z"))))", "re.opt single");

    // re.comp : "1" is NOT in [a-z], so it IS in the complement
    EXPECT_TRUE(R"((str.in_re "1" (re.comp (re.range "a" "z"))))", "re.comp 1 not-in [a-z]");

    // re.range : single character in range
    EXPECT_TRUE(R"((str.in_re "m" (re.range "a" "z"))))", "re.range m in [a-z]");

    // re.++ : concatenation
    EXPECT_TRUE(R"((str.in_re "ab" (re.++ (re.range "a" "a") (re.range "b" "b"))))",
                "re.concat ab");

    // re.++ : 3-level nested concatenation
    EXPECT_TRUE(R"((str.in_re "abc" (re.++ (re.range "a" "a") (re.++ (re.range "b" "b") (re.range "c" "c")))))",
                "re.concat nested abc");

    // re.++ with re.* as subexpr
    EXPECT_TRUE(R"((str.in_re "ab" (re.++ (re.range "a" "a") (re.* (re.range "b" "b")))))",
                "re.concat with re.*");

    // re.++ with re.union as subexpr
    EXPECT_TRUE(R"((str.in_re "ac" (re.++ (re.union (re.range "a" "a") (re.range "b" "b")) (re.range "c" "c"))))",
                "re.concat with re.union");

    // re.union : "5" is in [0-9]
    EXPECT_TRUE(R"((str.in_re "5" (re.union (re.range "a" "z") (re.range "0" "9"))))",
                "re.union 5 in [0-9]");

    // re.inter : "abc" is in both [a-z]* and [a-m]*  (a,b,c all <= m)
    EXPECT_TRUE(R"((str.in_re "abc" (re.inter (re.* (re.range "a" "z")) (re.* (re.range "a" "m")))))",
                "re.inter abc in both");

    // re.^ : exactly 3 repetitions
    EXPECT_TRUE(R"((str.in_re "aaa" (re.^ (re.range "a" "z") 3)))", "re.repeat aaa x3");

    // str.to_re : exact literal match
    EXPECT_TRUE(R"((str.in_re "hello" (str.to_re "hello")))", "str.to_re hello");

    // re.allchar : any single character
    EXPECT_TRUE(R"((str.in_re "x" re.allchar))", "re.allchar x");

    // ── Negative tests ────────────────────────────────────────────────

    // re.range : "abc" is NOT in [a-z] because the range matches exactly 1 character
    EXPECT_FALSE(R"((str.in_re "abc" (re.range "a" "z"))))", "re.range abc NOT 1-char");

    // Range endpoints must both be single characters. The old folder used
    // only their first bytes and turned the first formula into true.
    EXPECT_FALSE(R"((str.in_re "a" (re.range "ab" "z"))))", "multi-character lower range");
    EXPECT_FALSE(R"((str.in_re "a" (re.range "a" "zz"))))", "multi-character upper range");
    EXPECT_FALSE(R"((str.in_re "a" (re.range "" "z"))))", "empty range endpoint");
    EXPECT_FALSE(R"((str.in_re "a" (re.range "z" "a"))))", "reversed range");
    EXPECT_TRUE(R"((str.in_re "" (re.* (re.range "ab" "z"))))", "empty range star");

    // re.* : "1" is NOT in [a-z]*
    EXPECT_FALSE(R"((str.in_re "1" (re.* (re.range "a" "z"))))", "re.* 1 not in [a-z]*");

    // re.+ : empty string is NOT in re.+
    EXPECT_FALSE(R"((str.in_re "" (re.+ (re.range "a" "z"))))", "re.+ empty NOT valid");

    // re.diff : "abc" is in [a-z]* but ALSO in [a-m]*, so NOT in the difference
    EXPECT_FALSE(
        R"((str.in_re "abc" (re.diff (re.* (re.range "a" "z")) (re.* (re.range "a" "m")))))",
        "re.diff abc not in diff");

    // str.to_re : mismatch
    EXPECT_FALSE(R"((str.in_re "world" (str.to_re "hello")))", "str.to_re mismatch");

#undef EXPECT_TRUE
#undef EXPECT_FALSE

    std::cout << "  Issue #4 regex evaluate: all assertions passed\n";
}

int main() {
    std::cout << "======= String Operations Test =======" << std::endl;
    
    SOMTParser::ParserPtr parser = SOMTParser::newParser();
    
    test_string_constants(parser);
    test_string_operations(parser);
    test_string_comparisons(parser);
    test_regex_operations(parser);
    test_regex_evaluate(parser);
    
    return 0;
}
