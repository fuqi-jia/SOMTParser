#include <iostream>
#include <string>
#include <vector>
#include "somtparser/core/kind.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/ir/number.h"
#include "test_helpers.h"

using SOMTParser::SortManager;

// Test integer arithmetic operations
void test_integer_arithmetic(SOMTParser::ParserPtr& parser) {
    std::vector<std::pair<std::string, std::string>> cases = {
        {"42", "42"},
        {"-15", "-15"},
        {"(+ 10 20)", "30"},
        {"(- 50 30)", "20"},
        {"(* 6 7)", "42"},
        {"(div 20 5)", "4"},
        {"(mod 17 5)", "2"},
        {"(abs -42)", "42"}
    };
    
    std::cout << "=== Testing Integer Arithmetic ===" << std::endl;
    for (const auto& p : cases) {
        std::cout << "Expression: " << p.first << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(p.first);
        VERIFY(result);
        std::string got = parser->toString(result);
        std::cout << "  Result: " << got << std::endl;
        auto expected = parser->mkExpr(p.second);
        VERIFY(expected && parser->toString(result) == parser->toString(expected) &&
               "integer arithmetic result mismatch");
        std::cout << std::endl;
    }
}

// Test real number arithmetic operations
void test_real_arithmetic(SOMTParser::ParserPtr& parser) {
    std::vector<std::pair<std::string, std::string>> cases = {
        {"3.14159", "3.14159"},
        {"-2.71828", "-2.71828"},
        {"(+ 3.5 2.7)", "6.2"},
        {"(- 10.5 4.2)", "6.3"},
        {"(* 2.5 4.0)", "10.0"},
        {"(/ 15.0 3.0)", "5.0"},
        {"(^ 2.0 3.0)", "8.0"},
        {"(sqrt 16.0)", "4.0"},
        {"(abs -9.81)", "9.81"}
    };
    
    std::cout << "=== Testing Real Number Arithmetic ===" << std::endl;
    for (const auto& p : cases) {
        std::cout << "Expression: " << p.first << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(p.first);
        VERIFY(result);
        std::string got = parser->toString(result);
        std::cout << "  Result: " << got << std::endl;
        auto expected = parser->mkExpr(p.second);
        VERIFY(expected && parser->toString(result) == parser->toString(expected) &&
               "real arithmetic result mismatch");
        std::cout << std::endl;
    }
}

// Test arithmetic comparison operations
void test_comparisons(SOMTParser::ParserPtr& parser) {
    std::vector<std::pair<std::string, bool>> cases = {
        {"(< 5 10)", true},
        {"(<= 7 7)", true},
        {"(> 15 5)", true},
        {"(>= 12 12)", true},
        {"(= 42 42)", true},
        {"(distinct 3 5 7)", true}
    };
    
    std::cout << "=== Testing Arithmetic Comparisons ===" << std::endl;
    for (const auto& p : cases) {
        std::cout << "Expression: " << p.first << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(p.first);
        VERIFY(result);
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        VERIFY(result->isTrue() == p.second && "comparison should evaluate to expected bool");
        std::cout << std::endl;
    }
}

void test_precision(SOMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Precision ===" << std::endl;
    
    // Default precision (128 bits)
    std::cout << "=== Default Precision (128 bits) ===" << std::endl;
    auto r1 = parser->mkExpr("(+ 3.5 2.7)");
    auto r2 = parser->mkExpr("(- 10.5 4.2)");
    VERIFY(r1 && r2);
    std::cout << "Expression: (+ 3.5 2.7)" << std::endl;
    std::cout << "  Result: " << parser->toString(r1) << std::endl;
    VERIFY(r1->getValue()->getNumberValue().toRationalExact() ==
           SOMTParser::Rational("31/5"));
    std::cout << "Expression: (- 10.5 4.2)" << std::endl;
    std::cout << "  Result: " << parser->toString(r2) << std::endl;
    VERIFY(r2->getValue()->getNumberValue().toRationalExact() ==
           SOMTParser::Rational("63/10"));
    
    // Set higher precision (256 bits)
    parser->setEvaluatePrecision(256);
    std::cout << "\n=== Higher Precision (256 bits) ===" << std::endl;
    auto r3 = parser->mkExpr("(+ 3.5 2.7)");
    auto r4 = parser->mkExpr("(- 10.5 4.2)");
    VERIFY(r3 && r4);
    std::cout << "Expression: (+ 3.5 2.7)" << std::endl;
    std::cout << "  Result: " << parser->toString(r3) << std::endl;
    std::cout << "Expression: (- 10.5 4.2)" << std::endl;
    std::cout << "  Result: " << parser->toString(r4) << std::endl;
    VERIFY(r3->getValue()->getNumberValue().toRationalExact() ==
           SOMTParser::Rational("31/5"));
    VERIFY(r4->getValue()->getNumberValue().toRationalExact() ==
           SOMTParser::Rational("63/10"));
    
    // Disable floating point mode
    parser->setEvaluateUseFloating(false);
    std::cout << "\n=== Disable Floating Point Mode ===" << std::endl;
    auto r5 = parser->mkExpr("(+ 3.5 2.7)");
    auto r6 = parser->mkExpr("(- 10.5 4.2)");
    VERIFY(r5 && r6);
    std::cout << "Expression: (+ 3.5 2.7)" << std::endl;
    std::cout << "  Result: " << parser->toString(r5) << std::endl;
    std::cout << "Expression: (- 10.5 4.2)" << std::endl;
    std::cout << "  Result: " << parser->toString(r6) << std::endl;
    VERIFY(r5->getValue()->getNumberValue().toRationalExact() ==
           SOMTParser::Rational("31/5"));
    VERIFY(r6->getValue()->getNumberValue().toRationalExact() ==
           SOMTParser::Rational("63/10"));
}

static void test_builtin_shadow_pow2_uf(SOMTParser::ParserPtr& p) {
    std::cout << "=== Builtin shadow: pow2 ===" << std::endl;
    VERIFY(SOMTParser::builtinOperMayBeShadowedByUserFun("pow2"));
    VERIFY(!SOMTParser::isBuiltinNameReservedAgainstUserFun("pow2"));

    auto fd = p->mkFuncDec("pow2", {SortManager::INT_SORT}, SortManager::INT_SORT);
    VERIFY(fd && !fd->isUnknown() && !fd->isErr());

    p->mkVarInt("x");
    auto app = p->mkExpr("(pow2 x)");
    VERIFY(app && !app->isErr());
    VERIFY(app->isUFApplication());
}

void test_number_bitwise_operators() {
    std::cout << "=== Number (GMP) bitwise operators ===" << std::endl;
    SOMTParser::Number a(SOMTParser::Integer(0b1100));
    SOMTParser::Number b(SOMTParser::Integer(0b1010));

    VERIFY((a & b) == SOMTParser::Number(SOMTParser::Integer(0b1000)));
    VERIFY((a | b) == SOMTParser::Number(SOMTParser::Integer(0b1110)));
    VERIFY((a ^ b) == SOMTParser::Number(SOMTParser::Integer(0b0110)));
    VERIFY(~a == SOMTParser::Number(SOMTParser::Integer(-13)));

    SOMTParser::Number c(SOMTParser::Integer(1));
    VERIFY((c << 3) == SOMTParser::Number(SOMTParser::Integer(8)));

    SOMTParser::Number d(SOMTParser::Integer(16));
    VERIFY((d >> 2) == SOMTParser::Number(SOMTParser::Integer(4)));
}

int main() {
    std::cout << "======= Arithmetic Operations Test =======" << std::endl;
    
    SOMTParser::ParserPtr parser = SOMTParser::newParser();
    
    test_integer_arithmetic(parser);
    test_real_arithmetic(parser);
    test_comparisons(parser);
    test_builtin_shadow_pow2_uf(parser);
    test_precision(parser);
    test_number_bitwise_operators();

    return 0;
}
