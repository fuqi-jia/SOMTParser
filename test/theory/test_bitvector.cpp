#include <iostream>
#include <string>
#include <vector>
#include "somtparser/core/util.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/ir/number.h"
#include "somtparser/ir/value.h"
#include "test_helpers.h"

// Test bitvector constants
void test_bv_const_value_and_utils_nat(SOMTParser::ParserPtr& parser) {
    std::cout << "=== BV (_ bv n w) getValue + BitVectorUtils (not getNumberValue) ===" << std::endl;
    auto n = parser->mkExpr("(_ bv42 8)");
    VERIFY(n && n->isCBV());
    auto v = n->getValue();
    VERIFY(v && v->getType() == SOMTParser::BV);
    VERIFY(v->getBvWidth() == 8);
    VERIFY(SOMTParser::BitVectorUtils::bvToNat(n->toString()) == SOMTParser::Integer(42));
}

void test_bitvector_constants(SOMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "#b1010",                     // 4-bit binary
        "#x1A",                       // hexadecimal (26 in decimal)
        "(_ bv42 8)",              // 42 as an 8-bit bitvector
        "(_ bv255 8)"              // 255 as an 8-bit bitvector
    };
    
    std::cout << "=== Testing Bitvector Constants ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && !result->isErr());
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

// Test bitvector logical operations
void test_bv_logical_operations(SOMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(bvnot #b1010)",
        "(bvand #b1010 #b1100)",
        "(bvor #b1010 #b1100)",
        "(bvxor #b1010 #b1100)",
        "(bvnand #b1010 #b1100)",
        "(bvnor #b1010 #b1100)",
        "(bvxnor #b1010 #b1100)"
    };
    
    std::cout << "=== Testing Bitvector Logical Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && !result->isErr());
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

// Test bitvector arithmetic operations
void test_bv_arithmetic_operations(SOMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(bvneg #b0101)",
        "(bvadd #b0101 #b0011)",
        "(bvsub #b1010 #b0011)",
        "(bvmul #b0101 #b0011)",
        "(bvudiv #b1010 #b0011)",
        "(bvurem #b1010 #b0011)",
        "(bvshl #b0101 #b0011)",
        "(bvlshr #b1010 #b0001)",
        "(bvashr #b1010 #b0001)"
    };
    
    std::cout << "=== Testing Bitvector Arithmetic Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && !result->isErr());
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

// Test bitvector comparison operations
void test_bv_comparison_operations(SOMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(bvult #b0101 #b1010)",     // unsigned less than
        "(bvule #b0101 #b0101)",     // unsigned less than or equal
        "(bvugt #b1010 #b0101)",     // unsigned greater than
        "(bvuge #b0101 #b0101)",     // unsigned greater than or equal
        "(bvslt #b0101 #b1010)",     // signed less than
        "(bvsle #b0101 #b0101)",     // signed less than or equal
        "(bvsgt #b0000 #b1111)",     // signed greater than
        "(bvsge #b0101 #b0101)"      // signed greater than or equal
    };
    
    std::cout << "=== Testing Bitvector Comparison Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        std::shared_ptr<SOMTParser::DAGNode> result = parser->mkExpr(expr);
        VERIFY(result && (result->isTrue() || result->isFalse()));
        std::cout << "  Result: " << parser->toString(result) << std::endl;
        std::cout << std::endl;
    }
}

void test_value_bv_operators_ir() {
    std::cout << "=== Value class BV logical/shift (IR) ===" << std::endl;
    SOMTParser::Value a(SOMTParser::Number(SOMTParser::Integer(0xA)));
    a.setType(SOMTParser::BV);
    a.setBvWidth(4);
    SOMTParser::Value b(SOMTParser::Number(SOMTParser::Integer(0x5)));
    b.setType(SOMTParser::BV);
    b.setBvWidth(4);

    SOMTParser::Value r_and = a.andOp(b);
    VERIFY(r_and.getType() == SOMTParser::BV);
    VERIFY(r_and.toString() == "0");

    SOMTParser::Value r_or = a.orOp(b);
    VERIFY(r_or.toString() == "15");

    SOMTParser::Value r_xor = a.xorOp(b);
    VERIFY(r_xor.toString() == "15");

    SOMTParser::Value r_shl = a.shift_left(SOMTParser::Number(SOMTParser::Integer(1)));
    VERIFY(r_shl.toString() == "20");
}

// ─── Issue #3: BV arithmetic correctness (constant-folding path) ─────────────
// Verifies that the uint64 fast path (≤64-bit BVs) produces numerically correct
// results for all five arithmetic operators.
void test_bv_arithmetic_correctness(SOMTParser::ParserPtr& parser) {
    using SOMTParser::BitVectorUtils;
    using SOMTParser::Integer;
    std::cout << "=== Issue #3: BV arithmetic result correctness (≤64-bit) ===" << std::endl;

    // bvadd: 3 + 5 = 8  (#b0011 + #b0101 = #b1000)
    {
        auto r = parser->mkExpr("(bvadd #b0011 #b0101)");
        VERIFY(r && r->isCBV());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(8));
    }
    // bvsub: 10 - 3 = 7  (#b1010 - #b0011 = #b0111)
    {
        auto r = parser->mkExpr("(bvsub #b1010 #b0011)");
        VERIFY(r && r->isCBV());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(7));
    }
    // bvmul: 3 * 5 = 15  (#b0011 * #b0101 = #b1111)
    {
        auto r = parser->mkExpr("(bvmul #b0011 #b0101)");
        VERIFY(r && r->isCBV());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(15));
    }
    // bvudiv: 10 / 2 = 5  (#b1010 / #b0010 = #b0101)
    {
        auto r = parser->mkExpr("(bvudiv #b1010 #b0010)");
        VERIFY(r && r->isCBV());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(5));
    }
    // bvurem: 10 % 3 = 1  (#b1010 % #b0011 = #b0001)
    {
        auto r = parser->mkExpr("(bvurem #b1010 #b0011)");
        VERIFY(r && r->isCBV());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(1));
    }
    // overflow check: 15 + 1 wraps to 0 in 4-bit  (#b1111 + #b0001 = #b0000)
    {
        auto r = parser->mkExpr("(bvadd #b1111 #b0001)");
        VERIFY(r && r->isCBV());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(0));
    }
    std::cout << "  BV arithmetic correctness (fast path): OK\n";
}

// ─── Issue #3: Large BV (>64-bit) exercises GMP code path ────────────────────
// Verifies that 128-bit BV arithmetic falls back to GMP and produces correct
// results (the fast path only handles ≤64-bit widths).
void test_bv_large_width_gmp_path(SOMTParser::ParserPtr& parser) {
    using SOMTParser::BitVectorUtils;
    using SOMTParser::Integer;
    std::cout << "=== Issue #3: Large BV (128-bit) GMP code path ===" << std::endl;

    // bvadd: 100 + 200 = 300
    {
        auto r = parser->mkExpr("(bvadd (_ bv100 128) (_ bv200 128))");
        VERIFY(r && r->isCBV() && !r->isErr());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(300));
    }
    // bvsub: 500 - 1 = 499
    {
        auto r = parser->mkExpr("(bvsub (_ bv500 128) (_ bv1 128))");
        VERIFY(r && r->isCBV() && !r->isErr());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(499));
    }
    // bvmul: 1000 * 1000 = 1000000
    {
        auto r = parser->mkExpr("(bvmul (_ bv1000 128) (_ bv1000 128))");
        VERIFY(r && r->isCBV() && !r->isErr());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(1000000));
    }
    // bvudiv: 1000000 / 1000 = 1000
    {
        auto r = parser->mkExpr("(bvudiv (_ bv1000000 128) (_ bv1000 128))");
        VERIFY(r && r->isCBV() && !r->isErr());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(1000));
    }
    // bvurem: 1000007 % 1000 = 7
    {
        auto r = parser->mkExpr("(bvurem (_ bv1000007 128) (_ bv1000 128))");
        VERIFY(r && r->isCBV() && !r->isErr());
        VERIFY(BitVectorUtils::bvToNat(r->toString()) == Integer(7));
    }
    std::cout << "  Large BV GMP path: OK\n";
}

void test_signed_division_remainder_and_modulo(SOMTParser::ParserPtr& parser) {
    using SOMTParser::BitVectorUtils;
    using SOMTParser::Integer;
    for (unsigned width = 1; width <= 4; ++width) {
        const int modulus = 1 << width, mask = modulus - 1;
        for (int a = 0; a < modulus; ++a) for (int b = 0; b < modulus; ++b) {
            const int sa = a < modulus / 2 ? a : a - modulus;
            const int sb = b < modulus / 2 ? b : b - modulus;
            const int quotient = sb ? sa / sb : sa < 0 ? 1 : -1;
            const int remainder = sb ? sa % sb : sa;
            const int modulo = remainder != 0 && sb != 0 && ((remainder < 0) != (sb < 0))
                ? remainder + sb : remainder;
            const auto x = BitVectorUtils::natToBv(Integer(a), Integer(static_cast<int>(width)));
            const auto y = BitVectorUtils::natToBv(Integer(b), Integer(static_cast<int>(width)));
            VERIFY(BitVectorUtils::bvToNat(BitVectorUtils::bvSdiv(x, y)) == Integer(quotient & mask));
            VERIFY(BitVectorUtils::bvToNat(BitVectorUtils::bvSrem(x, y)) == Integer(remainder & mask));
            VERIFY(BitVectorUtils::bvToNat(BitVectorUtils::bvSmod(x, y)) == Integer(modulo & mask));
            for (const auto& operation : std::vector<std::pair<std::string, int>>{
                    {"bvsdiv", quotient}, {"bvsrem", remainder}, {"bvsmod", modulo}}) {
                const auto value = parser->mkExpr("(" + operation.first + " " + x + " " + y + ")");
                VERIFY(value && value->isCBV());
                VERIFY(BitVectorUtils::bvToNat(value->toString()) == Integer(operation.second & mask));
            }
        }
    }
    VERIFY(parser->parseStr("(declare-const signed_dividend (_ BitVec 4))"));
    const auto symbolic = parser->mkExpr("(bvsdiv signed_dividend #b0000)");
    VERIFY(symbolic && !symbolic->isCBV());
    VERIFY(symbolic->getKind() == SOMTParser::NODE_KIND::NT_BV_SDIV);
    for (const auto& source : {"(= (bvsdiv (_ bv7 128) (_ bv0 128)) (bvnot (_ bv0 128)))",
                               "(= (bvsmod (bvneg (_ bv7 128)) (_ bv3 128)) (_ bv2 128))"}) {
        const auto value = parser->mkExpr(source);
        VERIFY(value && value->isTrue());
    }
}

void test_signed_mod_divisor_sign(SOMTParser::ParserPtr& parser) {
    using SOMTParser::BitVectorUtils;
    using SOMTParser::Integer;
    struct Case { int dividend; int divisor; int result; };
    const Case cases[] = {{-7, 3, 2}, {7, -3, -2}, {-7, -3, -1},
                          {7, 3, 1}, {-6, -3, 0}, {-7, 0, -7}};
    for (unsigned width : {8U, 65U}) {
        for (const auto& row : cases) {
            const auto left = BitVectorUtils::intToBv(Integer(row.dividend), Integer(static_cast<int>(width)));
            const auto right = BitVectorUtils::intToBv(Integer(row.divisor), Integer(static_cast<int>(width)));
            const auto expected = BitVectorUtils::intToBv(Integer(row.result), Integer(static_cast<int>(width)));
            VERIFY(BitVectorUtils::bvSmod(left, right) == expected);
            const auto folded = parser->mkExpr("(bvsmod " + left + " " + right + ")");
            VERIFY(folded && folded->isCBV() && folded->toString() == expected);
        }
    }
}

int main() {
    std::cout << "======= Bitvector Operations Test =======" << std::endl;

    SOMTParser::ParserPtr parser = SOMTParser::newParser();

    test_signed_division_remainder_and_modulo(parser);
    test_bitvector_constants(parser);
    test_bv_const_value_and_utils_nat(parser);
    test_bv_logical_operations(parser);
    test_bv_arithmetic_operations(parser);
    test_bv_comparison_operations(parser);
    test_value_bv_operators_ir();
    test_bv_arithmetic_correctness(parser);
    test_bv_large_width_gmp_path(parser);
    test_signed_mod_divisor_sign(parser);

    return 0;
}
