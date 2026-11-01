#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <exception>
#include <string>
#include <vector>

using namespace SOMTParser;

static std::string nest(const std::string& prefix, const std::string& leaf,
                        const std::string& suffix, std::size_t depth) {
    std::string text;
    text.reserve(depth * (prefix.size() + suffix.size()) + leaf.size());
    for (std::size_t i = 0; i < depth; ++i) text += prefix;
    text += leaf;
    for (std::size_t i = 0; i < depth; ++i) text += suffix;
    return text;
}

static bool rejects(const ParserPtr& parser, const std::string& expression) {
    try {
        const auto result = parser->mkExpr(expression);
        return !result || result->isErr();
    } catch (const std::exception&) {
        return true;
    }
}

static void datatype(const ParserPtr& parser) {
    VERIFY(parser->parseStr(
        "(declare-datatypes ((L 0)) (((nil) (cons (head Int) (tail L)))))\n"
        "(declare-const n L)\n(declare-const x Int)\n"));
}

static void checkDeepTerms() {
    constexpr std::size_t depth = 20000;
    {
        auto parser = newParser();
        auto result = parser->mkExpr(nest("(forall ((x Bool)) ", "x", ")", depth));
        for (std::size_t i = 0; i < depth; ++i) {
            VERIFY(result->getKind() == NODE_KIND::NT_FORALL);
            VERIFY(result->getChildrenSize() == 2);
            VERIFY(result->getChild(1)->getSort()->isBool());
            result = result->getChild(0);
        }
        VERIFY(result->isQuantVar());
        VERIFY(!parser->getSymbolManager()->hasQuantVar("x"));
        VERIFY(!parser->getSymbolManager()->hasLet("x"));
    }
    for (bool preserve : {false, true}) {
        auto parser = newParser();
        parser->setOption("keep_let", preserve);
        VERIFY(parser->getOptions()->getKeepLet() == preserve);
        // A let in the RHS used to recurse even when adjacent body-lets were
        // handled iteratively by the old helper.
        auto result = parser->mkExpr(nest("(let ((x ", "1", ")) x)", depth));
        if (preserve) {
            for (std::size_t i = 0; i < depth; ++i) {
                VERIFY(result->isLetChain());
                VERIFY(result->getChildrenSize() == 2);
                const auto binding = result->getChild(0)->getChild(0);
                VERIFY(result->getChild(1) == binding);
                result = binding->getChild(0);
            }
        }
        VERIFY(parser->toString(result) == "1");
        VERIFY(!parser->getSymbolManager()->hasLet("x"));
    }
    {
        auto parser = newParser();
        parser->setOption("keep_let", true);
        VERIFY(parser->getOptions()->getKeepLet());
        auto result = parser->mkExpr(nest("(let ((x 1)) ", "x", ")", depth));
        VERIFY(result->isLetChain());
        VERIFY(result->getChildrenSize() == depth + 1); // Preserve the flat chain API.
        VERIFY(result->getChild(static_cast<int>(depth)) ==
               result->getChild(static_cast<int>(depth - 1))->getChild(0));
    }
    for (bool preserve : {false, true}) {
        auto parser = newParser();
        parser->setOption("preserve_annotations", preserve);
        auto result = parser->mkExpr(nest("(! ", "true", " :qid q)", depth));
        if (preserve) {
            for (std::size_t i = 0; i < depth; ++i) {
                VERIFY(result->getKind() == NODE_KIND::NT_ATTRIBUTE);
                result = result->getChild(0);
            }
        }
        VERIFY(parser->toString(result) == "true");
    }
    {
        auto parser = newParser();
        datatype(parser);
        auto result = parser->mkExpr(nest("(match n ((nil ", "false", ")))", depth));
        for (std::size_t i = 0; i < depth; ++i) {
            VERIFY(result->isMatchApp());
            VERIFY(result->getChildrenSize() == 3);
            result = result->getChild(2);
        }
        VERIFY(parser->toString(result) == "false");
    }
    {
        auto parser = newParser();
        // Each array has a scalar element sort, so this isolates expression
        // continuations from independently tested deep-sort parsing.
        auto result = parser->mkExpr(nest("(select ((as const (Array Int Int)) ",
                                          "0", ") 0)", depth));
        VERIFY(result && !result->isErr());
        VERIFY(result->getSort()->isInt());
    }
    {
        auto parser = newParser();
        parser->setOption("keep_let", false);
        VERIFY(!parser->getOptions()->getKeepLet());
        const auto sign = nest("(let ((s ", "#b0", ")) s)", depth);
        const auto fp = parser->mkExpr("(fp " + sign + " #b00000000 #b00000000000000000000000)");
        VERIFY(fp && !fp->isErr() && fp->getSort()->isFp());
        const auto polynomial = nest("(let ((p ", "poly_variable", ")) p)", depth);
        const auto algebraic = parser->mkExpr("(_ real_algebraic_number <" + polynomial
                                              + ", ((/ 3 2), (/ 7 4))>)");
        VERIFY(algebraic->isCRealAlgebraicNumber());
        VERIFY(algebraic->getChild(0)->getSort()->isReal());
        VERIFY(rejects(parser, "fresh_unknown_after_algebraic"));
    }
}

static void checkLexicalSemantics() {
    {
        auto parser = newParser();
        const auto interval = parser->mkExpr("(root-of-with-interval (coeffs 1 (- 2)) 0 3)");
        VERIFY(interval->isCRootOfWithInterval() && interval->getChildrenSize() == 4);
        const auto wrapped = parser->mkExpr("((root-of-with-interval (coeffs 1 (- 2)) 0 3))");
        VERIFY(wrapped == interval);
        const auto algebraic = parser->mkExpr("(_ real_algebraic_number (+ root_parameter 1) 0 3)");
        VERIFY(algebraic->isCRealAlgebraicNumber() && algebraic->getChildrenSize() == 3);
        VERIFY(parser->parseStr("(assert (= ((root-obj (+ (^ root_parameter 2) (- 3)) 1)) 1.0))\n"));
        VERIFY(rejects(parser, "unknown_after_root"));
    }
    for (bool preserve : {false, true}) {
        auto parser = newParser();
        datatype(parser);
        parser->setOption("keep_let", preserve);
        VERIFY(parser->getOptions()->getKeepLet() == preserve);
        const auto global = parser->getSymbolManager()->getVar("x");
        const auto parallel = parser->mkExpr("(let ((x 1) (y x)) (let ((x 2)) y))");
        if (preserve) {
            VERIFY(parallel->isLetChain() && parallel->getChildrenSize() == 3);
            const auto y = parallel->getChild(0)->getChild(1);
            VERIFY(y->getChild(0) == global);
            VERIFY(parallel->getChild(2) == y);
        } else VERIFY(parallel == global);
        const auto quantifier = parser->mkExpr(
            "(forall ((x Int)) (and (forall ((x Bool)) x) (= x 0)))");
        const auto body = quantifier->getChild(0);
        VERIFY(quantifier->getChild(1)->getSort()->isInt());
        // Commutative builders canonicalize AND and equality operands. Locate
        // their roles instead of assuming the source child order survives.
        VERIFY(body->isAnd() && body->getChildrenSize() == 2);
        std::shared_ptr<DAGNode> inner, equality;
        for (const auto& child : body->getChildren()) {
            if (child->getKind() == NODE_KIND::NT_FORALL) inner = child;
            if (child->isEq()) equality = child;
        }
        VERIFY(inner && equality);
        VERIFY(inner->getChild(1)->getSort()->isBool());
        VERIFY(inner->getChild(0) == inner->getChild(1));
        VERIFY(equality->getChildrenSize() == 2);
        VERIFY(equality->getChild(0) == quantifier->getChild(1)
               || equality->getChild(1) == quantifier->getChild(1));
        VERIFY(inner->getChild(1) != quantifier->getChild(1));
        const auto match = parser->mkExpr("(match n (((cons x xs) x) (nil x)))");
        VERIFY(match->getChild(2) == match->getChild(1)->getChild(0));
        VERIFY(match->getChild(4) == global);
        VERIFY(parser->mkExpr("x") == global);
        VERIFY(!parser->getSymbolManager()->hasLet("x"));
        VERIFY(!parser->getSymbolManager()->hasQuantVar("x"));
    }
    {
        auto parser = newParser();
        parser->setOption("keep_let", false);
        VERIFY(!parser->getOptions()->getKeepLet());
        const auto inner_let = parser->mkExpr("(forall ((x Int)) (let ((x true)) x))");
        VERIFY(inner_let->getChild(1)->getSort()->isInt());
        VERIFY(parser->toString(inner_let->getChild(0)) == "true");
        const auto inner_quant = parser->mkExpr("(let ((x true)) (forall ((x Int)) (= x 0)))");
        const auto equality = inner_quant->getChild(0);
        VERIFY(equality->isEq() && equality->getChildrenSize() == 2);
        VERIFY(equality->getChild(0) == inner_quant->getChild(1)
               || equality->getChild(1) == inner_quant->getChild(1));
    }
    {
        auto parser = newParser();
        parser->setOption("preserve_annotations", true);
        VERIFY(parser->parseStr("(declare-fun f (Int) Int)\n"));
        const std::string text = "(forall ((x Int)) (! (> (f x) 0) :pattern ((f x)) :no-pattern (f x) :weight 5 :qid q))";
        VERIFY(parser->toString(parser->mkExpr(text)) == text);
        // Unknown attributes remain skippable even with quoted parentheses.
        VERIFY(parser->toString(parser->mkExpr("(! true :unknown (|)| \"(\" (nested)))")) == "true");
        VERIFY(parser->parseStr("(assert (! true :named named_true))\n"));
        VERIFY(parser->getNamedAssertions().count("named_true") == 1);
    }
}

static void checkErrorRecovery() {
    for (bool preserve : {false, true}) {
        auto parser = newParser();
        datatype(parser);
        parser->setOption("keep_let", preserve);
        VERIFY(parser->getOptions()->getKeepLet() == preserve);
        parser->setOption("preserve_annotations", true);
        const auto global = parser->getSymbolManager()->getVar("x");
        for (const auto& text : std::vector<std::string>{
            "(let ((x 1) (x 2)) x)", "(let () x)", "(let ((x 1)))",
            "(forall ((x Bool)) (let ((z 1)) missing_in_body))",
            "(match n (((cons x xs) missing_in_case) (nil 0)))",
            "(match n (((cons x xs) x) (nil true)))",
            "(! true :pattern ((missing_function x)))",
            "((as const (Array Int Int)) (let ((z 1)) missing_array_value))",
            "(fp #b0 #b00000000)",
            "(_ real_algebraic_number (+ algebraic_parameter 1) 0)"}) {
            VERIFY(rejects(parser, text));
            VERIFY(!parser->getSymbolManager()->hasLet("x"));
            VERIFY(!parser->getSymbolManager()->hasLet("z"));
            VERIFY(!parser->getSymbolManager()->hasQuantVar("x"));
            VERIFY(!parser->getSymbolManager()->hasQuantVar("xs"));
            VERIFY(parser->mkExpr("x") == global);
            const auto valid = parser->mkExpr("(let ((fresh 1)) fresh)");
            VERIFY(valid && !valid->isErr());
            VERIFY(!parser->getSymbolManager()->hasLet("fresh"));
        }
        VERIFY(rejects(parser, "fresh_unknown_after_failure"));
        VERIFY(parser->mkExpr("true")->isCBool());
    }
}

int main() {
    checkLexicalSemantics();
    checkErrorRecovery();
    checkDeepTerms();
    return 0;
}
