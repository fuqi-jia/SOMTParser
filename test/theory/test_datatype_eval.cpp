#include <iostream>
#include <string>

#include "somtparser/frontend/parser.h"
#include "somtparser/ir/dag.h"
#include "../test_helpers.h"

int main() {
    using namespace SOMTParser;

    ParserPtr parser = newParser();
    bool parsed = parser->parseStr(R"(
; Parse regression: declare-datatypes (Either: left / right, Int selectors only)
(set-logic ALL)

(declare-datatypes ((Either 0)) (((left (lv Int)) (right (rv Int)))))

(assert (is-left (left 7)))
(assert (not (is-right (left 7))))
(assert (is-right (right 3)))
(assert (not (is-left (right 3))))
(assert (= (lv (left 42)) 42))
(assert (= (rv (right 99)) 99))

(check-sat)
(exit)
)");
    if (!parsed) {
        std::cerr << "test_datatype_eval: failed to parse inline datatypes\n";
        return 1;
    }
    std::cout << "parsed inline datatypes\n";

    ModelPtr model = newModel();

    {
        auto e = parser->mkExpr("(left 7)");
        VERIFY(e && !e->isErr());
        VERIFY(e->isConstructorApp());
        VERIFY(e->getName() == "left");
        {
            std::string d = dumpSMTLIB2(e);
            VERIFY(d.find("NT_DT") == std::string::npos);
        }
        auto ev = parser->evaluate(e, model);
        VERIFY(ev && ev->isConstructorApp());
        VERIFY(ev->getName() == "left");
        VERIFY(ev->getChildrenSize() == 1);
        VERIFY(parser->toString(ev->getChild(0)) == "7");
    }

    {
        auto e = parser->mkExpr("(lv (left 7))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        VERIFY(ev && parser->toString(ev) == "7");
    }

    {
        auto e = parser->mkExpr("(is-left (left 7))");
        VERIFY(e && !e->isErr());
        VERIFY(dumpSMTLIB2(e).find("NT_DT") == std::string::npos);
        auto ev = parser->evaluate(e, model);
        VERIFY(ev && ev->isTrue());
    }

    {
        auto e = parser->mkExpr("(is-right (left 7))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        VERIFY(ev && ev->isFalse());
    }

    {
        auto e = parser->mkExpr("(lv (right 3))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        VERIFY(ev && !parser->toString(ev).empty());
        VERIFY(parser->toString(ev) != "3");
    }

    // ─── DT structural equality ─────────────────────────────────────────
    {
        auto e = parser->mkExpr("(= (left 7) (left 7))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (= (left 7) (left 7)) => " << parser->toString(ev) << "\n";
        VERIFY(ev && ev->isTrue());
    }
    {
        auto e = parser->mkExpr("(= (left 7) (left 8))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (= (left 7) (left 8)) => " << parser->toString(ev) << "\n";
        VERIFY(ev && ev->isFalse());
    }
    {
        auto e = parser->mkExpr("(= (left 7) (right 7))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (= (left 7) (right 7)) => " << parser->toString(ev) << "\n";
        VERIFY(ev && ev->isFalse());
    }
    {
        auto e = parser->mkExpr("(distinct (left 1) (left 2))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (distinct (left 1) (left 2)) => " << parser->toString(ev) << "\n";
        VERIFY(ev && ev->isTrue());
    }
    {
        auto e = parser->mkExpr("(distinct (left 1) (left 1))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (distinct (left 1) (left 1)) => " << parser->toString(ev) << "\n";
        VERIFY(ev && ev->isFalse());
    }

    std::cout << "test_datatype_eval: basic DT assertions passed\n";

    // ─── Match expression tests ─────────────────────────────────────────
    {
        // The same pattern name is local to each branch and is rebound after
        // the first branch's scope has been popped.
        auto e = parser->mkExpr("(match (left 42) (((left x) x) ((right x) x)))");
        VERIFY(e && !e->isErr());
        {
            std::string d = dumpSMTLIB2(e);
            VERIFY(d.find("NT_DT") == std::string::npos);
            // SMT-LIB: (match s ( (<pat> <body>) ... )) — nested parens, not flat match args
            VERIFY(d.find("((left") != std::string::npos);
            auto roundtrip = parser->mkExpr(d);
            VERIFY(roundtrip && !roundtrip->isErr());
            VERIFY(dumpSMTLIB2(roundtrip) == d);
        }
        auto ev = parser->evaluate(e, model);
        std::cout << "  (match (left 42) ...) => " << parser->toString(ev) << "\n";
        VERIFY(ev && parser->toString(ev) == "42");
    }
    {
        // Constructor and catch-all patterns share the standard outer case-list.
        auto e = parser->mkExpr("(match (left 42) (((left x) x) (whole 0)))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        VERIFY(ev && parser->toString(ev) == "42");
    }
    {
        auto e = parser->mkExpr("(match (right 99) (((left x) x) ((right y) y)))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (match (right 99) ...) => " << parser->toString(ev) << "\n";
        VERIFY(ev && parser->toString(ev) == "99");
    }
    {
        // match with arithmetic in body
        auto e = parser->mkExpr("(match (left 5) (((left x) (+ x 10)) ((right y) (- y 1))))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (match (left 5) with +10) => " << parser->toString(ev) << "\n";
        VERIFY(ev && parser->toString(ev) == "15");
    }
    {
        // match right branch with arithmetic
        auto e = parser->mkExpr("(match (right 5) (((left x) (+ x 10)) ((right y) (- y 1))))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (match (right 5) with -1) => " << parser->toString(ev) << "\n";
        VERIFY(ev && parser->toString(ev) == "4");
    }
    {
        // nested match: match result of a selector
        auto e = parser->mkExpr("(match (left 7) (((left x) (= x 7)) ((right y) false)))");
        VERIFY(e && !e->isErr());
        auto ev = parser->evaluate(e, model);
        std::cout << "  (match (left 7) eq check) => " << parser->toString(ev) << "\n";
        VERIFY(ev && ev->isTrue());
    }

    std::cout << "test_datatype_eval: match expression tests passed\n";

    // The case list is required and all branches must return the same sort.
    {
        ParserPtr empty_cases = newParser();
        VERIFY(!empty_cases->parseStr(R"(
(set-logic ALL)
(declare-datatypes ((Either 0)) (((left (lv Int)) (right (rv Int)))))
(assert (match (left 1) ()))
)"));
    }
    {
        // Whitespace and comments between the case-list delimiters still form
        // an empty (and therefore invalid) match.
        ParserPtr comment_empty_cases = newParser();
        VERIFY(!comment_empty_cases->parseStr(R"(
(set-logic ALL)
(declare-datatypes ((Either 0)) (((left (lv Int)) (right (rv Int)))))
(assert (match (left 1) (
  ; no match cases
)))
)"));
    }
    {
        ParserPtr mixed_results = newParser();
        VERIFY(!mixed_results->parseStr(R"(
(set-logic ALL)
(declare-datatypes ((Either 0)) (((left (lv Int)) (right (rv Int)))))
(assert (match (left 1) (((left x) x) ((right y) true))))
)"));
    }

    // ─── Recursive DT tests ─────────────────────────────────────────────
    {
        // Declare a recursive list datatype
        ParserPtr p2 = newParser();
        VERIFY(p2->parseStr("(set-logic ALL)"));
        VERIFY(p2->parseStr(
            "(declare-datatypes ((IntList 0)) (((cons (head Int) (tail IntList)) (nil))))"));
        ModelPtr m2 = newModel();

        // nil
        {
            auto e = p2->mkExpr("nil");
            VERIFY(e && !e->isErr());
            VERIFY(e->isConstructorApp());
            VERIFY(e->getName() == "nil");
        }
        // (cons 1 nil)
        {
            auto e = p2->mkExpr("(cons 1 nil)");
            VERIFY(e && !e->isErr());
            VERIFY(e->isConstructorApp());
            VERIFY(e->getName() == "cons");
            auto ev = p2->evaluate(e, m2);
            VERIFY(ev && ev->isConstructorApp());
        }
        // (head (cons 1 nil))
        {
            auto e = p2->mkExpr("(head (cons 1 nil))");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            VERIFY(ev && p2->toString(ev) == "1");
        }
        // (is-cons (cons 1 nil))
        {
            auto e = p2->mkExpr("(is-cons (cons 1 nil))");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            VERIFY(ev && ev->isTrue());
        }
        // (is-nil (cons 1 nil))
        {
            auto e = p2->mkExpr("(is-nil (cons 1 nil))");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            VERIFY(ev && ev->isFalse());
        }
        // (is-nil nil)
        {
            auto e = p2->mkExpr("(is-nil nil)");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            VERIFY(ev && ev->isTrue());
        }
        // Recursive equality: (= (cons 1 nil) (cons 1 nil))
        {
            auto e = p2->mkExpr("(= (cons 1 nil) (cons 1 nil))");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            std::cout << "  (= (cons 1 nil) (cons 1 nil)) => " << p2->toString(ev) << "\n";
            VERIFY(ev && ev->isTrue());
        }
        // Nested cons: (head (tail (cons 1 (cons 2 nil))))
        {
            auto e = p2->mkExpr("(head (tail (cons 1 (cons 2 nil))))");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            std::cout << "  (head (tail (cons 1 (cons 2 nil)))) => " << p2->toString(ev) << "\n";
            VERIFY(ev && p2->toString(ev) == "2");
        }
        // match on recursive DT
        {
            auto e = p2->mkExpr("(match (cons 42 nil) (((cons h t) h) (nil 0)))");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            std::cout << "  (match (cons 42 nil) ...) => " << p2->toString(ev) << "\n";
            VERIFY(ev && p2->toString(ev) == "42");
        }
        // match nil case
        {
            auto e = p2->mkExpr("(match nil (((cons h t) h) (nil 0)))");
            VERIFY(e && !e->isErr());
            auto ev = p2->evaluate(e, m2);
            std::cout << "  (match nil ...) => " << p2->toString(ev) << "\n";
            VERIFY(ev && p2->toString(ev) == "0");
        }

        std::cout << "test_datatype_eval: recursive DT tests passed\n";
    }

    // ─── SMT-LIB declare-datatype + ((_ is ctor) x) (SMTClaw / issues.md) ───
    {
        ParserPtr pdt = newParser();
        VERIFY(pdt->parseStr(
            "(set-logic QF_UFDT)\n"
            "(declare-datatype D ((a) (b)))\n"
            "(declare-fun x () D)\n"
            "(assert ((_ is a) x))\n"
            "(check-sat)\n"));
        VERIFY(pdt->getAssertions().size() >= 1);
        std::cout << "test_datatype_eval: declare-datatype + indexed is-tester passed\n";
    }
    {
        ParserPtr pdt2 = newParser();
        VERIFY(pdt2->parseStr(
            "(set-logic QF_DT)\n"
            "(declare-datatypes ((T 0)) (((c1) (c2))))\n"
            "(declare-fun v () T)\n"
            "(assert ((_ is c1) v))\n"));
        VERIFY(pdt2->getAssertions().size() >= 1);
        std::cout << "test_datatype_eval: declare-datatypes + ((_ is c1) v) passed\n";
    }

    // ─── isRecursiveDatatype + mkDefaultDTValue ─────────────────────────
    {
        // Non-recursive: enum-like DT with only nullary constructors
        ParserPtr pe = newParser();
        VERIFY(pe->parseStr("(set-logic ALL) (declare-datatypes ((Color 0)) (((red) (green) (blue))))"));
        auto vars = pe->getDatatypeVars();
        // No variables declared, but the sort should exist via getDeclaredSorts
        // Look up the Color sort by parsing a zero-arg constructor to find its sort
        auto red_node = pe->mkExpr("red");
        VERIFY(red_node && !red_node->isErr());
        auto color_sort = red_node->getSort();
        VERIFY(color_sort && color_sort->isDatatype());

        VERIFY(!pe->isRecursiveDatatype(color_sort));  // not recursive

        auto def = pe->mkDefaultDTValue(color_sort);
        VERIFY(def && !def->isErr());
        VERIFY(def->isConstructorApp());
        // Should pick the first nullary constructor ("red")
        VERIFY(def->getName() == "red");
        std::cout << "  mkDefaultDTValue(Color) => " << pe->toString(def) << "\n";

        std::cout << "test_datatype_eval: isRecursiveDatatype (non-recursive) passed\n";
    }
    {
        // Directly recursive: IntList = nil | (cons Int IntList)
        ParserPtr pr = newParser();
        VERIFY(pr->parseStr("(set-logic ALL)"
            "(declare-datatypes ((IntList 0)) (((cons (head Int) (tail IntList)) (nil))))"));
        auto nil_node = pr->mkExpr("nil");
        VERIFY(nil_node && !nil_node->isErr());
        auto list_sort = nil_node->getSort();
        VERIFY(list_sort && list_sort->isDatatype());

        VERIFY(pr->isRecursiveDatatype(list_sort));  // is recursive

        auto def = pr->mkDefaultDTValue(list_sort);
        VERIFY(def && !def->isErr());
        VERIFY(def->isConstructorApp());
        // nil is nullary → should be picked as default
        VERIFY(def->getName() == "nil");
        std::cout << "  mkDefaultDTValue(IntList) => " << pr->toString(def) << "\n";

        std::cout << "test_datatype_eval: isRecursiveDatatype (directly recursive) passed\n";
    }
    {
        // Non-trivial default: DT where first constructor takes an Int arg and no nullary
        // Shape = (circle Int)   (only one constructor with Int radius)
        ParserPtr ps = newParser();
        VERIFY(ps->parseStr("(set-logic ALL)"
            "(declare-datatypes ((Shape 0)) (((circle (radius Int)))))"));
        auto circ = ps->mkExpr("(circle 0)");
        VERIFY(circ && !circ->isErr());
        auto shape_sort = circ->getSort();
        VERIFY(shape_sort && shape_sort->isDatatype());

        VERIFY(!ps->isRecursiveDatatype(shape_sort));  // Int selector is not DT

        auto def = ps->mkDefaultDTValue(shape_sort);
        VERIFY(def && !def->isErr());
        VERIFY(def->isConstructorApp());
        VERIFY(def->getName() == "circle");
        // selector default for Int should be 0
        VERIFY(def->getChildrenSize() == 1);
        VERIFY(ps->toString(def->getChild(0)) == "0");
        std::cout << "  mkDefaultDTValue(Shape) => " << ps->toString(def) << "\n";

        std::cout << "test_datatype_eval: mkDefaultDTValue (non-nullary constructor) passed\n";
    }

    // ─── Parametric sort parsing (parseSort shared-Sort mutation) ───────
    {
        ParserPtr pp = newParser();
        VERIFY(pp->parseStr("(set-logic ALL)"));
        VERIFY(pp->parseStr("(declare-sort S 1)"));
        VERIFY(pp->parseStr("(define-sort SB () (S Bool))"));
        VERIFY(pp->parseStr("(declare-fun A () (S Bool))"));
        VERIFY(pp->parseStr("(declare-fun B () SB)"));

        auto vars = pp->getVariables();
        std::shared_ptr<SOMTParser::DAGNode> varA = nullptr;
        std::shared_ptr<SOMTParser::DAGNode> varB = nullptr;
        for (auto& v : vars) {
            if (v->getName() == "A") varA = v;
            if (v->getName() == "B") varB = v;
        }
        VERIFY(varA && varB);

        auto sortA = varA->getSort();
        auto sortB = varB->getSort();
        VERIFY(sortA && sortA->name == "S");
        VERIFY(sortB && sortB->name == "S");
        VERIFY(sortA->children.size() == 1);
        VERIFY(sortB->children.size() == 1);
        VERIFY(sortA->children[0]->isBool());
        VERIFY(sortB->children[0]->isBool());

        // Parse a second parametric sort (S Int) — must NOT corrupt the sort of A
        VERIFY(pp->parseStr("(declare-fun C () (S Int))"));
        auto vars2 = pp->getVariables();
        std::shared_ptr<SOMTParser::DAGNode> varC = nullptr;
        for (auto& v : vars2) {
            if (v->getName() == "C") varC = v;
        }
        VERIFY(varC);
        auto sortC = varC->getSort();
        VERIFY(sortC && sortC->name == "S");
        VERIFY(sortC->children.size() == 1);
        VERIFY(sortC->children[0]->isInt());

        // A and B must still have Bool child, not Int
        VERIFY(varA->getSort()->children[0]->isBool());
        VERIFY(varB->getSort()->children[0]->isBool());

        std::cout << "test_datatype_eval: parametric sort parsing passed\n";
    }

    std::cout << "test_datatype_eval: all assertions passed\n";
    return 0;
}
