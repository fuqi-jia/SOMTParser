// Boolean constants are operands of equality and pairwise distinctness, not
// neutral elements. Check the DAG against an independent truth-table oracle so
// that the parser's own evaluator cannot hide a construction error.
#include "somtparser/parser.h"
#include "test_helpers.h"

#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace SOMTParser;

namespace {

void configure(const ParserPtr& parser, bool preserve) {
    parser->getOptions()->setEvaluateUseFloating(false);
    if (preserve) parser->getOptions()->preserveOperators({NODE_KIND::NT_EQ, NODE_KIND::NT_DISTINCT});
}

bool truth(const Node& node, unsigned assignment) {
    struct Frame { Node node; size_t next = 0; };
    std::vector<Frame> stack = {{node}};
    std::unordered_map<const DAGNode*, bool> values;
    while (!stack.empty()) {
        auto& frame = stack.back();
        const Node current = frame.node;
        VERIFY(current && current->getSort()->isBool());
        if (values.count(current.get())) { stack.pop_back(); continue; }
        if (current->isTrue() || current->isFalse()) {
            values.emplace(current.get(), current->isTrue());
            stack.pop_back();
            continue;
        }
        if (current->isVar()) {
            VERIFY(current->getName() == "p" || current->getName() == "q");
            values.emplace(current.get(),
                (assignment & (current->getName() == "p" ? 1u : 2u)) != 0);
            stack.pop_back();
            continue;
        }
        if (frame.next < current->getChildrenSize()) {
            const Node child = current->getChild(frame.next++);
            if (!values.count(child.get())) stack.push_back({child});
            continue;
        }
        const auto childValue = [&](size_t index) {
            return values.at(current->getChild(index).get());
        };
        bool result;
        if (current->isNot()) {
            VERIFY(current->getChildrenSize() == 1);
            result = !childValue(0);
        } else if (current->isAnd() || current->isOr()) {
            result = current->isAnd();
            for (size_t i = 0; i < current->getChildrenSize(); ++i) {
                if (childValue(i) != current->isAnd()) {
                    result = current->isOr();
                    break;
                }
            }
        } else {
            VERIFY(current->isEq() || current->isDistinct());
            VERIFY(current->getChildrenSize() >= 2);
            result = true;
            for (size_t i = 0; result && i < current->getChildrenSize(); ++i) {
                for (size_t j = i + 1; j < current->getChildrenSize(); ++j) {
                    if ((childValue(i) == childValue(j)) != current->isEq()) {
                        result = false;
                        break;
                    }
                }
            }
        }
        values.emplace(current.get(), result);
        stack.pop_back();
    }
    return values.at(node.get());
}

bool expectTruth(const Node& node, unsigned assignment, bool expected,
                 const std::string& source) {
    if (truth(node, assignment) == expected) return true;
    std::cerr << "Wrong Boolean value for " << source << " at assignment "
              << assignment << ": " << node->toString() << '\n';
    return false;
}

void expectOperands(const Node& node, const std::vector<Node>& operands,
                    bool equality) {
    VERIFY(equality ? node->isEq() : node->isDistinct());
    VERIFY(node->getChildrenSize() == operands.size());
    std::multiset<std::string> expected, actual;
    for (const auto& operand : operands) expected.insert(operand->toString());
    for (const auto& child : node->getChildren()) actual.insert(child->toString());
    VERIFY(actual == expected);
}

void testWitnesses() {
    bool passed = true;
    for (bool preserve : {false, true}) {
        for (const char* source : {"(= true false false)",
                                   "(distinct false false true)"}) {
            auto parser = newParser();
            configure(parser, preserve);
            const std::string script = std::string("(set-logic ALL)\n(assert ") +
                                       source + ")\n(check-sat)\n";
            // Exercise the same command-at-a-time API as the direct frontend.
            VERIFY(parser->loadStr(script));
            VERIFY(parser->nextCommand().type == CMD_TYPE::CT_SET_LOGIC);
            const auto command = parser->nextCommand();
            VERIFY(command.type == CMD_TYPE::CT_ASSERT);
            passed &= expectTruth(command.expr, 0, false, source);
            VERIFY(parser->nextCommand().type == CMD_TYPE::CT_CHECK_SAT);
            VERIFY(parser->nextCommand().type == CMD_TYPE::CT_EOF);
            VERIFY(parser->getAssertions().size() == 1);
            passed &= expectTruth(parser->getAssertions()[0], 0, false, source);

            auto again = newParser();
            configure(again, preserve);
            VERIFY(again->parseStr(parser->dumpSMT2()));
            VERIFY(again->getAssertions().size() == 1);
            passed &= expectTruth(again->getAssertions()[0], 0, false, source);
        }
    }
    VERIFY(passed);
}

void testTruthTables() {
    const std::vector<std::string> names = {"false", "true", "p", "q"};
    for (bool preserve : {false, true}) {
        auto parser = newParser();
        configure(parser, preserve);
        const std::vector<Node> atoms = {parser->mkFalse(), parser->mkTrue(),
                                        parser->mkVarBool("p"), parser->mkVarBool("q")};
        // All ordered tuples of 2..4 operands: includes constants in every
        // position, duplicates, and symbolic operands under all assignments.
        for (unsigned arity = 2; arity <= 4; ++arity) {
            for (unsigned tuple = 0; tuple < (1u << (2 * arity)); ++tuple) {
                std::vector<Node> operands;
                std::vector<unsigned> indices;
                unsigned remaining = tuple;
                for (unsigned i = 0; i < arity; ++i) {
                    indices.push_back(remaining % 4);
                    operands.push_back(atoms[remaining % 4]);
                    remaining /= 4;
                }
                for (bool equality : {true, false}) {
                    std::string source = equality ? "(=" : "(distinct";
                    for (unsigned index : indices) source += " " + names[index];
                    source += ")";
                    const Node built = equality ? parser->mkEq(operands)
                                                : parser->mkDistinct(operands);
                    const Node parsed = parser->mkExpr(source);
                    auto again = newParser();
                    configure(again, preserve);
                    VERIFY(again->parseStr("(set-logic ALL)\n"
                                           "(declare-const p Bool)\n"
                                           "(declare-const q Bool)\n(assert " +
                                           parser->toString(parsed) + ")\n(check-sat)\n"));
                    VERIFY(again->getAssertions().size() == 1);
                    for (unsigned assignment = 0; assignment < 4; ++assignment) {
                        unsigned trueCount = 0;
                        for (unsigned index : indices) {
                            trueCount += index == 1 ||
                                         (index == 2 && (assignment & 1)) ||
                                         (index == 3 && (assignment & 2));
                        }
                        const bool expected = equality ? trueCount == 0 || trueCount == arity
                                                       : arity == 2 && trueCount == 1;
                        VERIFY(expectTruth(built, assignment, expected, source));
                        VERIFY(expectTruth(parsed, assignment, expected, source));
                        VERIFY(expectTruth(again->getAssertions()[0], assignment, expected, source));
                        auto model = std::make_shared<Model>();
                        model->add(atoms[2], assignment & 1 ? parser->mkTrue() : parser->mkFalse());
                        model->add(atoms[3], assignment & 2 ? parser->mkTrue() : parser->mkFalse());
                        const auto evaluated = parser->evaluate(built, model);
                        VERIFY(evaluated && evaluated->isCBool());
                        VERIFY(evaluated->isTrue() == expected);
                    }
                    if (preserve) {
                        expectOperands(built, operands, equality);
                        expectOperands(parsed, operands, equality);
                        expectOperands(again->getAssertions()[0], operands, equality);
                    }
                }
            }
        }
    }
}

void testLargeArity() {
    // Cover both sides of the builders' unsorted-node fast path (>100).
    for (bool preserve : {false, true}) {
        auto parser = newParser();
        configure(parser, preserve);
        for (size_t size : {100u, 101u, 102u}) {
            for (bool equality : {true, false}) {
                std::vector<Node> operands(size, equality ? parser->mkTrue() : parser->mkFalse());
                for (bool mixed : {false, true}) {
                    if (mixed) operands[size / 2] = equality ? parser->mkFalse() : parser->mkTrue();
                    const Node node = equality ? parser->mkEq(operands) : parser->mkDistinct(operands);
                    VERIFY(expectTruth(node, 0, equality && !mixed, "large-arity comparison"));
                    if (preserve) expectOperands(node, operands, equality);
                    auto again = newParser();
                    configure(again, preserve);
                    VERIFY(again->parseStr("(assert " + parser->toString(node) + ")"));
                    VERIFY(again->getAssertions().size() == 1);
                    VERIFY(expectTruth(again->getAssertions()[0], 0, equality && !mixed,
                                       "large-arity round trip"));
                }
            }
        }
    }
}

void testSimplification() {
    auto parser = newParser();
    const auto p = parser->mkVarBool("p");
    const auto q = parser->mkVarBool("q");
    const std::vector<Node> variables = {p, q};
    // Preserve the useful reductions, while making constant-containing n-ary
    // equality constrain every remaining operand to the constant's value.
    for (const char* source : {"(= true true true)", "(= false false false)"}) {
        VERIFY(parser->mkExpr(source)->isTrue());
    }
    for (const char* source : {"(= true false false)", "(distinct false false true)",
                               "(distinct false false)", "(distinct p q true)",
                               "(distinct p q p)"}) {
        VERIFY(parser->mkExpr(source)->isFalse());
    }
    VERIFY(parser->mkExpr("(= true true p)") == p);
    VERIFY(parser->mkExpr("(= false false p)") == parser->mkNot(p));
    VERIFY(parser->mkExpr("(distinct false p)") == p);
    VERIFY(parser->mkExpr("(distinct p false)") == p);
    VERIFY(parser->mkExpr("(distinct true p)") == parser->mkNot(p));
    VERIFY(parser->mkExpr("(distinct p true)") == parser->mkNot(p));
    VERIFY(parser->mkExpr("(distinct false true)")->isTrue());
    VERIFY(parser->mkExpr("(= true p q)") == parser->mkAnd(variables));
    VERIFY(parser->mkExpr("(= false p q)") == parser->mkNot(parser->mkOr(variables)));
}

void testOtherSorts() {
    // The shared builders must still implement equality and pairwise
    // distinctness over non-Boolean sorts.
    for (bool preserve : {false, true}) {
        auto parser = newParser();
        configure(parser, preserve);
        for (const auto& test : std::vector<std::pair<std::string, bool>>{
                 {"(= 7 7 7)", true}, {"(= 7 7 8)", false},
                 {"(distinct 1 2 3)", true}, {"(distinct 1 2 1)", false},
                 {"(= #b01 #b01 #b01)", true}, {"(distinct #b01 #b10 #b01)", false},
                 {"(= \"a\" \"a\" \"a\")", true}, {"(distinct \"a\" \"b\" \"a\")", false}}) {
            const auto node = parser->mkExpr(test.first);
            const auto result = parser->evaluate(node, std::make_shared<Model>());
            VERIFY(result && result->isCBool());
            VERIFY(result->isTrue() == test.second);
        }
    }
}

void testConstantSortValidation() {
    // Constant folding must not accept an ill-typed operand, including one
    // after constants that already decide a Boolean relation's truth value.
    for (bool preserve : {false, true}) {
        for (const char* source : {"(= true false \"x\")", "(= true false #b1)",
                                   "(distinct true false \"x\")",
                                   "(distinct true false #b1)"}) {
            auto parser = newParser();
            configure(parser, preserve);
            VERIFY(!parser->parseStr(std::string("(assert ") + source + ")"));
        }
    }
}

} // namespace

int main() {
    testWitnesses();
    testTruthTables();
    testLargeArity();
    testSimplification();
    testOtherSorts();
    testConstantSortValidation();
    std::cout << "Boolean equality/distinct regression tests passed.\n";
}
