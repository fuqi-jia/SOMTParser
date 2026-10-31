#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <string>
#include <vector>

using namespace SOMTParser;
using Node = std::shared_ptr<DAGNode>;

static Node raw(const ParserPtr& parser, const std::shared_ptr<Sort>& sort,
                NODE_KIND kind, std::vector<Node> children, const std::string& name = {}) {
    return parser->getNodeManager()->createNode(sort, kind,
        name.empty() ? kindToString(kind) : name, std::move(children));
}

static void checkDeepAndShared() {
    auto parser = newParser();
    auto b = parser->mkVarBool("b"), x = parser->mkVarInt("x");
    auto model = newModel();
    model->add(b, parser->mkTrue());
    model->add(x, parser->mkConstInt(2));
    auto boolean = b, arithmetic = x;
    auto one = parser->mkConstInt(1);
    for(int i = 0; i < 20000; ++i) {
        boolean = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_NOT, {boolean});
        arithmetic = raw(parser, SortManager::INT_SORT, NODE_KIND::NT_ADD, {arithmetic, one});
    }
    VERIFY(parser->evaluate(boolean, model)->isTrue());
    VERIFY(parser->toInt(parser->evaluate(arithmetic, model)) == Integer(20002));
    model->add(b, parser->mkFalse());
    model->add(x, parser->mkConstInt(3));
    VERIFY(parser->evaluate(boolean, model)->isFalse());
    VERIFY(parser->toInt(parser->evaluate(arithmetic, model)) == Integer(20003));

    // Forty shared doublings have exponentially many paths but only forty
    // operations; each node is evaluated once under this model.
    auto shared = x;
    for(int i = 0; i < 40; ++i) shared = raw(parser, SortManager::INT_SORT, NODE_KIND::NT_ADD, {shared, shared});
    VERIFY(parser->toInt(parser->evaluate(shared, model)) == Integer("3298534883328"));

    auto unknown = parser->mkVarBool("unassigned");
    VERIFY(parser->evaluate(unknown, model) == unknown);
    auto empty = newModel();
    VERIFY(parser->evaluate(boolean, empty) == boolean);
}

static void checkShortCircuitAndRecovery() {
    auto parser = newParser();
    auto b = parser->mkVarBool("b");
    auto model = newModel();
    model->add(b, parser->mkTrue());
    // Deliberately malformed unselected work: traversing it would invoke a
    // unary handler with no operand. Short-circuiting must avoid it entirely.
    auto poison = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_NOT, {});
    auto conjunction = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_AND, {parser->mkFalse(), poison});
    auto disjunction = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_OR, {parser->mkTrue(), poison});
    auto distinct = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_DISTINCT_BOOL,
                        {parser->mkTrue(), parser->mkTrue(), poison});
    VERIFY(parser->evaluate(conjunction, model)->isFalse());
    VERIFY(parser->evaluate(disjunction, model)->isTrue());
    VERIFY(parser->evaluate(distinct, model)->isFalse());

    // An unexpanded let used to recursively ask to evaluate itself forever.
    // The worklist rejects that cycle, and the public wrapper retains the
    // unevaluated term. Its session must not leak into a later valid call.
    parser->getOptions()->parsing_preserve_let = false;
    auto unexpanded = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_LET, {b});
    VERIFY(parser->evaluate(unexpanded, model) == unexpanded);
    VERIFY(parser->evaluate(parser->mkNot(b), model)->isFalse());

    auto x = parser->mkVarInt("x");
    auto application = raw(parser, SortManager::INT_SORT, NODE_KIND::NT_UF_APPLY, {x}, "f");
    model->add(x, parser->mkConstInt(3));
    model->add("uf@@f@@x", parser->mkConstInt(7));
    model->add("uf@@f@@3", parser->mkConstInt(8));
    VERIFY(parser->toInt(parser->evaluate(application, model)) == Integer(7));
}

static void checkFunctionAndMatchBodies() {
    auto parser = newParser();
    auto x = parser->mkVarInt("x");
    auto parameter = parser->mkFunParamVar(SortManager::INT_SORT, "parameter");
    auto function = parser->mkFuncDef("identity", {parameter}, SortManager::INT_SORT, parameter);
    auto root = x;
    for(int i = 0; i < 12000; ++i)
        root = raw(parser, SortManager::INT_SORT, NODE_KIND::NT_FUNC_APPLY, {function, root}, "identity");
    auto model = newModel();
    model->add(x, parser->mkConstInt(17));
    parser->getOptions()->setExpandFunctions(false);
    VERIFY(parser->toInt(parser->evaluate(root, model)) == Integer(17));
    VERIFY(!parser->getOptions()->getExpandFunctions());

    VERIFY(parser->parseStr("(declare-datatype List ((nil) (cons (head Int) (tail List))))"));
    auto match = parser->mkExpr("(match (cons 4 nil) ((nil 0) ((cons h t) (+ h 1))))");
    VERIFY(parser->toInt(parser->evaluate(match, model)) == Integer(5));
    parser->getOptions()->parsing_preserve_let = true;
    auto let = parser->mkExpr("(let ((a 3)) (let ((b (+ a 2))) (+ a b)))");
    VERIFY(parser->toInt(parser->evaluate(let, model)) == Integer(8));
}

static void checkTypedComparisonDispatch() {
    auto parser = newParser();
    auto empty = newModel();
    for(const auto kind : {NODE_KIND::NT_EQ, NODE_KIND::NT_EQ_BOOL, NODE_KIND::NT_EQ_OTHER}) {
        const auto left = kind == NODE_KIND::NT_EQ_OTHER ? parser->mkConstInt(1) : parser->mkTrue();
        const auto right = kind == NODE_KIND::NT_EQ_OTHER ? parser->mkConstInt(2) : parser->mkFalse();
        VERIFY(parser->evaluate(raw(parser, SortManager::BOOL_SORT, kind,
            {left, right}), empty)->isFalse());
        VERIFY(parser->evaluate(raw(parser, SortManager::BOOL_SORT, kind,
            {left, left}), empty)->isTrue());
    }
    for(const auto kind : {NODE_KIND::NT_DISTINCT, NODE_KIND::NT_DISTINCT_BOOL, NODE_KIND::NT_DISTINCT_OTHER}) {
        const auto left = kind == NODE_KIND::NT_DISTINCT_OTHER ? parser->mkConstInt(1) : parser->mkTrue();
        const auto right = kind == NODE_KIND::NT_DISTINCT_OTHER ? parser->mkConstInt(2) : parser->mkFalse();
        VERIFY(parser->evaluate(raw(parser, SortManager::BOOL_SORT, kind,
            {left, right}), empty)->isTrue());
        VERIFY(parser->evaluate(raw(parser, SortManager::BOOL_SORT, kind,
            {left, left}), empty)->isFalse());
    }
}

static void checkDeepDatatypeValues() {
    auto parser = newParser();
    auto sort = std::make_shared<Sort>(SORT_KIND::SK_DATATYPE, "Value");
    auto left = raw(parser, sort, NODE_KIND::NT_DT_CONSTRUCTOR, {parser->mkConstInt(1)}, "leaf");
    auto right = raw(parser, sort, NODE_KIND::NT_DT_CONSTRUCTOR, {parser->mkConstInt(2)}, "leaf");
    for(int i = 0; i < 20000; ++i) {
        left = raw(parser, sort, NODE_KIND::NT_DT_CONSTRUCTOR, {left}, "next");
        right = raw(parser, sort, NODE_KIND::NT_DT_CONSTRUCTOR, {right}, "next");
    }
    VERIFY(left->isDtGroundValue() && right->isDtGroundValue());
    auto empty = newModel();
    auto unequal = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_EQ_OTHER, {left, right});
    auto equal = raw(parser, SortManager::BOOL_SORT, NODE_KIND::NT_EQ_OTHER, {left, left});
    VERIFY(parser->evaluate(unequal, empty)->isFalse());
    VERIFY(parser->evaluate(equal, empty)->isTrue());
    auto non_ground = raw(parser, sort, NODE_KIND::NT_DT_CONSTRUCTOR, {parser->mkVarInt("free")}, "leaf");
    VERIFY(!non_ground->isDtGroundValue());
}

int main() {
    checkTypedComparisonDispatch();
    checkDeepAndShared();
    checkShortCircuitAndRecovery();
    checkFunctionAndMatchBodies();
    checkDeepDatatypeValues();
    return 0;
}
