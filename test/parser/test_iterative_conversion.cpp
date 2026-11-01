#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <cstdint>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace SOMTParser;
using Node = std::shared_ptr<DAGNode>;

static Node raw(const ParserPtr& parser, NODE_KIND kind, std::vector<Node> children) {
    return parser->getNodeManager()->createNode(SortManager::BOOL_SORT, kind,
                                                kindToString(kind), std::move(children));
}

static void checkDeepWalks() {
    auto parser = newParser();
    auto x = parser->mkVarInt("x");
    auto atom = parser->mkGt(x, parser->mkConstInt(0));
    auto root = atom;
    for(int i = 0; i < 20000; ++i) root = raw(parser, NODE_KIND::NT_NOT, {root});
    std::unordered_set<Node> atoms, variables, assignable;
    parser->collectAtoms(root, atoms);
    parser->collectVars(root, variables);
    parser->collectAssignableVars(root, assignable);
    VERIFY(atoms.size() == 1 && atoms.count(atom));
    VERIFY(variables.size() == 1 && variables.count(x));
    VERIFY(assignable.size() == 1 && assignable.count(x));
    VERIFY(parser->toNNF(root) == atom);
    VERIFY(parser->toDNF(root) == atom);

    auto a = parser->mkVarBool("a"), b = parser->mkVarBool("b");
    root = a;
    for(int i = 0; i < 20000; ++i) root = raw(parser, NODE_KIND::NT_NOT, {root});
    std::unordered_map<Node, Node> replacements{{a, b}};
    auto replaced = parser->replaceNodes(root, replacements);
    variables.clear();
    parser->collectVars(replaced, variables);
    VERIFY(variables.size() == 1 && variables.count(b));

    std::vector<Node> clauses;
    auto representative = parser->toTseitinCNF(root, clauses);
    VERIFY(representative && representative->isLiteral());
    VERIFY(clauses.size() > 20000);

    // The operand count can be deep independently of expression depth.
    auto wide_xor = raw(parser, NODE_KIND::NT_XOR, std::vector<Node>(12000, a));
    VERIFY(parser->toDNF(wide_xor)->isFalse());
    auto odd_xor = raw(parser, NODE_KIND::NT_XOR, std::vector<Node>(12001, a));
    VERIFY(parser->toDNF(odd_xor) == a);
    std::vector<Node> complements(12000, a);
    complements.push_back(parser->mkNot(a));
    complements.push_back(a);
    VERIFY(parser->toDNF(raw(parser, NODE_KIND::NT_XOR, complements))->isTrue());
    complements.push_back(parser->mkTrue());
    VERIFY(parser->toDNF(raw(parser, NODE_KIND::NT_XOR, complements))->isFalse());

    // A changed shared child must be propagated through every parent, even
    // when its cached result is used after the first occurrence.
    auto shared = raw(parser, NODE_KIND::NT_OR, {a, b});
    auto combined = raw(parser, NODE_KIND::NT_AND, {
        raw(parser, NODE_KIND::NT_NOT, {shared}), shared});
    auto c = parser->mkVarBool("c");
    replacements = {{b, c}};
    replaced = parser->replaceNodes(combined, replacements);
    variables.clear();
    parser->collectVars(replaced, variables);
    VERIFY(!variables.count(b));

    // A removed descendant changes all its ancestors, not only its immediate
    // parent. Keep construction raw so simplification cannot hide the depth.
    root = raw(parser, NODE_KIND::NT_AND, {a, b});
    for(int i = 0; i < 12000; ++i) root = raw(parser, NODE_KIND::NT_AND, {a, root});
    auto removed = parser->remove(root, {b});
    variables.clear();
    parser->collectVars(removed, variables);
    VERIFY(variables.size() == 1 && variables.count(a));

    auto comparison = parser->mkGe(x, parser->mkConstInt(0));
    root = comparison;
    for(int i = 0; i < 12000; ++i) root = raw(parser, NODE_KIND::NT_NOT, {root});
    const auto split = parser->splitOp(root, {NODE_KIND::NT_GE});
    VERIFY(!parser->hasSomeKinds(split, {NODE_KIND::NT_GE}));
    VERIFY(parser->getSplitLemmas().size() == 1);
    root = raw(parser, NODE_KIND::NT_EQ_BOOL, {a, b, c});
    for(int i = 0; i < 12000; ++i) root = raw(parser, NODE_KIND::NT_NOT, {root});
    auto binary = parser->binarizeOp(root);
    std::vector<Node> pending{binary};
    std::unordered_set<Node> seen;
    while(!pending.empty()) {
        auto node = pending.back(); pending.pop_back();
        if(!seen.insert(node).second) continue;
        if(node->isEq()) VERIFY(node->getChildrenSize() <= 2);
        for(const auto& child : node->getChildren()) pending.push_back(child);
    }
}

static void checkTruthTables() {
    auto parser = newParser();
    auto a = parser->mkVarBool("a"), b = parser->mkVarBool("b"), c = parser->mkVarBool("c");
    const std::vector<Node> formulas{
        raw(parser, NODE_KIND::NT_IMPLIES, {a, b, c}),
        raw(parser, NODE_KIND::NT_ITE, {a, b, c}),
        raw(parser, NODE_KIND::NT_XOR, {a, b, c}),
        raw(parser, NODE_KIND::NT_EQ_BOOL, {a, b, c}),
        raw(parser, NODE_KIND::NT_DISTINCT_BOOL, {a, b, c}),
        raw(parser, NODE_KIND::NT_AND, {
            raw(parser, NODE_KIND::NT_OR, {a, b}),
            raw(parser, NODE_KIND::NT_OR, {parser->mkNot(a), c})})};
    for(size_t f = 0; f < formulas.size(); ++f) {
        auto nnf = parser->toNNF(formulas[f]);
        auto negative = parser->toNNF(raw(parser, NODE_KIND::NT_NOT, {formulas[f]}));
        auto dnf = parser->toDNF(formulas[f]);
        for(unsigned bits = 0; bits < 8; ++bits) {
            const bool av = bits & 1, bv = bits & 2, cv = bits & 4;
            const bool expected[] = {!av || !bv || cv, av ? bv : cv,
                bool(av ^ bv ^ cv), av == bv && bv == cv, false, (av || bv) && (!av || cv)};
            auto model = newModel();
            model->add(a, av ? parser->mkTrue() : parser->mkFalse());
            model->add(b, bv ? parser->mkTrue() : parser->mkFalse());
            model->add(c, cv ? parser->mkTrue() : parser->mkFalse());
            for(const auto& output : {nnf, dnf}) {
                const auto value = parser->evaluate(output, model);
                VERIFY(value->isCBool() && value->isTrue() == expected[f]);
            }
            const auto value = parser->evaluate(negative, model);
            VERIFY(value->isCBool() && value->isTrue() != expected[f]);
        }
    }
}

int main() {
    checkDeepWalks();
    checkTruthTables();
    return 0;
}
