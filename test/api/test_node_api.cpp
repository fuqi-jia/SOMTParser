/**
 * Phase 1: Node API and NodeRange unit test.
 * Exercises kind(), sort(), numChildren(), child(), children() and range-for.
 */
#include "somtparser/ir/node.h"
#include "somtparser/frontend/parser.h"
#include <iostream>
#include "test_helpers.h"

using namespace SOMTParser;

int main() {
    std::cout << "======= Node API (Phase 1) Test =======" << std::endl;

    ParserPtr parser = newParser();

    // Leaf: constant
    Node leaf = parser->mkExpr("42");
    VERIFY(leaf);
    VERIFY(kind(leaf) == NODE_KIND::NT_CONST);
    VERIFY(sort(leaf));
    VERIFY(numChildren(leaf) == 0);
    VERIFY(child(leaf, 0) == nullptr);
    size_t count = 0;
    std::cout << "Leaf (42): " << parser->toString(leaf) << std::endl;
    for (Node c : children(leaf)) {
        std::cout << "Child: " << parser->toString(c) << std::endl;
        ++count;
    }
    VERIFY(count == 0);
    std::cout << "Leaf (42): kind=NT_CONST, numChildren=0, range size=0 OK" << std::endl;

    // (+ 1 2): parser may fold to constant 3 or keep ADD node; both are valid for testing Node API
    Node add = parser->mkExpr("(+ 1 2)");
    VERIFY(add);
    std::cout << "(+ 1 2) -> " << parser->toString(add)
              << ", kind=" << (kind(add) == NODE_KIND::NT_CONST ? "NT_CONST" : "NT_ADD")
              << ", numChildren=" << numChildren(add) << std::endl;

    if (kind(add) == NODE_KIND::NT_CONST) {
        // Folded to constant 3 at parse time
        VERIFY(numChildren(add) == 0);
        count = 0;
        for (Node c : children(add)) { (void)c; ++count; }
        VERIFY(count == 0);
        std::cout << "  (folded to constant: 0 children) OK" << std::endl;
    } else {
        // Not folded; still ADD node with two children 1 and 2
        VERIFY(kind(add) == NODE_KIND::NT_ADD);
        VERIFY(numChildren(add) == 2);
        Node a = child(add, 0), b = child(add, 1);
        VERIFY(a && b);
        count = 0;
        for (Node c : children(add)) {
            std::cout << "  child: " << parser->toString(c) << std::endl;
            VERIFY(c);
            ++count;
        }
        VERIFY(count == 2);
        std::cout << "  (ADD with 2 children) OK" << std::endl;
    }

    // (+ x 2): with variable, no folding; must be ADD with 2 children
    parser->mkVarInt("x");
    Node addX = parser->mkExpr("(+ x 2)");
    VERIFY(addX);
    VERIFY(kind(addX) == NODE_KIND::NT_ADD);
    VERIFY(numChildren(addX) == 2);
    count = 0;
    std::cout << "(+ x 2): " << parser->toString(addX) << std::endl;
    for (Node c : children(addX)) {
        std::cout << "  child: " << parser->toString(c) << std::endl;
        VERIFY(c);
        ++count;
    }
    VERIFY(count == 2);
    std::cout << "(+ x 2): kind=NT_ADD, numChildren=2, range-for count=2 OK" << std::endl;

    // Null safety
    Node empty;
    VERIFY(kind(empty) == NODE_KIND::NT_UNKNOWN);
    VERIFY(sort(empty) == nullptr);
    VERIFY(numChildren(empty) == 0);
    VERIFY(child(empty, 0) == nullptr);

    std::cout << "Empty node: " << parser->toString(empty) << std::endl;
    for (Node c : children(empty)) {
        VERIFY(false && "should not iterate");
    }
    std::cout << "Null node: safe defaults OK" << std::endl;

    // Reallocation and rehashing must preserve canonical handles and indices.
    Node retained;
    {
        NodeManager manager;
        const auto integer = SortManager::getInt();
        const auto boolean = SortManager::getBool();
        Node first = manager.createNode(integer, NODE_KIND::NT_VAR, "first");
        Node one = manager.createNode(integer, 1);
        retained = manager.createNode(integer, NODE_KIND::NT_ADD, "+", {first, one});
        const auto firstIndex = manager.getIndex(first);
        const auto sumIndex = manager.getIndex(retained);
        for (size_t i = 0; i < 20000; ++i) {
            Node variable = manager.createNode(integer, NODE_KIND::NT_VAR,
                                               "growth_" + std::to_string(i));
            VERIFY(manager.getNode(manager.getIndex(variable)) == variable);
            if (i % 257 == 0) {
                VERIFY(manager.createNode(integer, NODE_KIND::NT_VAR, "first") == first);
                VERIFY(manager.createNode(integer, NODE_KIND::NT_ADD, "+", {first, one}) == retained);
                VERIFY(manager.getIndex(first) == firstIndex);
                VERIFY(manager.getIndex(retained) == sumIndex);
            }
        }
        // Equal names in different sorts remain distinct after table growth.
        Node predicate = manager.createNode(boolean, NODE_KIND::NT_VAR, "first");
        VERIFY(predicate != first);
        VERIFY(manager.createNode(boolean, NODE_KIND::NT_VAR, "first") == predicate);
        manager.clear();
        VERIFY(retained->getChild(0) == first);
        VERIFY(retained->getChild(1) == one);
    }
    VERIFY(retained->getChildrenSize() == 2);
    VERIFY(retained->getChild(0)->getName() == "first");
    retained.reset();
    std::cout << "All Node API tests passed." << std::endl;
    return 0;
}
