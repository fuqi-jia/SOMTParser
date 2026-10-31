#include <algorithm>
#include <cstdlib>
#include <memory>
#include <new>
#include <vector>

#include "somtparser/ir/dag.h"
#include "test_helpers.h"

using namespace SOMTParser;

namespace {
bool countAllocations = false;
std::size_t largestAllocation = 0;

void* allocate(std::size_t bytes) {
    if (countAllocations) largestAllocation = std::max(largestAllocation, bytes);
    if (void* pointer = std::malloc(bytes == 0 ? 1 : bytes)) return pointer;
    throw std::bad_alloc();
}

NodePtr variable(NodeManager& manager, const char* name) {
    return manager.createNode(SortManager::BOOL_SORT, NODE_KIND::NT_VAR, name);
}

void testWideSharedSubtree() {
    NodeManager manager;
    auto leaf = variable(manager, "retained");
    constexpr std::size_t fanout = 32768;
    auto root = manager.createNode(SortManager::BOOL_SORT, NODE_KIND::NT_AND,
        "and", std::vector<NodePtr>(fanout, leaf));
    std::weak_ptr<DAGNode> retained = leaf;
    leaf.reset();
    auto discarded = variable(manager, "discarded");
    std::weak_ptr<DAGNode> reclaimed = discarded;
    discarded.reset();

    // Count only teardown allocations. The live graph has two distinct nodes
    // but many repeated edges; freeing the manager must not copy that wide
    // child vector or put every repeated edge on the traversal work-list.
    largestAllocation = 0;
    countAllocations = true;
    manager.clear();
    countAllocations = false;
    VERIFY(largestAllocation < fanout * sizeof(DAGNode*));
    VERIFY(reclaimed.expired());
    VERIFY(!retained.expired());
    VERIFY(root->isAnd());
    VERIFY(root->getChildrenSize() == fanout);
    VERIFY(root->getChild(0) == root->getChild(fanout - 1));
    VERIFY(root->getChild(0)->getName() == "retained");
}

void testUnretainedDeepChain() {
    NodeManager manager;
    auto node = variable(manager, "deep");
    std::weak_ptr<DAGNode> leaf = node;
    for (int depth = 0; depth < 32000; ++depth) {
        node = manager.createNode(SortManager::BOOL_SORT, NODE_KIND::NT_NOT,
            "not", std::vector<NodePtr>{node});
    }
    std::weak_ptr<DAGNode> root = node;
    node.reset();
    manager.clear();
    VERIFY(leaf.expired());
    VERIFY(root.expired());
}

void testCycles(bool retainRoot) {
    NodeManager manager;
    auto first = variable(manager, "first");
    auto second = variable(manager, "second");
    // Recursive definitions update nodes in place; exercise that ownership
    // shape without relying on the recursive-definition parser's syntax.
    *first = DAGNode(SortManager::BOOL_SORT, NODE_KIND::NT_NOT,
        "not", std::vector<NodePtr>{second});
    *second = DAGNode(SortManager::BOOL_SORT, NODE_KIND::NT_NOT,
        "not", std::vector<NodePtr>{first});
    std::weak_ptr<DAGNode> firstWeak = first;
    std::weak_ptr<DAGNode> secondWeak = second;
    second.reset();
    if (!retainRoot) first.reset();
    manager.clear();
    if (retainRoot) {
        VERIFY(first->isNot());
        VERIFY(first->getChild(0)->isNot());
        VERIFY(first->getChild(0)->getChild(0) == first);
        first->clear(); // the external owner releases its retained cycle
        first.reset();
    }
    VERIFY(firstWeak.expired());
    VERIFY(secondWeak.expired());
}

void testUnmanagedIntermediate() {
    NodeManager manager;
    auto leaf = variable(manager, "through_external_node");
    auto intermediate = std::make_shared<DAGNode>(SortManager::BOOL_SORT,
        NODE_KIND::NT_NOT, "not", std::vector<NodePtr>{leaf});
    auto root = manager.createNode(SortManager::BOOL_SORT, NODE_KIND::NT_NOT,
        "not", std::vector<NodePtr>{intermediate});
    leaf.reset();
    intermediate.reset();
    manager.clear();
    VERIFY(root->getChild(0)->isNot());
    VERIFY(root->getChild(0)->getChild(0)->getName() == "through_external_node");
}
} // namespace

void* operator new(std::size_t bytes) { return allocate(bytes); }
void* operator new[](std::size_t bytes) { return allocate(bytes); }
void operator delete(void* pointer) noexcept { std::free(pointer); }
void operator delete[](void* pointer) noexcept { std::free(pointer); }
void operator delete(void* pointer, std::size_t) noexcept { std::free(pointer); }
void operator delete[](void* pointer, std::size_t) noexcept { std::free(pointer); }

int main() {
    testWideSharedSubtree();
    testUnretainedDeepChain();
    testCycles(false);
    testCycles(true);
    testUnmanagedIntermediate();
}
